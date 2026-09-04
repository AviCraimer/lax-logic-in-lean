#!/usr/bin/env python3
"""Sample proofs from a prover model and verify them, recording real numbers.

Writes one JSON object per attempt to a JSONL file: the item, the sample index,
token counts, wall-clock, the verdict, and the pinned axioms on success.  That
file is the input to `theorem_cost_model.py`; nothing in the cost model is a
placeholder.

The endpoint is any OpenAI-compatible server — `llama-server`, Ollama, or a
hosted API — so the same harness measures local and cloud models identically.

    llama-server -hf mradermacher/Goedel-Prover-V2-8B-GGUF:Q5_K_M --port 8088

    python3 harness.py --items benchmarks/items.jsonl --out runs/goedel8b.jsonl \\
        --model mradermacher/Goedel-Prover-V2-8B-GGUF:Q5_K_M -k 4 --limit 20
"""

from __future__ import annotations

import argparse
import concurrent.futures as cf
import json
import os
import queue
import random
import re
import threading
import time
import urllib.error
import urllib.request
from dataclasses import asdict
from pathlib import Path

from verify import verify
import openai_batch

RETRIEVAL_HEADER = (
    "The following declarations are from THIS project's own sources. The\n"
    "connectives below are OBJECT-LEVEL constructors of an inductive datatype,\n"
    "not Lean's own logical connectives, and the goal is membership in an\n"
    "inductively defined relation. Use these definitions rather than guessing.\n"
)


def retrieve(url: str, query: str, k: int) -> str:
    """Fetch local-corpus declarations to prepend to the prompt.

    Goedel-Prover-V2 has no tool-use post-training, so it cannot call
    LeanSearch itself; the retrieval is done here and injected. Failure is
    non-fatal -- a retrieval outage must not silently become a model result.
    """
    try:
        req = urllib.request.Request(
            url.rstrip("/") + "/search",
            data=json.dumps({"query": [query], "num_results": k}).encode(),
            headers={"Content-Type": "application/json"},
        )
        with urllib.request.urlopen(req, timeout=20) as r:
            data = json.loads(r.read())
    except (urllib.error.URLError, TimeoutError, OSError, json.JSONDecodeError):
        return ""
    if not data or not data[0]:
        return ""
    lines = [RETRIEVAL_HEADER]
    for item in data[0]:
        res = item.get("result", {})
        lines.append(f"-- {res.get('name','?')}  [{res.get('kind','')}]")
        lines.append(res.get("signature", ""))
        doc = (res.get("docstring") or "").strip()
        if doc:
            lines.append("-- " + doc.splitlines()[0][:200])
        lines.append("")
    return "\n".join(lines)

# The template from the Goedel-Prover-V2 model card.
PROMPT_TEMPLATE = (
    "Complete the following Lean 4 code:\n\n"
    "```lean4\n{code}\n```\n\n"
    "Before producing the Lean 4 code to formally prove the given theorem, "
    "provide a detailed proof plan outlining the main proof steps and strategies."
)


def build_prompt(item: dict, context_lines: int, retrieved: str = "") -> str:
    """The file up to the target, with the proof left as `sorry`.

    The prefix is truncated to the last `context_lines` lines: the whole file
    can exceed the model's context, and the tail is where the relevant
    definitions live.
    """
    prefix = item["prefix"]
    if context_lines > 0:
        lines = prefix.splitlines()
        if len(lines) > context_lines:
            prefix = "-- (file truncated above)\n" + "\n".join(lines[-context_lines:]) + "\n"
    code = f"{prefix}{item['statement']} := by\n  sorry"
    if retrieved:
        code = f"/- Relevant declarations from this project:\n{retrieved}-/\n\n{code}"
    return PROMPT_TEMPLATE.format(code=code)


def call_model(url: str, model: str, prompt: str, max_tokens: int,
               temperature: float, timeout: int,
               api_key: str = "") -> tuple[str, dict]:
    payload = {
        "model": model,
        "messages": [{"role": "user", "content": prompt}],
        "max_tokens": max_tokens,
        "temperature": temperature,
    }
    headers = {"Content-Type": "application/json"}
    if api_key:
        headers["Authorization"] = f"Bearer {api_key}"

    def _post(body: dict) -> dict:
        req = urllib.request.Request(
            url.rstrip("/") + "/v1/chat/completions",
            data=json.dumps(body).encode(),
            headers=headers,
        )
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read())

    # Reasoning models reject `max_tokens` (want `max_completion_tokens`) and
    # refuse a non-default `temperature`.  They report ONE offending parameter
    # per 400, so a single retry is not enough: adapt in a loop until the
    # request is accepted or nothing further can be adjusted.
    body = dict(payload)
    last: Exception | None = None
    for _ in range(4):
        try:
            data = _post(body)
            break
        except urllib.error.HTTPError as e:
            if e.code != 400:
                raise
            detail = e.read().decode(errors="replace") if e.fp else ""
            adjusted = dict(body)
            if "max_tokens" in detail and "max_tokens" in adjusted:
                adjusted["max_completion_tokens"] = adjusted.pop("max_tokens")
            elif "temperature" in detail:
                adjusted.pop("temperature", None)
            elif "top_p" in detail:
                adjusted.pop("top_p", None)
            if adjusted == body:
                raise
            body, last = adjusted, e
    else:
        raise last if last else RuntimeError("could not adapt request")
    text = data["choices"][0]["message"]["content"]
    usage = data.get("usage", {}) or {}
    return text, usage


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--items", type=Path, default=Path("benchmarks/items.jsonl"))
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--url", default="http://127.0.0.1:8088")
    ap.add_argument("--model", required=True)
    ap.add_argument("-k", "--samples", type=int, default=4,
                    help="attempts per lemma (pass@k denominator)")
    ap.add_argument("--limit", type=int, default=0, help="cap number of lemmas")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--max-tokens", type=int, default=2048)
    ap.add_argument("--temperature", type=float, default=0.9)
    ap.add_argument("--context-lines", type=int, default=0,
                    help="truncate the prompt prefix to the last N lines; "
                         "0 = send the whole file (default). Truncation was "
                         "measurably suppressing results: gpt-5 failed "
                         "hasPar_bigOr 0/3 truncated, then proved it first try "
                         "with the full file via ax-prover.")
    ap.add_argument("--gen-timeout", type=int, default=900)
    ap.add_argument("--verify-workers", type=int, default=6)
    ap.add_argument("--groups", default="", help="comma-separated group filter")
    ap.add_argument("--leansearch-url", default="",
                    help="local LeanSearch server; enables retrieval-augmented prompts")
    ap.add_argument("--leansearch-k", type=int, default=6)
    ap.add_argument("--now", action="store_true",
                    help="synchronous requests instead of the Batch API. "
                         "Batch is HALF PRICE but can take up to 24h; use "
                         "--now only when the answer is needed immediately.")
    ap.add_argument("--batch-resume", default="",
                    help="collect a previously submitted batch by id")
    ap.add_argument("--batch-wait", type=int, default=0,
                    help="seconds to poll before detaching (0 = wait forever)")
    ap.add_argument("--api-key-file", type=Path, default=None,
                    help="file containing ONLY the API key. Read by this "
                         "process at startup, stripped of whitespace, never "
                         "logged and never written to run files. Preferred "
                         "over --api-key-env when the key cannot be exported "
                         "into the calling shell.")
    ap.add_argument("--api-key-env", default="",
                    help="env var holding the API key for a hosted endpoint. "
                         "The key is read from the environment and never logged; "
                         "run files record only the model name.")
    args = ap.parse_args()

    api_key = ""
    if args.api_key_file:
        try:
            api_key = args.api_key_file.read_text().strip()
        except OSError as e:
            print(f"error: cannot read --api-key-file: {e.__class__.__name__}")
            return 2
        if not api_key:
            print(f"error: {args.api_key_file} is empty")
            return 2
        print(f"api key: loaded from {args.api_key_file} "
              f"({len(api_key)} chars, value not shown)")
    elif args.api_key_env:
        api_key = os.environ.get(args.api_key_env, "")
        if not api_key:
            print(f"error: ${args.api_key_env} is not set in the environment")
            return 2

    # An API key with a localhost endpoint is always a mistake: the key is for a
    # hosted provider, so the URL was left at its default. Fail before burning a
    # whole sweep on connection errors.
    if api_key and ("127.0.0.1" in args.url or "localhost" in args.url):
        print(f"error: --api-key-file/--api-key-env given but --url is {args.url}\n"
              f"       pass the provider URL, e.g. --url https://api.openai.com")
        return 2

    items = [json.loads(l) for l in args.items.read_text().splitlines() if l.strip()]
    if args.groups:
        keep = {g.strip() for g in args.groups.split(",")}
        items = [i for i in items if i["group"] in keep]
    if args.limit:
        rng = random.Random(args.seed)
        # Stratify by group so the pilot is not dominated by the largest file.
        by_group: dict[str, list[dict]] = {}
        for it in items:
            by_group.setdefault(it["group"], []).append(it)
        for g in by_group.values():
            rng.shuffle(g)
        picked, gi = [], list(by_group.values())
        while len(picked) < args.limit and any(gi):
            for g in gi:
                if g and len(picked) < args.limit:
                    picked.append(g.pop())
        items = picked

    args.out.parent.mkdir(parents=True, exist_ok=True)
    print(f"{len(items)} lemmas x {args.samples} samples = "
          f"{len(items) * args.samples} attempts -> {args.out}")

    items_by_id = {i['id']: i for i in items}
    n_retrieval_failures = [0]
    write_lock = threading.Lock()
    fh = args.out.open("a")
    verify_pool = cf.ThreadPoolExecutor(max_workers=args.verify_workers)
    pending: list[cf.Future] = []
    counts = {"ok": 0, "fail": 0}

    def record(rec: dict) -> None:
        with write_lock:
            fh.write(json.dumps(rec) + "\n")
            fh.flush()

    def verify_and_record(item, k, text, usage, gen_s):
        res = verify(item, text, Path(item["repo"]))
        rec = {
            "id": item["id"], "name": item["name"], "group": item["group"],
            "file": item["file"], "proof_lines": item["proof_lines"],
            "sample": k, "model": args.model,
            "temperature": args.temperature,
            "prompt_tokens": usage.get("prompt_tokens"),
            "completion_tokens": usage.get("completion_tokens"),
            "retrieval": bool(args.leansearch_url),
            "gen_seconds": round(gen_s, 2),
            "verify_seconds": round(res.elapsed_s, 2),
            "ok": res.ok, "reason": res.reason, "axioms": res.axioms,
            "response": text,
            "candidate": res.candidate if not res.ok else "",
            "lean_error": (res.lean_stdout + res.lean_stderr)[:2000] if not res.ok else "",
        }
        record(rec)
        counts["ok" if res.ok else "fail"] += 1
        status = "OK  " if res.ok else "fail"
        print(f"  [{counts['ok']+counts['fail']:4d}] {status} {item['id']}#{k} "
              f"({res.reason}, gen {gen_s:.0f}s, {usage.get('completion_tokens')} tok)")
        return res.ok

    # ---------------- Batch path (default) ----------------
    if not args.now:
        if not api_key:
            print("error: batch mode needs --api-key-file or --api-key-env")
            return 2
        index: dict[str, tuple[dict, int]] = {}
        if args.batch_resume:
            bid = args.batch_resume
            state = args.out.with_suffix(".batchstate.json")
            if not state.exists():
                print(f"error: no {state}; cannot map results back to lemmas")
                return 2
            saved = json.loads(state.read_text())
            for cid, v in saved["index"].items():
                index[cid] = (items_by_id[v["id"]], v["sample"])
        else:
            reqs = []
            for item in items:
                for k in range(args.samples):
                    retrieved = ""
                    if args.leansearch_url:
                        q = re.sub(r"/--.*?-/", " ", item["statement"], flags=re.S)
                        retrieved = retrieve(args.leansearch_url, q, args.leansearch_k)
                        if not retrieved:
                            n_retrieval_failures[0] += 1
                    cid = f"{len(reqs):04d}"
                    index[cid] = (item, k)
                    reqs.append({
                        "custom_id": cid,
                        "method": "POST",
                        "url": "/v1/chat/completions",
                        "body": {
                            "model": args.model,
                            "messages": [{"role": "user",
                                          "content": build_prompt(item, args.context_lines, retrieved)}],
                            "max_completion_tokens": args.max_tokens,
                        },
                    })
            print(f"submitting {len(reqs)} requests to the Batch API "
                  f"(half price; up to 24h)")
            fid = openai_batch.upload_jsonl(reqs, api_key)
            batch = openai_batch.create(fid, api_key)
            bid = batch["id"]
            args.out.with_suffix(".batchstate.json").write_text(json.dumps({
                "batch_id": bid,
                "index": {c: {"id": it["id"], "sample": k} for c, (it, k) in index.items()},
            }))
            print(f"  batch id: {bid}")
            print(f"  resume later with:  --batch-resume {bid}")

        b = openai_batch.wait(bid, api_key, limit=(args.batch_wait or None))
        if b.get("status") != "completed":
            print(f"batch not complete (status={b.get('status')}); nothing verified yet")
            return 0
        out_id = b.get("output_file_id")
        if not out_id:
            print("batch completed but produced no output file")
            return 1
        results = openai_batch.fetch_output(out_id, api_key)
        print(f"collected {len(results)} responses; verifying ...")
        for row in results:
            cid = row.get("custom_id")
            if cid not in index:
                continue
            item, k = index[cid]
            body = ((row.get("response") or {}).get("body") or {})
            choices = body.get("choices") or []
            if not choices:
                record({"id": item["id"], "sample": k, "ok": False,
                        "reason": "batch_no_choices", "model": args.model,
                        "group": item["group"]})
                counts["fail"] += 1
                continue
            text = choices[0]["message"]["content"]
            pending.append(verify_pool.submit(
                verify_and_record, item, k, text, body.get("usage", {}) or {}, 0.0))
        for f in pending:
            f.result()
        verify_pool.shutdown()
        fh.close()
        total = counts["ok"] + counts["fail"]
        print(f"\n{counts['ok']}/{total} attempts verified "
              f"({100.0 * counts['ok'] / max(total,1):.1f}%)  [batch, half price]")
        print(f"results: {args.out}")
        return 0

    t_start = time.monotonic()
    # Generation is serialized (one llama-server slot); verification overlaps it.
    for item in items:
        for k in range(args.samples):
            retrieved = ""
            if args.leansearch_url:
                q = re.sub(r"/--.*?-/", " ", item["statement"], flags=re.S)
                retrieved = retrieve(args.leansearch_url, q, args.leansearch_k)
                if not retrieved:
                    n_retrieval_failures[0] += 1
            prompt = build_prompt(item, args.context_lines, retrieved)
            t0 = time.monotonic()
            try:
                text, usage = call_model(
                    args.url, args.model, prompt, args.max_tokens,
                    args.temperature, args.gen_timeout, api_key,
                )
            except (urllib.error.URLError, TimeoutError, OSError) as e:
                record({"id": item["id"], "sample": k, "ok": False,
                        "reason": f"generation_error:{type(e).__name__}",
                        "model": args.model, "group": item["group"]})
                counts["fail"] += 1
                print(f"  generation error on {item['id']}#{k}: {e}")
                continue
            gen_s = time.monotonic() - t0
            pending.append(
                verify_pool.submit(verify_and_record, item, k, text, usage, gen_s)
            )

    for f in pending:
        f.result()
    verify_pool.shutdown()
    fh.close()

    total = counts["ok"] + counts["fail"]
    elapsed = time.monotonic() - t_start
    print(f"\n{counts['ok']}/{total} attempts verified "
          f"({100.0 * counts['ok'] / max(total, 1):.1f}%) in {elapsed/60:.1f} min")
    if args.leansearch_url:
        print(f"retrieval failures: {n_retrieval_failures[0]} "
              f"(these are harness faults, not model failures)")
    print(f"results: {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
