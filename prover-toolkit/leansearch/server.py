#!/usr/bin/env python3
"""A LeanSearch-API-compatible server over this project's own index.

Speaks the same contract as leansearch.net, so ax-prover's existing
`search_lean_search` tool works against it with only a `server_url` change:

    POST /search   {"query": ["..."], "num_results": 6}
    ->  [[ {"result": {"name", "kind", "signature", "docstring"}}, ... ]]

Stdlib only -- no FastAPI, no uvicorn, nothing to install.

Retrieval is BM25 over name + signature + docstring, with two adjustments that
matter for this corpus:

  * **Symbols are tokens.**  A query containing `⊟` or `➝` must be able to find
    the notation declaration that defines it.  Ordinary word tokenisation drops
    those characters entirely, which would make the index useless for exactly
    the lookups it exists to serve.
  * **Name hits are boosted**, and `notation`/`inductive`/`structure` entries
    are boosted further, because when a model is confused about what `⋏` *is*,
    the definition is a better answer than the 40 lemmas that mention it.

    python3 server.py --port 8080
"""

from __future__ import annotations

import argparse
import json
import math
import re
import sys
import unicodedata
from collections import defaultdict
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

WORD_RE = re.compile(r"[A-Za-z][A-Za-z0-9_']*|\d+")

# Natural-language filler. A query like "what does the connective ⋏ mean" is
# mostly noise; without this the filler words outweigh the one token (`⋏`) that
# actually discriminates, and the notation declaration loses to an unrelated def.
STOPWORDS = frozenset("""
a an the of for and or to in on is are be it its this that these those with
what which how why when where does do did i we you they there here as by from
mean means meaning definition define defined lemma theorem proof prove proves
about into over under can could should would need want find search show
""".split())

# Kinds that answer "what IS this thing?" rather than "what is true about it?"
KIND_BOOST = {
    "notation": 2.2, "inductive": 1.9, "structure": 1.8, "class": 1.6,
    "def": 1.25, "abbrev": 1.2, "instance": 1.0,
    "theorem": 1.0, "lemma": 1.0, "axiom": 1.1, "opaque": 1.0,
}


def _is_symbol(tok: str) -> bool:
    return len(tok) == 1 and ord(tok) > 127


def tokenize(text: str) -> list[str]:
    """Words, camelCase/dotted pieces, and every non-ASCII symbol as its own token."""
    toks: list[str] = []
    for w in WORD_RE.findall(text):
        lw = w.lower()
        toks.append(lw)
        # split camelCase and snake_case into parts as well
        for part in re.findall(r"[A-Z]?[a-z]+|[A-Z]+(?![a-z])|\d+", w):
            p = part.lower()
            if p != lw:
                toks.append(p)
    for ch in text:
        if ord(ch) > 127 and not unicodedata.category(ch).startswith("L"):
            toks.append(ch)
        elif ord(ch) > 0x2000:          # arrows, logical operators, etc.
            toks.append(ch)
    return toks


class Index:
    def __init__(self, entries: list[dict]) -> None:
        self.entries = entries
        self.docs: list[list[str]] = []
        self.name_toks: list[set[str]] = []
        df: dict[str, int] = defaultdict(int)
        for e in entries:
            blob = f"{e['name']} {e['signature']} {e.get('docstring','')} {e['module']}"
            toks = tokenize(blob)
            self.docs.append(toks)
            self.name_toks.append(set(tokenize(e["name"] + " " + e.get("short", ""))))
            for t in set(toks):
                df[t] += 1
        n = len(entries)
        self.idf = {t: math.log(1 + (n - c + 0.5) / (c + 0.5)) for t, c in df.items()}
        self.tf: list[dict[str, int]] = []
        for toks in self.docs:
            d: dict[str, int] = defaultdict(int)
            for t in toks:
                d[t] += 1
            self.tf.append(d)
        self.avglen = sum(len(d) for d in self.docs) / max(n, 1)

    def search(self, query: str, k: int) -> list[dict]:
        q = [t for t in tokenize(query)
             if t not in STOPWORDS and (len(t) > 1 or _is_symbol(t))]
        if not q:
            q = tokenize(query)
        if not q:
            return []
        qset = set(q)
        scores: list[tuple[float, int]] = []
        k1, b = 1.5, 0.75
        for i, tf in enumerate(self.tf):
            dl = len(self.docs[i]) or 1
            s = 0.0
            for t in qset:
                f = tf.get(t, 0)
                if not f:
                    continue
                idf = self.idf.get(t, 0.0)
                w = 3.0 if _is_symbol(t) else 1.0   # symbols are the discriminative tokens
                s += w * idf * (f * (k1 + 1)) / (f + k1 * (1 - b + b * dl / self.avglen))
            if s <= 0:
                continue
            overlap = len(qset & self.name_toks[i])
            s *= 1.0 + 0.65 * overlap                      # name hits matter
            s *= KIND_BOOST.get(self.entries[i]["kind"], 1.0)
            scores.append((s, i))
        scores.sort(key=lambda x: (-x[0], x[1]))
        out = []
        for s, i in scores[:k]:
            e = self.entries[i]
            out.append({
                "result": {
                    "name": e["name"],
                    "kind": e["kind"],
                    "signature": e["signature"],
                    "docstring": (
                        (e.get("docstring") or "")
                        + f"\n[{e['repo']}: {e['file']}:{e['line']}]"
                    ).strip(),
                },
                "score": round(s, 4),
            })
        return out


def make_handler(index: Index):
    class H(BaseHTTPRequestHandler):
        def log_message(self, *a):  # quieter
            pass

        def _send(self, obj, code=200):
            body = json.dumps(obj).encode()
            self.send_response(code)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def do_GET(self):
            if self.path.rstrip("/") in ("", "/health"):
                self._send({"status": "ok", "entries": len(index.entries)})
            else:
                self._send({"error": "not found"}, 404)

        def do_POST(self):
            if self.path.rstrip("/") != "/search":
                return self._send({"error": "not found"}, 404)
            n = int(self.headers.get("Content-Length", 0))
            try:
                payload = json.loads(self.rfile.read(n) or b"{}")
            except json.JSONDecodeError:
                return self._send({"error": "bad json"}, 400)
            queries = payload.get("query", [])
            if isinstance(queries, str):
                queries = [queries]
            k = int(payload.get("num_results", 6))
            self._send([index.search(q, k) for q in queries])

    return H


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--index", type=Path, default=Path(__file__).parent / "index.jsonl")
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=None,
                    help="default: the port in toolkit.json, so the server and "
                         "the clients cannot disagree")
    a = ap.parse_args()

    port = a.port
    if port is None:
        sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
        from toolkit_config import find_config
        port = find_config().index_port
    a.port = port
    entries = [json.loads(l) for l in a.index.read_text().splitlines() if l.strip()]
    idx = Index(entries)
    print(f"indexed {len(entries)} declarations; serving on http://{a.host}:{a.port}")
    ThreadingHTTPServer((a.host, a.port), make_handler(idx)).serve_forever()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
