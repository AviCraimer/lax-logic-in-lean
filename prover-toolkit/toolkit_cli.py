#!/usr/bin/env python3
"""Toolkit primitives for a human or an agent acting as the proposer.

The API route (`harness.py`, `constructive_prove.py`) puts a hosted model in
the proposer seat and drives it with a fixed prompt. This is the other option:
YOU are the proposer -- a person, or a coding agent with its own tools -- and
the toolkit supplies only the parts that are tedious or easy to get wrong.

    search   query the corpus index (what ax-prover's LeanSearch tool does)
    goals    show the open goal at each `sorry`, as Lean reports it
    check    compile and report axioms: the verification that actually matters

Neither route is privileged. The API route is unattended and costs money per
attempt; this route costs nothing per attempt but needs someone in the loop,
and can bring judgement, repository grep, and a whole-file view that a fixed
prompt cannot.

    python3 toolkit_cli.py search "nucleus lax modality"
    python3 toolkit_cli.py goals  LaxLogic/PLLSemUIHenkin.lean
    python3 toolkit_cli.py check  LaxLogic/PLLSemUIHenkin.lean wit_pbisim
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import urllib.request
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from toolkit_config import find_config


def cmd_search(cfg, args) -> int:
    url = f"http://127.0.0.1:{cfg.index_port}/search"
    body = json.dumps({"query": [args.query], "num_results": args.n}).encode()
    try:
        req = urllib.request.Request(url, data=body,
                                     headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=30) as r:
            data = json.load(r)
    except OSError as e:
        print(f"index not reachable on port {cfg.index_port}: {e}\n"
              f"start it:  python3 leansearch/server.py   (uses toolkit.json)")
        return 2
    if not data or not data[0]:
        print("no results")
        return 0
    for item in data[0]:
        res = item.get("result", {})
        print(f"\n[{res.get('kind')}] {res.get('name')}")
        print(f"  {res.get('signature','')}")
        doc = (res.get("docstring") or "").strip()
        if doc:
            print(f"  {doc[:400]}")
    return 0


def _lean(cfg, path: Path, extra: str = "") -> str:
    src = path.read_text() + extra
    tmp = cfg.repo / f"_toolkit_{path.stem}.lean"
    tmp.write_text(src)
    try:
        p = subprocess.run(["lake", "env", "lean", str(tmp)], cwd=cfg.repo,
                           capture_output=True, text=True, timeout=900)
        return p.stdout + p.stderr
    finally:
        tmp.unlink(missing_ok=True)


def cmd_goals(cfg, args) -> int:
    """Show what Lean actually reports at each `sorry` -- the real proof state,
    not a guess from reading the source."""
    path = cfg.repo / args.file if not Path(args.file).is_absolute() else Path(args.file)
    src = path.read_text()
    # replace each `sorry` with a deliberate error so Lean prints the goal
    probed = re.sub(r"(?m)^(\s*)sorry\s*$", r"\1skip -- toolkit: goal probe", src)
    tmp = cfg.repo / f"_toolkit_goals_{path.stem}.lean"
    tmp.write_text(probed)
    try:
        p = subprocess.run(["lake", "env", "lean", str(tmp)], cwd=cfg.repo,
                           capture_output=True, text=True, timeout=900)
        out = p.stdout + p.stderr
    finally:
        tmp.unlink(missing_ok=True)
    blocks = re.split(r"(?=^\S+:\d+:\d+: error:)", out, flags=re.MULTILINE)
    shown = 0
    for b in blocks:
        if "unsolved goals" in b:
            print(b.rstrip()[:4000]); print("-" * 60); shown += 1
    if not shown:
        print("no open goals found (no `sorry`, or the file does not compile)")
        print(out[:1500])
    return 0


def qualified(src: str, name: str) -> str:
    """Fully qualify `name` using the namespaces open where it is declared.

    `#print axioms` is appended after the file, by which point every
    `namespace` has been closed, so a bare name is an unknown constant.
    """
    stack: list[str] = []
    for line in src.splitlines():
        m = re.match(r"^namespace\s+([A-Za-z_][\w'.]*)", line)
        if m:
            stack.append(m.group(1)); continue
        if re.match(r"^end\s+[A-Za-z_][\w'.]*", line) and stack:
            stack.pop(); continue
        if re.match(rf"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma|def)\s+{re.escape(name)}\b", line):
            return ".".join(stack + [name]) if stack else name
    return name


def cmd_check(cfg, args) -> int:
    """The verification that matters: compiles, no `sorry`, and which axioms."""
    path = cfg.repo / args.file if not Path(args.file).is_absolute() else Path(args.file)
    full = qualified(path.read_text(), args.name)
    out = _lean(cfg, path, f"\n#print axioms {full}\n")
    # Lean 4.31 emits both `error:` and `error(lean.someCode):` -- matching only
    # the first form let an "Unknown constant" slip through, and this command
    # then reported a file containing `sorry` as clean.
    errors = re.findall(r"^\S+:\d+:\d+: error(?:\([^)]*\))?:.*$", out, re.MULTILINE)
    m = re.search(r"depends on axioms:\s*\[(.*?)\]", out, re.DOTALL)
    axs = [a.strip() for a in m.group(1).split(",") if a.strip()] if m else []
    none = "does not depend on any axioms" in out

    # Absence of an axiom report is NOT absence of axioms. Fail loudly.
    if not m and not none and not errors:
        print(f"FAIL — no axiom report for `{full}`. The check did not run; "
              f"do not treat this as a pass.")
        return 1
    if re.search(r"declaration uses `sorry`", out):
        print("FAIL — the file still contains `sorry`")
        for w in re.findall(r"^\S+:(\d+):\d+: warning: declaration uses `sorry`",
                            out, re.MULTILINE)[:5]:
            print(f"  line {w}")
        return 1

    if errors:
        print(f"FAIL — {len(errors)} compile error(s)")
        for e in errors[:5]:
            print("  " + e[:200])
        return 1
    if "sorryAx" in axs:
        print("FAIL — still contains `sorry` (axioms include sorryAx)")
        return 1
    print(f"OK — compiles, no sorry")
    print(f"  axioms: {axs if axs else 'none'}")
    if args.baseline:
        base = {b.strip() for b in args.baseline.split(",") if b.strip()}
        extra = sorted(set(axs) - base)
        if extra:
            print(f"  NOTE: {extra} beyond the stated baseline {sorted(base)}")
            print("  (a change-detector, not a verdict — an axiom can enter via a "
                  "library lemma rather than from mathematical need)")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--config", default=None)
    sub = ap.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("search", help="query the corpus index")
    s.add_argument("query"); s.add_argument("-n", type=int, default=6)
    s.set_defaults(fn=cmd_search)

    g = sub.add_parser("goals", help="show the goal at each `sorry`")
    g.add_argument("file"); g.set_defaults(fn=cmd_goals)

    c = sub.add_parser("check", help="compile and report axioms")
    c.add_argument("file"); c.add_argument("name")
    c.add_argument("--baseline", default="", help="comma-separated axioms to compare against")
    c.set_defaults(fn=cmd_check)

    args = ap.parse_args()
    return args.fn(find_config(args.config), args)


if __name__ == "__main__":
    raise SystemExit(main())
