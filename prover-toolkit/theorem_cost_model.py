#!/usr/bin/env python3
"""Cost per verified theorem, computed from measured harness runs.

The unit is

    kappa = (cost of one agent attempt) / (probability that attempt verifies)

i.e. expected spend per *verified* theorem, not per token.  Everything here is
derived from a run file produced by `harness.py`; there are no placeholder
success rates.

Two things this deliberately does differently from a naive spreadsheet:

**The success rate carries an interval.**  A pilot of a few dozen attempts
estimates p poorly, and kappa = C/p is hyperbolic in p, so a point estimate is
actively misleading near p = 0.  Every kappa is reported as a range derived
from a Wilson score interval on p.  When zero attempts succeed the point
estimate of kappa is infinite and only the *lower bound* is finite; that lower
bound is the honest number to quote, and it is usually the one that settles the
decision.

**Local and hosted costs are not the same kind of quantity.**  A hosted API
bills tokens.  A local model bills wall-clock on hardware you already own, so
its marginal cash cost is electricity.  Both are reported, but they are not
added together or silently compared.

    python3 theorem_cost_model.py runs/goedel8b-pilot.jsonl --by-group
"""

from __future__ import annotations

import argparse
import json
import math
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

# ---------------------------------------------------------------------------
# Pricing. Hosted rates are $ per 1M tokens (input, output).
# Sources are recorded so a stale figure is visible rather than assumed.
# ---------------------------------------------------------------------------

HOSTED_PRICING: dict[str, tuple[float, float, str]] = {
    # name: (input $/1M, output $/1M, note)
    "deepseek-prover-v2-671b (DeepInfra)": (0.50, 2.18, "handoff, 2026-08"),
    "claude-sonnet-4-6": (3.00, 15.00, "list price"),
    "claude-opus-4-6": (15.00, 75.00, "list price"),
}

# Apple M4 Pro under sustained inference load. Measured figures should replace
# these; they are the only numbers here that are not derived from the run file.
LOCAL_POWER_W = 45.0
ELECTRICITY_PER_KWH = 0.27  # GBP/kWh, UK domestic cap, 2026


@dataclass
class Stats:
    attempts: int
    successes: int
    prompt_tokens: int
    completion_tokens: int
    gen_seconds: float
    verify_seconds: float

    @property
    def p(self) -> float:
        return self.successes / self.attempts if self.attempts else 0.0

    def wilson(self, z: float = 1.96) -> tuple[float, float]:
        """Wilson score interval for the success probability."""
        n = self.attempts
        if n == 0:
            return (0.0, 1.0)
        phat = self.successes / n
        denom = 1 + z * z / n
        centre = (phat + z * z / (2 * n)) / denom
        halfwidth = (
            z * math.sqrt(phat * (1 - phat) / n + z * z / (4 * n * n)) / denom
        )
        return (max(0.0, centre - halfwidth), min(1.0, centre + halfwidth))

    @property
    def mean_prompt(self) -> float:
        return self.prompt_tokens / self.attempts if self.attempts else 0.0

    @property
    def mean_completion(self) -> float:
        return self.completion_tokens / self.attempts if self.attempts else 0.0

    @property
    def mean_gen_s(self) -> float:
        return self.gen_seconds / self.attempts if self.attempts else 0.0


def load(paths: list[Path]) -> list[dict]:
    recs = []
    for p in paths:
        for line in p.read_text().splitlines():
            if line.strip():
                recs.append(json.loads(line))
    return recs


def aggregate(recs: list[dict], key) -> dict[str, Stats]:
    buckets: dict[str, list[dict]] = defaultdict(list)
    for r in recs:
        buckets[key(r)].append(r)
    out = {}
    for name, rs in buckets.items():
        out[name] = Stats(
            attempts=len(rs),
            successes=sum(1 for r in rs if r.get("ok")),
            prompt_tokens=sum(r.get("prompt_tokens") or 0 for r in rs),
            completion_tokens=sum(r.get("completion_tokens") or 0 for r in rs),
            gen_seconds=sum(r.get("gen_seconds") or 0.0 for r in rs),
            verify_seconds=sum(r.get("verify_seconds") or 0.0 for r in rs),
        )
    return out


def fmt_kappa(cost_per_attempt: float, s: Stats) -> str:
    """kappa with an interval, formatted for reading."""
    lo_p, hi_p = s.wilson()
    # High p gives low kappa, so the bounds swap.
    lo_k = cost_per_attempt / hi_p if hi_p > 0 else float("inf")
    hi_k = cost_per_attempt / lo_p if lo_p > 0 else float("inf")
    if s.successes == 0:
        return f">= ${lo_k:,.2f}  (0/{s.attempts}; p<={hi_p:.2f} at 95%)"
    point = cost_per_attempt / s.p
    if math.isinf(hi_k):
        return f"${point:,.2f}  (95% CI: ${lo_k:,.2f} - unbounded)"
    return f"${point:,.2f}  (95% CI: ${lo_k:,.2f} - ${hi_k:,.2f})"


def report_group(name: str, s: Stats, hosted: bool = True) -> None:
    lo, hi = s.wilson()
    print(f"\n### {name}")
    print(f"  attempts          {s.attempts}")
    print(f"  verified          {s.successes}  "
          f"(p = {s.p:.3f}, 95% CI {lo:.3f}-{hi:.3f})")
    print(f"  mean tokens       {s.mean_prompt:,.0f} in / "
          f"{s.mean_completion:,.0f} out")
    print(f"  mean generation   {s.mean_gen_s:,.1f} s")

    # Local: electricity plus the wall-clock it occupies.
    kwh = (s.mean_gen_s / 3600.0) * (LOCAL_POWER_W / 1000.0)
    local_cost = kwh * ELECTRICITY_PER_KWH
    print(f"  local (M4 Pro)    {fmt_kappa(local_cost, s)}"
          f"   [electricity only, @{LOCAL_POWER_W:.0f} W]")
    if s.p > 0:
        print(f"                    {s.mean_gen_s / s.p / 60:,.1f} min of "
              f"wall-clock per verified theorem")
    else:
        hrs = s.mean_gen_s / hi / 3600 if hi > 0 else float("inf")
        print(f"                    >= {hrs:,.1f} h of wall-clock per verified "
              f"theorem (95% bound)")

    if not hosted:
        return
    for model, (pin, pout, note) in HOSTED_PRICING.items():
        cost = (s.mean_prompt * pin + s.mean_completion * pout) / 1e6
        print(f"  {model:<36s} {fmt_kappa(cost, s)}")
        print(f"  {'':<36s}   ${cost:.4f}/attempt  [{note}]")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("runs", type=Path, nargs="+")
    ap.add_argument("--by-group", action="store_true")
    ap.add_argument("--by-reason", action="store_true")
    args = ap.parse_args()

    recs = load(args.runs)
    if not recs:
        print("no records")
        return 1

    models = sorted({r.get("model", "?") for r in recs})
    print("=" * 72)
    print("COST PER VERIFIED THEOREM")
    print(f"run files : {', '.join(str(p) for p in args.runs)}")
    print(f"model(s)  : {', '.join(models)}")
    print(f"records   : {len(recs)}")
    print("=" * 72)

    overall = aggregate(recs, lambda r: "ALL")
    report_group("overall", overall["ALL"])

    if args.by_group:
        print("\n" + "-" * 72)
        print("BY GROUP  (the control/target split is the point of the pilot)")
        print("-" * 72)
        for name, s in sorted(aggregate(recs, lambda r: r.get("group", "?")).items()):
            report_group(name, s, hosted=False)

    if args.by_reason:
        print("\n" + "-" * 72)
        print("FAILURE MODES")
        print("-" * 72)
        counts: dict[str, int] = defaultdict(int)
        for r in recs:
            if not r.get("ok"):
                counts[r.get("reason", "?")] += 1
        total = sum(counts.values())
        for reason, n in sorted(counts.items(), key=lambda kv: -kv[1]):
            print(f"  {n:5d}  ({100*n/total:5.1f}%)  {reason}")

    print("\n" + "=" * 72)
    print("Local and hosted figures are different kinds of cost: the local row")
    print("is marginal electricity on hardware already owned, the hosted rows")
    print("are cash per token. They are not comparable without also pricing")
    print("your own wall-clock time.")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
