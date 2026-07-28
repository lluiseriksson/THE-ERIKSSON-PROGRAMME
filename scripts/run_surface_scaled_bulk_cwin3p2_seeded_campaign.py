"""Run a preregistered seeded-grid campaign without promoting G2.

The campaign is deliberately an evidence fabricator only.  Each beta unit
gets two fresh executions, byte equality is required, and a manifest is
written with ``promotion: NONE``.  The authoritative G2 audit does not read
these manifests until a separate human review changes their status.
"""

from __future__ import annotations

from fractions import Fraction
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts" / "certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_seeded_grid.py"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unit_name(lo: Fraction, hi: Fraction, step: Fraction) -> str:
    def slug(x):
        return str(x).replace("/", "_p_").replace("-", "m_")
    return f"{slug(lo)}_{slug(hi)}_seed{slug(step)}"


def run_one(lo: Fraction, hi: Fraction, seed_step: Fraction) -> int:
    unit = unit_name(lo, hi, seed_step)
    base = ROOT / "scripts" / f"surface_scaled_bulk_{unit}.txt"
    replay = ROOT / "scripts" / f"surface_scaled_bulk_{unit}_rerun.txt"
    command = [sys.executable, str(DRIVER), "--unit", unit,
               "--lo", str(lo), "--hi", str(hi), "--step", str(seed_step)]
    for output in (base, replay):
        result = subprocess.run(command, cwd=ROOT, text=True,
                                capture_output=True, check=False)
        output.write_text(result.stdout, encoding="utf-8")
        if result.returncode:
            failed = output.with_suffix(".failed.txt")
            failed.write_text(result.stdout, encoding="utf-8")
            print(f"FAIL {unit} exit={result.returncode}", flush=True)
            print(result.stderr, file=sys.stderr, flush=True)
            return result.returncode or 1
    equal = base.read_bytes() == replay.read_bytes()
    if not equal:
        print(f"FAIL {unit} production_replay_byte_mismatch", flush=True)
        return 2
    manifest = {
        "schema_version": 1,
        "run_id": f"surface-scaled-bulk-cwin3p2-seeded-{unit}",
        "claim_scope": (f"Diagnostic paired production/replay for beta [{lo},{hi}], "
                        f"CWIN=3/2 seeded-grid step {seed_step}; strict W rows only; "
                        "no G2/G6 or H_tail promotion."),
        "status": "current-candidate",
        "git_head_at_run": subprocess.check_output(
            ["git", "-c", f"safe.directory={ROOT.as_posix()}",
             "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "command": ["python", str(DRIVER.relative_to(ROOT)), "--unit", unit,
                    "--lo", str(lo), "--hi", str(hi), "--step", str(seed_step)],
        "inputs": [
            {"path": str(DRIVER.relative_to(ROOT)), "sha256": sha256(DRIVER)},
        ],
        "outputs": {
            "production": {"path": str(base.relative_to(ROOT)), "sha256": sha256(base)},
            "replay": {"path": str(replay.relative_to(ROOT)), "sha256": sha256(replay)},
        },
        "result": {"production_replay_byte_equal": True},
        "promotion": "NONE",
    }
    manifest_path = ROOT / "run-records" / "local-staging" / f"{manifest['run_id']}.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"PASS {unit} manifest={manifest_path.name}", flush=True)
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--lo", default="85")
    parser.add_argument("--hi", default="401/4")
    parser.add_argument("--beta-step", default="1/4")
    parser.add_argument("--seed-step", default="1/64")
    args = parser.parse_args()
    lo, hi = Fraction(args.lo), Fraction(args.hi)
    beta_step, seed_step = Fraction(args.beta_step), Fraction(args.seed_step)
    if not (lo < hi and beta_step > 0 and seed_step > 0):
        raise SystemExit("invalid campaign interval or step")
    beta = lo
    while beta < hi:
        beta2 = min(beta + beta_step, hi)
        code = run_one(beta, beta2, seed_step)
        if code:
            raise SystemExit(code)
        beta = beta2
