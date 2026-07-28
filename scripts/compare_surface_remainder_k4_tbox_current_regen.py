"""Compare current K4 t-box regeneration with the historical candidate.

The comparison strips only the expected provenance changes (git head and the
single changed dependency digest).  Every mathematical row, cell, fraction,
and footer must otherwise agree exactly.  It is an audit aid, not a promotion.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
UNITS = [f"{i:03d}_{i+1:03d}" for i in range(300, 314)] + ["314_pi"]


def canonical(lines: list[str]) -> list[str]:
    out = []
    for line in lines:
        if line.startswith("PROVENANCE git_head "):
            continue
        if line.startswith("DEPENDENCY scripts/surface_remainder_centered_delta_carrier.py "):
            continue
        out.append(line)
    return out


def main() -> None:
    total = 0
    for unit in UNITS:
        old = ROOT / "scripts" / f"surface_remainder_k4_tbox_{unit}_20260723.txt"
        regen = ROOT / "scripts" / f"surface_remainder_k4_tbox_{unit}_20260723_current_regen.txt"
        rerun = ROOT / "scripts" / f"surface_remainder_k4_tbox_{unit}_20260723_current_regen_rerun.txt"
        if not (old.exists() and regen.exists() and rerun.exists()):
            raise SystemExit(f"missing unit {unit}")
        if regen.read_bytes() != rerun.read_bytes():
            raise SystemExit(f"production/replay mismatch {unit}")
        old_lines = old.read_text(encoding="utf-8").splitlines()
        regen_lines = regen.read_text(encoding="utf-8").splitlines()
        if canonical(old_lines) != canonical(regen_lines):
            for i, (a, b) in enumerate(zip(canonical(old_lines), canonical(regen_lines))):
                if a != b:
                    raise SystemExit(f"content mismatch {unit} line {i}: {a!r} != {b!r}")
            raise SystemExit(f"content length mismatch {unit}")
        total += sum(line.startswith("CELL ") for line in regen_lines)
        print(f"unit {unit} PASS cells {sum(line.startswith('CELL ') for line in regen_lines)}")
    print(f"K4 CURRENT REGEN CONTENT AUDIT PASS units {len(UNITS)} cells {total}")
    print("CANDIDATE ONLY; NO K4/S1'''/S2'''/G2/G6 PROMOTION")


if __name__ == "__main__":
    main()
