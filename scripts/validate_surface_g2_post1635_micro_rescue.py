"""Independent validator for the candidate post-1635 micro-rescue pair."""

from pathlib import Path
import hashlib
import re

from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
PROD = ROOT / "scripts/surface_scaled_bulk_post1635_micro_rescue_20260725.txt"
REPLAY = ROOT / "scripts/surface_scaled_bulk_post1635_micro_rescue_20260725_rerun.txt"
EXPECTED = {
    "scripts/probe_surface_g2_post1635_micro_rescue.py",
    "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high.py",
    "scripts/certify_bulk_beta_taylor_scaled_design.py",
    "scripts/certify_bulk_beta_taylor_arb.py",
    "docs/SURFACE-G2-POST1635-MICRO-RESCUE-PREREG-20260725.md",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(path: Path) -> None:
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED BULK G2 POST1635 MICRO RESCUE"
    assert "config CWIN 3/2 beta_order 30 t_order 37 min_dt 1/100000000 prec 180" in lines
    assert "beta_domain 1635/16 3271/32" in lines
    assert "t_domain 3123099/1000000 31231/10000" in lines
    deps = {}
    rows = []
    for line in lines:
        if line.startswith("dependency "):
            _, name, _, digest = line.split()
            deps[name] = digest
        if line.startswith("trow "):
            m = re.match(r"trow (\d+) ([^ ]+) ([^ ]+) upper (.+)$", line)
            assert m is not None
            rows.append((m.group(2), m.group(3), arb(m.group(4))))
    assert set(deps) == EXPECTED
    assert all(digest == sha256(ROOT / name) for name, digest in deps.items())
    assert len(rows) == 1
    assert rows[0][0] == "3123099/1000000"
    assert rows[0][1] == "31231/10000"
    assert rows[0][2].upper() < arb(0)
    assert "t_rows 1" in lines
    assert "G2 POST1635 MICRO RESCUE PASS" in lines
    assert "SCOPE candidate-only local row rescue; no G2/G6 promotion" in lines


def main() -> int:
    ctx.prec = 180
    assert PROD.is_file() and REPLAY.is_file()
    assert PROD.read_bytes() == REPLAY.read_bytes()
    validate(PROD)
    print("G2 POST1635 MICRO RESCUE VALIDATION PASS")
    print("rows 1")
    print("production_replay_byte_equal True")
    print("scope candidate-only; no G2/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

