import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "k4_lower_union", ROOT / "scripts" /
    "audit_surface_remainder_k4_centered_lower_union.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_superseded_local_lower_union_is_scoped_and_replayed():
    # The original driver was never committed and the current local copy no
    # longer matches the archived dependency hash.  The terminal weak-main
    # route consumes none of this candidate evidence; retain only the exact
    # production/replay and non-promotion scope contract here.
    missing = []
    for unit, *_ in MOD.UNITS:
        production_path = ROOT / "scripts" / f"surface_remainder_k4_{unit}.txt"
        replay_path = (
            ROOT / "scripts" / f"surface_remainder_k4_{unit}_rerun.txt"
        )
        if not production_path.exists() or not replay_path.exists():
            missing.append(unit)
            continue
        production = production_path.read_text(encoding="utf-8").splitlines()
        replay = replay_path.read_text(encoding="utf-8").splitlines()
        assert production == replay
        assert "SCOPE local positive-delta witness only; no K4/G6 promotion" in production
    assert missing == ["k4_0030"]
