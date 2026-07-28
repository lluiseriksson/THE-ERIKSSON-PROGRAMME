import importlib.util
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "certify_delta0_endpoint",
    ROOT/"scripts"/"certify_surface_remainder_delta0_endpoint.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_provenance_owns_every_live_dependency():
    provenance = MOD.provenance()
    assert provenance["script"] == \
        "scripts/certify_surface_remainder_delta0_endpoint.py"
    for dependency in MOD.DEPENDENCIES:
        assert Path(dependency).stem+"_sha256" in provenance


def test_authoritative_terminal_word_is_not_design():
    source = Path(MOD.__file__).read_text(encoding="utf-8")
    assert "CERTIFIED (K2 endpoint, Arb)" in source
    assert "DESIGN_COVER_PASS" not in source
