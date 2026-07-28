from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import audit_surface_optional_hcube_removed as audit


def test_optional_hcube_is_absent_and_unconditional_bound_remains():
    assert audit.audit()
