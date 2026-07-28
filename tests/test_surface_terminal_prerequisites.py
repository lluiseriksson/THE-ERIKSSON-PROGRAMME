from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import audit_surface_terminal_prerequisites as terminal_prerequisites


def test_terminal_prerequisites_are_rebuilt_from_evidence():
    result = terminal_prerequisites.audit()
    assert result["promotion"] == "TERMINAL_PREREQUISITES_PROVED"
    assert result["thmb_witnesses"] == 2
    assert result["bulk_beta_boxes"] == 3651
    assert result["bulk_t_boxes"] == 600_026
    assert result["left_beta_boxes"] == 170
    assert result["right_beta_boxes"] == 410
