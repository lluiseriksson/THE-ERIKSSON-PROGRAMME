import importlib.util
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "delta0_series_cover_design",
    ROOT/"scripts"/"surface_remainder_delta0_series_cover_design.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_born_t_boxes_are_adjacent_and_fixed_width():
    boxes = list(MOD.born_t_boxes())
    assert len(boxes) == 158
    assert boxes[0][0] == 0
    for previous, current in zip(boxes, boxes[1:]):
        assert previous[1] == current[0]
        assert previous[1]-previous[0] == MOD.T_STEP
    assert boxes[-1][1]-boxes[-1][0] <= MOD.T_STEP


def test_design_cover_never_uses_certificate_terminal_word():
    source = (ROOT/"scripts"/"surface_remainder_delta0_series_cover_design.py").read_text(
        encoding="utf-8")
    assert "DESIGN_COVER_PASS" in source
    assert "CERTIFIED (" not in source
