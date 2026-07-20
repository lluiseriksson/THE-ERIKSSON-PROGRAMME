from scripts.validate_surface_bulk_3_6 import validate


def test_canonical_surface_bulk_3_6_transcript():
    result = validate()
    assert result["beta_boxes"] == 3472
    assert result["t_boxes"] == 592068
