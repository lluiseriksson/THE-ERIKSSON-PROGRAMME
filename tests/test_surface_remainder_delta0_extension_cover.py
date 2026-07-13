from fractions import Fraction

import surface_remainder_delta0_extension_cover as mod


def test_cover_configuration_is_fixed():
    assert mod.DELTA_MAX == Fraction(1, 250)
    assert mod.GRIDS == (96, 192, 384, 768, 1024)
    assert tuple(sorted(mod.GRIDS)) == mod.GRIDS


def test_resume_index_does_not_change_born_partition():
    boxes = list(mod.probe.sealed.born_t_boxes())
    assert len(boxes[33:]) == len(boxes)-33
    assert boxes[32][1] == boxes[33][0]
