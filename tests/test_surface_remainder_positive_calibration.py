from flint import arb, arb_series, ctx

from surface_remainder_positive_t_centered import _pilot_calibration, PREC


def test_pilot_calibration_uses_ratio_when_kd_is_separated():
    ctx.prec = 80
    pilot = {
        "KD": arb_series([arb(2), arb(0)], PREC),
        "KF": arb_series([arb(6), arb(0)], PREC),
    }
    calibration = _pilot_calibration(pilot)
    assert len(calibration) == PREC
    assert calibration[0] == 3
    assert all(value == 0 for value in calibration[1:])


def test_pilot_calibration_falls_back_to_zero_gauge_when_kd_contains_zero():
    ctx.prec = 80
    pilot = {
        "KD": arb_series([arb("0 +/- 1"), arb(0)], PREC),
        "KF": arb_series([arb(7), arb(0)], PREC),
    }
    calibration = _pilot_calibration(pilot)
    assert len(calibration) == PREC
    assert all(value == 0 for value in calibration)
