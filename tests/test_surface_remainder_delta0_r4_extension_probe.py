from flint import arb, arb_series

import surface_remainder_delta0_r4_extension_probe as mod


def test_assembly_exposes_the_previously_unused_fourth_coefficient():
    # KD=1, KF=0, HDD=0, HDF=2*c*d*(1+...+5*d^4).
    t = arb("2.9")
    c = (t/4).cos()
    kd = arb_series([1, 0, 0, 0, 0, 0], 6)
    hdf = arb_series([0]+[2*c*k for k in range(1, 6)], 6)
    zero = arb_series([0], 6)
    y = mod.assemble_y_through_four({
        "kd": kd, "kf": zero, "hdd": zero, "hdf": hdf,
    }, t)
    assert [value.unique_fmpz() for value in y.coeffs()] == [1, 2, 3, 4, 5]


def test_r4_probe_contract_is_fixed_before_measurement():
    assert mod.DELTA_CANDIDATE.numerator == 1
    assert mod.DELTA_CANDIDATE.denominator == 200
    assert mod.GRID_LADDER == (192, 384, 768, 1024, 1536, 2048)
