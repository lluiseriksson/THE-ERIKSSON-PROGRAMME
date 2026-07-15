import surface_finite_beta_scaled_partition as partition


def test_single_driver_partition_is_exact_and_complete():
    assert partition.BETA_INTERVALS[0] == (partition.Fraction(20),
                                            partition.Fraction(201, 10))
    assert partition.BETA_INTERVALS[-1][1] == partition.BETA_STOP
    assert len(partition.BETA_INTERVALS) == 912
