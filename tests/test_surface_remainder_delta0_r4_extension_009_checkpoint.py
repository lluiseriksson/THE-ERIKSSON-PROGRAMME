import pytest

import surface_remainder_delta0_r4_extension_009_checkpoint as checkpoint
import surface_remainder_delta0_r4_extension_009_fixed_cover as fixed


def test_checkpoint_uses_only_the_frozen_grid_map():
    assert checkpoint.fixed is fixed
    assert [checkpoint.fixed.grid_for(index) for index in range(158)] == (
        [384]*50+[192]*96+[384]*12)


def test_checkpoint_rejects_indices_outside_the_born_partition(monkeypatch):
    monkeypatch.setattr("sys.argv", ["checkpoint", "--index", "158"])
    with pytest.raises(SystemExit):
        checkpoint.main()

