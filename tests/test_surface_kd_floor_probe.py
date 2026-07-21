import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_saved_kd_floor_probe_is_complete_and_explicitly_nonpromotional():
    payload = json.loads((ROOT / "probe_kd_born_grid16.json").read_text())
    assert payload["kind"] == "probe_only"
    assert payload["parents"] == payload["rows"] == 158
    assert payload["failures"] == 0
    assert all(row["positive"] for row in payload["rows_data"])
