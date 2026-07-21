"""Validate the saved KD floor probe without promoting it to G2."""

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("path", nargs="?", default="probe_kd_born_grid16.json")
    args = parser.parse_args()
    payload = json.loads((ROOT / args.path).read_text(encoding="utf-8"))
    assert payload["kind"] == "probe_only"
    assert payload["delta"] == "0.010 +/- 0.0005"
    assert payload["grid"] == 16
    assert payload["parent_start"] == 0
    assert payload["parent_stop"] == 158
    assert payload["parents"] == 158
    assert payload["rows"] == 158
    assert payload["failures"] == 0
    rows = payload["rows_data"]
    assert len(rows) == 158
    assert [row["parent"] for row in rows] == list(range(158))
    assert all(row["positive"] and row["cells"] == 256 for row in rows)
    print("KD FLOOR PROBE VALID", "rows=158", "grid=16", "failures=0")
    print("NO G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
