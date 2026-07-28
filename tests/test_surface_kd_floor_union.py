import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_kd_floor_union_has_contiguous_zero_failure_partition():
    manifest = json.loads(
        (ROOT / "run-manifests/surface-kd-floor-union-20260721.json")
        .read_text()
    )
    assert manifest["status"] == "PROBE_ONLY"
    assert manifest["total_rows"] == 3002
    assert manifest["total_failures"] == 0
    parts = manifest["delta_partition"]
    assert parts[0]["lo"] == "1/1000"
    assert parts[-1]["hi"] == "1/15"
    assert all(left["hi"] == right["lo"] for left, right in zip(parts, parts[1:]))
    assert all(part["failures"] == 0 for part in parts)
