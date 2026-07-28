"""Validate the aggregate KD floor probe manifest and its raw partitions."""

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "run-manifests/surface-kd-floor-union-20260721.json"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    assert manifest["status"] == "PROBE_ONLY"
    assert manifest["total_rows"] == 3002
    assert manifest["total_failures"] == 0
    previous = None
    rows = 0
    for part in manifest["delta_partition"]:
        raw = next(ROOT.glob(f"probe_kd_delta_{part['lo'].replace('/', '')}*"), None)
        # Use the manifest's explicit raw hash and locate by exact digest;
        # this prevents silently validating a different same-shaped output.
        candidates = list(ROOT.glob("probe_kd_delta_*.json"))
        matching = [p for p in candidates if sha256(p) == part["sha256"]]
        assert len(matching) == 1, (part, matching)
        payload = json.loads(matching[0].read_text(encoding="utf-8"))
        assert payload["kind"] == "probe_only"
        assert payload["rows"] == part["rows"]
        assert payload["failures"] == part["failures"] == 0
        assert all(row["positive"] for row in payload["rows_data"])
        rows += payload["rows"]
        assert previous is None or previous == part["lo"]
        previous = part["hi"]
    assert rows == manifest["total_rows"]
    print("KD FLOOR UNION VALID", "rows=3002", "failures=0")
    print("PROBE_ONLY; NO G2/G6 PROMOTION")


if __name__ == "__main__":
    main()
