"""Validate the segmented endpoint-series production/replay union.

The validator certifies only the registered nominal endpoint lane
``[0,1/1000] x (0,pi]`` as a scoped analytic brick.  It deliberately refuses
to infer K2, G2, G6, or the positive-delta union from this lane.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
import re

from flint import arb


ROW = re.compile(
    r"ROW index=(\d+) lo=(\S+) hi=(\S+) grid=(\d+) "
    r"Y3_abs=(\[[^]]+\]) C_value=(\[[^]]+\]) margin=(\[[^]]+\]) "
    r"margin_lower=(\[[^]]+\]) margin_upper=(\[[^]]+\])"
)
PROV_HASH = re.compile(r"PROVENANCE script_sha256=([0-9a-f]{64})")


def parse(path: Path) -> tuple[dict[int, str], str]:
    text = path.read_text(encoding="utf-8")
    if "CANDIDATE_ENDPOINT_SEGMENT_PASS" not in text:
        raise ValueError(f"missing candidate scope marker: {path}")
    hashes = PROV_HASH.findall(text)
    if len(hashes) != 1:
        raise ValueError(f"bad provenance hash count: {path}")
    rows: dict[int, str] = {}
    for line in text.splitlines():
        match = ROW.fullmatch(line)
        if not match:
            continue
        index = int(match.group(1))
        if index in rows:
            raise ValueError(f"duplicate row {index}: {path}")
        lo, hi = Fraction(match.group(2)), Fraction(match.group(3))
        if Fraction(match.group(4)) not in (96, 192):
            raise ValueError(f"unexpected grid at row {index}: {path}")
        margin_lower = arb(match.group(8))
        if not margin_lower > 0:
            raise ValueError(f"non-positive margin at row {index}: {path}")
        rows[index] = line
    if not rows:
        raise ValueError(f"no rows: {path}")
    return rows, hashes[0]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--production", type=Path, nargs="+", required=True)
    parser.add_argument("--replay", type=Path, nargs="+", required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    args = parser.parse_args()
    production: dict[int, str] = {}
    replay: dict[int, str] = {}
    hashes: set[str] = set()
    for path in args.production:
        rows, digest = parse(path)
        hashes.add(digest)
        if production.keys() & rows.keys():
            raise SystemExit("production row overlap")
        production.update(rows)
    for path in args.replay:
        rows, digest = parse(path)
        hashes.add(digest)
        if replay.keys() & rows.keys():
            raise SystemExit("replay row overlap")
        replay.update(rows)
    if len(production) != 158 or len(replay) != 158:
        raise SystemExit(f"expected 158 rows, got production={len(production)} "
                         f"replay={len(replay)}")
    if sorted(production) != list(range(158)) or sorted(replay) != list(range(158)):
        raise SystemExit("born index coverage is not exactly 0..157")
    if production != replay:
        for index in range(158):
            if production.get(index) != replay.get(index):
                raise SystemExit(f"production/replay row mismatch at {index}")
    # Every transcript must execute the same wrapper bytes.
    script = Path(__file__).with_name("run_surface_remainder_delta0_endpoint_campaign.py")
    actual = hashlib.sha256(script.read_bytes()).hexdigest()
    if hashes != {actual}:
        raise SystemExit("wrapper hash mismatch")
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    if manifest.get("status") != "CERTIFIED_SCOPED_BRICK":
        raise SystemExit("manifest status mismatch")
    if manifest.get("born_boxes") != 158:
        raise SystemExit("manifest born-box count mismatch")
    manifest_paths = {
        item["production"] for item in manifest["segments"]
    } | {item["replay"] for item in manifest["segments"]}
    actual_paths = {p.name for p in args.production + args.replay}
    if manifest_paths != actual_paths:
        raise SystemExit("manifest segment set mismatch")
    for item in manifest["segments"]:
        for key in ("production", "replay"):
            file_path = args.manifest.parent.parent / item[key]
            digest = hashlib.sha256(file_path.read_bytes()).hexdigest().upper()
            if digest != item["sha256"]:
                raise SystemExit(f"manifest hash mismatch: {item[key]}")
    print("ENDPOINT SERIES UNION CERTIFIED: 158/158 rows, exact replay, "
          "strict margins")
    print("SCOPE ONLY: delta=[0,1/1000] nominal endpoint; "
          "NO K2/G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
