"""Compare two fresh signed-bilinear candidate transcripts.

This is intentionally a same-source replay check.  It is useful provenance,
but it is not an independent proof and therefore never promotes K2/G2.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROW = re.compile(
    r"^ROW index=(\d+) lo=(\S+) hi=(\S+) grid=(\d+) "
    r"y3=(.*?) kd=(.*?) value=(.*?) margin=(.*?) verdict=(PASS|FAIL)$"
)


def transcript_rows(path: Path):
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = ROW.match(line)
        if match:
            groups = match.groups()
            rows.append({
                "index": int(groups[0]), "lo": groups[1], "hi": groups[2],
                "grid": int(groups[3]), "y3_abs": groups[4],
                "kd_lower": groups[5], "value_charge": groups[6],
                "margin": groups[7], "pass": groups[8] == "PASS",
            })
    return rows


def main(transcript: str, replay: str) -> int:
    production = transcript_rows(Path(transcript))
    replay_rows = transcript_rows(Path(replay))
    if len(production) != 158 or len(replay_rows) != 158:
        raise SystemExit("expected 158 rows in both sources")
    fields = ("index", "lo", "hi", "grid", "y3_abs", "kd_lower",
              "value_charge", "margin", "pass")
    for index, (left, right) in enumerate(zip(production, replay_rows)):
        for field in fields:
            if str(left[field]) != str(right[field]):
                raise SystemExit(
                    f"replay mismatch row {index}, field {field}: "
                    f"{left[field]!r} != {right[field]!r}")
    if Path(transcript).read_bytes() != Path(replay).read_bytes():
        raise SystemExit("replay row fields match, but transcript bytes differ")
    print("SIGNED-BILINEAR SAME-SOURCE REPLAY PASS")
    print("rows=158; all fields and transcript bytes equal")
    print("NO_G2_PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1], sys.argv[2]))
