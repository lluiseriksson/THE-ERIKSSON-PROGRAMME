"""Validate the recorded G5 half-line archive against its source commit.

The current worktree validator has evolved (its pair-order check is now
order-free), so it cannot directly validate transcripts generated at the
historical head.  This audit binds every recorded dependency to the exact
``git show`` blob named by the transcript, checks all 600 rows and strict
positive lower bounds, and compares production/replay after removing only
wall-clock fields.  It does not promote any other gate.
"""

import hashlib
import json
import re
import subprocess
from pathlib import Path

from flint import arb

import certify_surface_right_edge_five_family_halfline as cert


ROOT = Path(__file__).resolve().parents[1]
HEAD = "1da7e4148f03ebafa350756e0981f647a3e8954e"
PREFIX = "certify_surface_right_edge_five_family_halfline_"
ELAPSED = re.compile(r"(elapsed_seconds\s+)[^\s]+$")


def blob_hash(path: str) -> str:
    blob = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "show", f"{HEAD}:{path}"],
        cwd=ROOT,
    )
    return hashlib.sha256(blob).hexdigest()


def normalized(lines):
    out = []
    for line in lines:
        if line.startswith("CERTIFIED RIGHT-EDGE"):
            line = ELAPSED.sub(r"\1<wall-clock>", line)
        out.append(line)
    return out


def validate() -> list[dict]:
    rows = []
    for unit in cert.UNITS:
        slug = cert.unit_slug(unit)
        prod = ROOT / "scripts" / f"{PREFIX}{slug}_transcript.txt"
        replay = ROOT / "scripts" / f"{PREFIX}{slug}_rerun_transcript.txt"
        plines = prod.read_text(encoding="utf-8").splitlines()
        rlines = replay.read_text(encoding="utf-8").splitlines()
        assert f"PROVENANCE git_head {HEAD}" in plines
        assert normalized(plines) == normalized(rlines), slug
        dependencies = {
            line.split()[1]: line.split()[2]
            for line in plines if line.startswith("DEPENDENCY ")
        }
        assert dependencies
        assert dependencies == {path: blob_hash(path) for path in dependencies}, slug
        unit_rows = [json.loads(line[4:]) for line in plines if line.startswith("ROW ")]
        assert len(unit_rows) == 40, slug
        for row in unit_rows:
            assert len(row["families_lower"]) == 5
            assert row["P0_lower"] and arb(row["P0_lower"]) > 0
            assert arb(row["H_lower"]) > 0
        rows.extend(unit_rows)
    pairs = {(row["delta_index"], row["lambda_index"]) for row in rows}
    expected = {(d, l) for d in range(8) for l in range(75)}
    assert len(rows) == 600 and pairs == expected
    return rows


def main() -> int:
    rows = validate()
    worst = min(rows, key=lambda row: float(arb(row["H_lower"])))
    print("G5 HISTORICAL HALF-LINE VALIDATION PASS: 600/600")
    print("source_head", HEAD, "worst", worst["delta_index"],
          worst["lambda_index"], "H_lower", worst["H_lower"])
    print("SCOPE G5 half-line archive only; no G2/K4/S1'''/S2'''/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
