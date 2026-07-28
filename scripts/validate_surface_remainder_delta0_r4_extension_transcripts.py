"""Validate both authoritative [0,1/200] exact-r4 regular segments."""

import hashlib
import json
from pathlib import Path
import re

from flint import arb

import certify_surface_remainder_delta0_r4_extension as cert
import surface_remainder_delta0_extension_probe as regular


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPTS = (
    ROOT/"scripts"/"certify_surface_remainder_delta0_r4_extension_part1.txt",
    ROOT/"scripts"/"certify_surface_remainder_delta0_r4_extension_part2.txt",
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate():
    expected_hashes = {relative: sha256(ROOT/relative)
                       for relative in cert.DEPENDENCIES}
    expected_boxes = list(regular.sealed.born_t_boxes())
    rows, segments, heads = {}, [], set()
    for path in TRANSCRIPTS:
        lines = path.read_text(encoding="utf-8").splitlines()
        if any("CERTIFICATE FAIL" in line for line in lines):
            raise AssertionError(f"failure marker in {path.name}")
        head_lines = [line for line in lines
                      if line.startswith("PROVENANCE git_head ")]
        if len(head_lines) != 1:
            raise AssertionError("missing unique git provenance")
        heads.add(head_lines[0].split()[-1])
        dependencies = {}
        for line in lines:
            if line.startswith("DEPENDENCY "):
                _, relative, digest = line.split()
                dependencies[relative] = digest
        if dependencies != expected_hashes:
            raise AssertionError(f"dependency mismatch in {path.name}")
        config = next((line for line in lines if line.startswith("CONFIG ")),
                      None)
        match = re.search(r"start (\d+) stop (\d+)", config or "")
        if not match:
            raise AssertionError("missing segment config")
        start, stop = map(int, match.groups())
        segments.append((start, stop))
        terminal = [line for line in lines
                    if line.startswith("CERTIFIED SEGMENT ")]
        if len(terminal) != 1:
            raise AssertionError("missing unique segment certificate")
        for line in lines:
            if not line.startswith("ROW "):
                continue
            row = json.loads(line[4:])
            index = row["index"]
            if index in rows:
                raise AssertionError(f"duplicate row {index}")
            if not start <= index < stop:
                raise AssertionError("row outside declared segment")
            lo, hi = expected_boxes[index]
            if (row["t_lo"] != cert.fraction_string(lo)
                    or row["t_hi"] != cert.fraction_string(hi)):
                raise AssertionError(f"parameter mismatch at {index}")
            if row["grid"] != cert.grid_for(index):
                raise AssertionError(f"grid mismatch at {index}")
            if not arb(row["margin_lower"]) > 0:
                raise AssertionError(f"nonpositive margin at {index}")
            rows[index] = row
    if segments != [(0, 151), (151, 158)]:
        raise AssertionError(f"unexpected segment partition {segments}")
    if len(heads) != 1:
        raise AssertionError("segments were not executed from one commit")
    if set(rows) != set(range(158)):
        raise AssertionError("incomplete 158-box cover")
    for index in range(157):
        if expected_boxes[index][1] != expected_boxes[index+1][0]:
            raise AssertionError("born cover is not adjacent")
    worst = min(rows.values(), key=lambda row: float(arb(row["margin_lower"])))
    print("K2 exact-r4 extension transcripts OK: 158 boxes, worst index",
          worst["index"], "margin_lower", worst["margin_lower"])


if __name__ == "__main__":
    validate()
