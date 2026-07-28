"""Validate the two authoritative regular-K2 delta<=0.007 segments."""

import hashlib
import json
import re
from pathlib import Path

from flint import arb

import certify_surface_remainder_delta0_r4_extension_007 as cert
import surface_remainder_delta0_extension_probe as regular


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPTS = (
    ROOT/"scripts"/"certify_surface_remainder_delta0_r4_extension_007_part1.txt",
    ROOT/"scripts"/"certify_surface_remainder_delta0_r4_extension_007_part2.txt",
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate():
    hashes = {path: sha256(ROOT/path) for path in cert.DEPENDENCIES}
    boxes = list(regular.sealed.born_t_boxes())
    rows, segments, heads = {}, [], set()
    for path in TRANSCRIPTS:
        lines = path.read_text(encoding="utf-8").splitlines()
        if any("CERTIFICATE FAIL" in line for line in lines):
            raise AssertionError("certificate failure marker")
        head_lines = [line for line in lines
                      if line.startswith("PROVENANCE git_head ")]
        if len(head_lines) != 1:
            raise AssertionError("provenance head")
        heads.add(head_lines[0].split()[-1])
        dependencies = {line.split()[1]: line.split()[2] for line in lines
                        if line.startswith("DEPENDENCY ")}
        if dependencies != hashes:
            raise AssertionError("dependency mismatch")
        config = next(line for line in lines if line.startswith("CONFIG "))
        if ("delta_max 7/1000" not in config
                or "physical_inner 23/20" not in config
                or "band_radius 137/10" not in config):
            raise AssertionError("configuration mismatch")
        start, stop = map(
            int, re.search(r"start (\d+) stop (\d+)", config).groups())
        segments.append((start, stop))
        if sum(line.startswith("CERTIFIED SEGMENT ")
               for line in lines) != 1:
            raise AssertionError("terminal marker")
        for line in lines:
            if not line.startswith("ROW "):
                continue
            row = json.loads(line[4:])
            index = row["index"]
            if index in rows or not start <= index < stop:
                raise AssertionError("duplicate or misplaced index")
            lo, hi = boxes[index]
            if (row["t_lo"] != cert.fraction_string(lo)
                    or row["t_hi"] != cert.fraction_string(hi)):
                raise AssertionError("box mismatch")
            if (row["grid"] != cert.grid_for(index)
                    or row["band_radius"] != "137/10"):
                raise AssertionError("row contract")
            if not arb(row["margin_lower"]) > 0:
                raise AssertionError("nonpositive margin")
            rows[index] = row
    if segments != [(0, 119), (119, 158)]:
        raise AssertionError("segment partition")
    if len(heads) != 1 or set(rows) != set(range(158)):
        raise AssertionError("commit or cover mismatch")
    if any(boxes[index][1] != boxes[index+1][0]
           for index in range(157)):
        raise AssertionError("nonadjacent t partition")
    worst = min(rows.values(), key=lambda row: float(arb(row["margin_lower"])))
    print("K2 delta 0.007 transcripts OK: 158 boxes, band radius 137/10, "
          "worst index", worst["index"], "margin_lower",
          worst["margin_lower"])


if __name__ == "__main__":
    validate()
