"""Validate the two authoritative regular-K2 delta<=0.006 segments."""

import hashlib, json, re
from pathlib import Path
from flint import arb
import certify_surface_remainder_delta0_r4_extension_006 as cert
import surface_remainder_delta0_extension_probe as regular

ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPTS = (
    ROOT/"scripts"/"certify_surface_remainder_delta0_r4_extension_006_part1.txt",
    ROOT/"scripts"/"certify_surface_remainder_delta0_r4_extension_006_part2.txt")

def sha256(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def validate():
    hashes = {p: sha256(ROOT/p) for p in cert.DEPENDENCIES}
    boxes = list(regular.sealed.born_t_boxes())
    rows, segments, heads = {}, [], set()
    for path in TRANSCRIPTS:
        lines = path.read_text(encoding="utf-8").splitlines()
        if any("CERTIFICATE FAIL" in x for x in lines): raise AssertionError("fail")
        hs = [x for x in lines if x.startswith("PROVENANCE git_head ")]
        if len(hs) != 1: raise AssertionError("head")
        heads.add(hs[0].split()[-1])
        deps = {x.split()[1]: x.split()[2] for x in lines
                if x.startswith("DEPENDENCY ")}
        if deps != hashes: raise AssertionError("dependency mismatch")
        config = next(x for x in lines if x.startswith("CONFIG "))
        start, stop = map(int, re.search(r"start (\d+) stop (\d+)", config).groups())
        segments.append((start, stop))
        if sum(x.startswith("CERTIFIED SEGMENT ") for x in lines) != 1:
            raise AssertionError("terminal")
        for line in lines:
            if not line.startswith("ROW "): continue
            row = json.loads(line[4:]); i = row["index"]
            if i in rows or not start <= i < stop: raise AssertionError("index")
            lo, hi = boxes[i]
            if row["t_lo"] != cert.fraction_string(lo) or row["t_hi"] != cert.fraction_string(hi): raise AssertionError("box")
            if row["grid"] != cert.grid_for(i) or row["band_radius"] != "71/5": raise AssertionError("contract")
            if not arb(row["margin_lower"]) > 0: raise AssertionError("margin")
            rows[i] = row
    if segments != [(0,137),(137,158)] or len(heads) != 1 or set(rows) != set(range(158)): raise AssertionError("cover")
    if any(boxes[i][1] != boxes[i+1][0] for i in range(157)): raise AssertionError("adjacency")
    worst = min(rows.values(), key=lambda r: float(arb(r["margin_lower"])))
    print("K2 delta 0.006 transcripts OK: 158 boxes, band radius 71/5, worst index", worst["index"], "margin_lower", worst["margin_lower"])

if __name__ == "__main__": validate()
