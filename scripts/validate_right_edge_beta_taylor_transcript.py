"""Validate the exhaustive compact moving-right-edge transcript union."""

from decimal import Decimal
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
SPECS = (
    (ROOT/"scripts"/"certify_right_edge_beta_taylor_3_10_transcript.txt",
     Decimal("3.0"), Decimal("10.0"), Decimal("0.1"),
     "d7919ff2f64ffd17669aab4fc756070cbb942a18"),
    (ROOT/"scripts"/"certify_right_edge_beta_taylor_10_15_transcript.txt",
     Decimal("10.0"), Decimal("15.0"), Decimal("0.05"),
     "d7919ff2f64ffd17669aab4fc756070cbb942a18"),
    (ROOT/"scripts"/"certify_right_edge_beta_taylor_15_17p5_transcript.txt",
     Decimal("15.0"), Decimal("17.5"), Decimal("0.025"),
     "d7919ff2f64ffd17669aab4fc756070cbb942a18"),
    (ROOT/"scripts"/"certify_right_edge_beta_taylor_17p5_19_transcript.txt",
     Decimal("17.5"), Decimal("19.0"), Decimal("0.025"),
     "f2facea71af230de9eaba029f1821e65bdc025e4"),
    (ROOT/"scripts"/"certify_right_edge_beta_taylor_19_19p75_transcript.txt",
     Decimal("19.0"), Decimal("19.75"), Decimal("0.0125"),
     "f2facea71af230de9eaba029f1821e65bdc025e4"),
    (ROOT/"scripts"/"certify_right_edge_beta_taylor_19p75_20_transcript.txt",
     Decimal("19.75"), Decimal("20.0"), Decimal("0.0125"),
     "f2facea71af230de9eaba029f1821e65bdc025e4"),
)
BOX = re.compile(
    r"^beta-box \[([0-9.]+),([0-9.]+)\]: normalized=([0-9]+) regular=([0-9]+)$")
FINAL = re.compile(
    r"^CERTIFIED \(right-edge, Arb\): W<0 on "
    r"pi-1\.5/beta<=t<pi x \[([0-9.]+),([0-9.]+)\]; beta_boxes=([0-9]+) "
    r"normalized_boxes=([0-9]+) regular_boxes=([0-9]+)$")
EXPECTED_PROVENANCE = {
    "script": "scripts/certify_right_edge_beta_taylor_arb.py",
    "script_sha256": "d614f97a120b13b8cb02b00f6906fd76780c6c329062cdc71fec499083137cdc",
    "python": "3.12.6",
    "python_flint": "0.9.0",
    "arb_prec_bits": "140",
    "bulk_dependency_sha256": "f69cfaadd311218a749039a64ad4ae3a68e4bd3e0527be5ac75744955f97b9aa",
}


def _validate_one(path, start, end, initial_step, git_head):
    raw = Path(path).read_bytes()
    lines = raw.decode("utf-8").splitlines()
    if not lines:
        raise AssertionError("empty transcript: "+str(path))
    final = FINAL.match(lines[-1])
    if final is None:
        raise AssertionError("missing exact terminal CERTIFIED verdict: "+str(path))
    if Decimal(final.group(1)) != start or Decimal(final.group(2)) != end:
        raise AssertionError("terminal range mismatch: "+str(path))
    provenance = {}
    for line in lines:
        if line.startswith("PROVENANCE "):
            key, value = line[len("PROVENANCE "):].split("=", 1)
            provenance[key] = value
    expected_provenance = dict(EXPECTED_PROVENANCE, git_head=git_head)
    if provenance != expected_provenance:
        raise AssertionError("provenance mismatch: "+str(path))
    config = ("CONFIG beta_order=12 d_order=9 CWIN=3/2 splice=1/500 "
              "initial_db=%s" % initial_step)
    if config not in lines:
        raise AssertionError("configuration contract missing: "+str(path))

    boxes = []
    for line in lines:
        match = BOX.match(line)
        if match:
            boxes.append((Decimal(match.group(1)), Decimal(match.group(2)),
                          int(match.group(3)), int(match.group(4))))
    cursor = start
    for lo, hi, normalized, regular in boxes:
        if lo != cursor or not (Decimal(0) < hi-lo <= initial_step):
            raise AssertionError("coverage gap/overlap at %s" % lo)
        if normalized <= 0 or regular <= 0:
            raise AssertionError("empty right-edge lane at %s" % lo)
        cursor = hi
    if cursor != end:
        raise AssertionError("coverage does not end at %s" % end)
    totals = (len(boxes), sum(row[2] for row in boxes),
              sum(row[3] for row in boxes))
    declared = tuple(int(final.group(index)) for index in (3, 4, 5))
    if totals != declared:
        raise AssertionError("terminal box totals do not match exhaustive rows")
    return totals, hashlib.sha256(raw).hexdigest()


def validate(specs=SPECS):
    for key, rel in (("script_sha256", EXPECTED_PROVENANCE["script"]),
                     ("bulk_dependency_sha256",
                      "scripts/certify_bulk_beta_taylor_arb.py")):
        if hashlib.sha256((ROOT/rel).read_bytes()).hexdigest() \
                != EXPECTED_PROVENANCE[key]:
            raise AssertionError("worktree hash mismatch for "+rel)
    aggregate = [0, 0, 0]
    hashes = {}
    cursor = Decimal("3.0")
    checked_heads = set()
    for path, start, end, step, git_head in specs:
        if start != cursor:
            raise AssertionError("chunk union gap/overlap at %s" % start)
        if git_head not in checked_heads:
            blob = subprocess.check_output(
                ["git", "show", git_head+":"+EXPECTED_PROVENANCE["script"]],
                cwd=ROOT)
            if hashlib.sha256(blob).hexdigest() \
                    != EXPECTED_PROVENANCE["script_sha256"]:
                raise AssertionError("recorded commit blob mismatch")
            checked_heads.add(git_head)
        totals, digest = _validate_one(path, start, end, step, git_head)
        aggregate = [x+y for x, y in zip(aggregate, totals)]
        hashes[Path(path).name] = digest
        cursor = end
    if cursor != Decimal("20.0"):
        raise AssertionError("chunk union does not end at beta=20")
    return {
        "beta_boxes": aggregate[0],
        "normalized_boxes": aggregate[1],
        "regular_boxes": aggregate[2],
        "transcript_sha256": hashes,
    }


if __name__ == "__main__":
    result = validate()
    print("right-edge transcript union OK: {beta_boxes} beta boxes, "
          "{normalized_boxes} normalized, {regular_boxes} regular".format(
              **result))
