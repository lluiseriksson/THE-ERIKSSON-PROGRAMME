"""Validate the exhaustive compact left-edge transcript."""

from decimal import Decimal
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = ROOT/"scripts"/"certify_left_edge_beta_taylor_transcript.txt"
BOX = re.compile(
    r"^beta-box \[([0-9.]+),([0-9.]+)\]: normalized=([0-9]+) regular=([0-9]+)$")
FINAL = ("CERTIFIED (left-edge, Arb): W<0 on (0,0.6] x [3.0,20.0]; "
         "beta_boxes=170 normalized_boxes=170 regular_boxes=883")


def validate(path=TRANSCRIPT):
    raw = Path(path).read_bytes()
    lines = raw.decode("utf-8").splitlines()
    if not lines or lines[-1] != FINAL:
        raise AssertionError("missing exact terminal CERTIFIED verdict")
    if any(line.startswith("narrowing beta step") for line in lines):
        raise AssertionError("unexpected beta-step refinement")
    provenance = {}
    for line in lines:
        if line.startswith("PROVENANCE "):
            key, value = line[len("PROVENANCE "):].split("=", 1)
            provenance[key] = value
    expected = {
        "script": "scripts/certify_left_edge_beta_taylor_arb.py",
        "script_sha256": "1ea85d53518f71dd4a1986e91b8b3c8df56fa9eaad01b462be2c5862019d6ddc",
        "git_head": "643c62d68758932bb896b1d236b41a0a1f590441",
        "python": "3.12.6",
        "python_flint": "0.9.0",
        "arb_prec_bits": "140",
        "bulk_dependency_sha256": "f69cfaadd311218a749039a64ad4ae3a68e4bd3e0527be5ac75744955f97b9aa",
    }
    if provenance != expected:
        raise AssertionError("provenance mismatch")
    config = "CONFIG beta_order=12 t_order=9 splice=1/5 initial_db=0.1"
    if config not in lines:
        raise AssertionError("configuration contract missing")
    for key, rel in (("script_sha256", provenance["script"]),
                     ("bulk_dependency_sha256",
                      "scripts/certify_bulk_beta_taylor_arb.py")):
        if hashlib.sha256((ROOT/rel).read_bytes()).hexdigest() != provenance[key]:
            raise AssertionError("worktree hash mismatch for "+rel)
    blob = subprocess.check_output(
        ["git", "show", provenance["git_head"]+":"+provenance["script"]],
        cwd=ROOT,
    )
    if hashlib.sha256(blob).hexdigest() != provenance["script_sha256"]:
        raise AssertionError("recorded commit blob mismatch")

    boxes = []
    for line in lines:
        match = BOX.match(line)
        if match:
            boxes.append((Decimal(match.group(1)), Decimal(match.group(2)),
                          int(match.group(3)), int(match.group(4))))
    if len(boxes) != 170:
        raise AssertionError("expected 170 beta boxes")
    cursor = Decimal("3.0")
    for lo, hi, normalized, regular in boxes:
        if lo != cursor or hi-lo != Decimal("0.1"):
            raise AssertionError("coverage gap/overlap at %s" % lo)
        if normalized <= 0 or regular <= 0:
            raise AssertionError("empty t cover at %s" % lo)
        cursor = hi
    if cursor != Decimal("20.0"):
        raise AssertionError("coverage does not end at beta=20")
    if sum(row[2] for row in boxes) != 170:
        raise AssertionError("normalized-box count mismatch")
    if sum(row[3] for row in boxes) != 883:
        raise AssertionError("regular-box count mismatch")
    return {
        "beta_boxes": 170,
        "normalized_boxes": 170,
        "regular_boxes": 883,
        "transcript_sha256": hashlib.sha256(raw).hexdigest(),
    }


if __name__ == "__main__":
    result = validate()
    print("left-edge transcript OK: {beta_boxes} beta boxes, "
          "{normalized_boxes} normalized, {regular_boxes} regular, "
          "sha256={transcript_sha256}".format(**result))
