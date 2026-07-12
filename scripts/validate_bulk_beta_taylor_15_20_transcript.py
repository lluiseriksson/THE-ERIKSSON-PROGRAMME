"""Validate the exhaustive [15,20] compact-relay extension transcript."""

from decimal import Decimal
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = ROOT / "scripts" / "certify_bulk_beta_taylor_15_20_transcript.txt"
BOX = re.compile(
    r"^beta-box \[([0-9.]+), ([0-9.]+)\]: ([0-9]+) t-boxes$")
FINAL = ("CERTIFIED (beta-Taylor, Arb): W < 0 on "
         "[0.6, pi-1.5/beta] x [15.0, 20.0]; 4736 t-boxes total")
NARROWING = ("narrowing beta step to 0.05 at beta=16.1 "
             "(bulk failure near t=3.0441141399384817)")


def validate(path=TRANSCRIPT):
    raw = Path(path).read_bytes()
    lines = raw.decode("utf-8").splitlines()
    if not lines or lines[-1] != FINAL:
        raise AssertionError("missing exact terminal CERTIFIED verdict")
    narrowing = [line for line in lines if line.startswith("narrowing beta step")]
    if narrowing != [NARROWING]:
        raise AssertionError("unexpected beta-step refinement history")

    provenance = {}
    for line in lines:
        if line.startswith("PROVENANCE "):
            key, value = line[len("PROVENANCE "):].split("=", 1)
            provenance[key] = value
    expected = {
        "script": "scripts/certify_bulk_beta_taylor_arb.py",
        "script_sha256": "f69cfaadd311218a749039a64ad4ae3a68e4bd3e0527be5ac75744955f97b9aa",
        "git_head": "668ed6ac4061f9930d0b2dfdd46ff312b755a296",
        "python": "3.12.6",
        "python_flint": "0.9.0",
        "arb_prec_bits": "130",
    }
    if provenance != expected:
        raise AssertionError("provenance mismatch")
    config = ("CONFIG prec=130 beta_order=12 t_order=9 initial_db=0.1 "
              "CWIN=3/2 PI_UP=31415927/10000000")
    if config not in lines:
        raise AssertionError("configuration contract missing")
    script = ROOT/provenance["script"]
    if hashlib.sha256(script.read_bytes()).hexdigest() != provenance["script_sha256"]:
        raise AssertionError("worktree script hash mismatch")
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
                          int(match.group(3))))
    if len(boxes) != 89:
        raise AssertionError("expected 89 beta boxes, got %d" % len(boxes))
    cursor = Decimal("15.0")
    for lo, hi, count in boxes:
        expected_step = Decimal("0.1") if lo < Decimal("16.1") else Decimal("0.05")
        if lo != cursor or hi-lo != expected_step or count <= 0:
            raise AssertionError("coverage gap/overlap or wrong step at %s" % lo)
        cursor = hi
    if cursor != Decimal("20.0"):
        raise AssertionError("coverage does not end at beta=20")
    if sum(count for _, _, count in boxes) != 4736:
        raise AssertionError("t-box count mismatch")
    return {
        "beta_boxes": 89,
        "t_boxes": 4736,
        "transcript_sha256": hashlib.sha256(raw).hexdigest(),
    }


if __name__ == "__main__":
    result = validate()
    print("bulk beta-Taylor [15,20] transcript OK: "
          "{beta_boxes} beta boxes, {t_boxes} t boxes, sha256={transcript_sha256}"
          .format(**result))
