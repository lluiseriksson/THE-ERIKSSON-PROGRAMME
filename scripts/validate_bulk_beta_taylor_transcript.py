"""Validate the exhaustive [6,15] beta-Taylor Arb transcript."""

from decimal import Decimal
import hashlib
from pathlib import Path
import platform
import re
import subprocess

import flint


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = ROOT / "scripts" / "certify_bulk_beta_taylor_arb_transcript.txt"
BOX = re.compile(
    r"^beta-box \[([0-9.]+), ([0-9.]+)\]: ([0-9]+) t-boxes$")
FINAL = ("CERTIFIED (beta-Taylor, Arb): W < 0 on "
         "[0.6, pi-1.5/beta] x [6.0, 15.0]; 3222 t-boxes total")


def validate(path=TRANSCRIPT):
    raw = Path(path).read_bytes()
    lines = raw.decode("utf-8").splitlines()
    text = "\n".join(lines)
    if not lines or lines[-1] != FINAL:
        raise AssertionError("missing exact terminal CERTIFIED verdict")
    if "narrowing beta step" in text:
        raise AssertionError("unexpected beta-step reduction in authoritative run")

    provenance = {}
    for line in lines:
        if line.startswith("PROVENANCE "):
            key, value = line[len("PROVENANCE "):].split("=", 1)
            provenance[key] = value
    required = {"script", "script_sha256", "git_head", "python",
                "python_flint", "arb_prec_bits"}
    if set(provenance) != required:
        raise AssertionError("incomplete or extra provenance fields")
    if provenance["arb_prec_bits"] != "130":
        raise AssertionError("wrong Arb precision")
    if provenance["python"] != platform.python_version():
        raise AssertionError("Python version drift")
    if provenance["python_flint"] != flint.__version__:
        raise AssertionError("python-flint version drift")
    config = ("CONFIG prec=130 beta_order=12 t_order=9 initial_db=0.1 "
              "CWIN=3/2 PI_UP=31415927/10000000")
    if config not in lines:
        raise AssertionError("configuration contract missing")

    script = ROOT / provenance["script"]
    digest = hashlib.sha256(script.read_bytes()).hexdigest()
    if digest != provenance["script_sha256"]:
        raise AssertionError("worktree script hash mismatch")
    blob = subprocess.check_output(
        ["git", "show", "%s:%s" %
         (provenance["git_head"], provenance["script"])], cwd=ROOT)
    if hashlib.sha256(blob).hexdigest() != digest:
        raise AssertionError("executed script does not match recorded commit blob")

    boxes = []
    for line in lines:
        match = BOX.match(line)
        if match:
            boxes.append((Decimal(match.group(1)), Decimal(match.group(2)),
                          int(match.group(3))))
    if len(boxes) != 90:
        raise AssertionError("expected 90 beta boxes, got %d" % len(boxes))
    cursor = Decimal("6.0")
    for lo, hi, count in boxes:
        if lo != cursor or hi-lo != Decimal("0.1") or count <= 0:
            raise AssertionError("coverage gap/overlap or empty box at %s" % lo)
        cursor = hi
    if cursor != Decimal("15.0"):
        raise AssertionError("coverage does not end at beta=15")
    if sum(count for _, _, count in boxes) != 3222:
        raise AssertionError("t-box count mismatch")
    return {
        "beta_boxes": len(boxes),
        "t_boxes": 3222,
        "transcript_sha256": hashlib.sha256(raw).hexdigest(),
    }


if __name__ == "__main__":
    result = validate()
    print("bulk beta-Taylor transcript OK: "
          "{beta_boxes} beta boxes, {t_boxes} t boxes, sha256={transcript_sha256}"
          .format(**result))
