"""Validate the exact fifth-head symbolic transcript."""

import hashlib
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = ROOT/"scripts"/"surface_remainder_delta0_fifth_coefficient_transcript.txt"
SCRIPT = "scripts/surface_remainder_delta0_fifth_coefficient.py"
SCRIPT_SHA = "1dd66f589d50c1c2a927d8158e2a850a8c19f30f735bf52ac05a9d99efa9eb0d"
HEAD = "5defcffd7b70978e3b4f1628b425f0491e22536d"
COEFFICIENT = ("Y delta coefficient 4 = (12940*c**10 + 16077*c**8 + "
               "173288*c**6 - 1300912*c**4 + 1358400*c**2 - 346112)"
               "/(262144*c**15)")


def validate(path=TRANSCRIPT):
    raw = Path(path).read_bytes()
    lines = raw.decode("utf-8").splitlines()
    expected_prefix = [
        "PROVENANCE script="+SCRIPT,
        "PROVENANCE script_sha256="+SCRIPT_SHA,
        "PROVENANCE git_head="+HEAD,
        "PROVENANCE python=3.12.6",
        "PROVENANCE sympy=1.14.0",
    ]
    if lines[:5] != expected_prefix:
        raise AssertionError("fifth-head provenance mismatch")
    if len(lines) != 7 or lines[5] != COEFFICIENT or \
            lines[6] != "TARGET MATCH: fifth coefficient r5(c)":
        raise AssertionError("fifth-head coefficient block mismatch")
    worktree = (ROOT/SCRIPT).read_bytes()
    if hashlib.sha256(worktree).hexdigest() != SCRIPT_SHA:
        raise AssertionError("fifth-head worktree hash mismatch")
    blob = subprocess.check_output(["git", "show", HEAD+":"+SCRIPT], cwd=ROOT)
    if hashlib.sha256(blob).hexdigest() != SCRIPT_SHA:
        raise AssertionError("fifth-head executed blob mismatch")
    lf = raw.replace(b"\r\n", b"\n")
    return {"raw_sha256": hashlib.sha256(raw).hexdigest(),
            "lf_sha256": hashlib.sha256(lf).hexdigest()}


if __name__ == "__main__":
    result = validate()
    print("fifth-head transcript OK: raw={raw_sha256} lf={lf_sha256}".format(
        **result))
