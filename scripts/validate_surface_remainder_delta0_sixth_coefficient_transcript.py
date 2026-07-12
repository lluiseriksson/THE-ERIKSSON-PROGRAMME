"""Validate the exact sixth-head symbolic transcript."""

import hashlib
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = ROOT/"scripts"/"surface_remainder_delta0_sixth_coefficient_transcript.txt"
SCRIPT = "scripts/surface_remainder_delta0_sixth_coefficient.py"
DEPENDENCY = "scripts/derive_surface_remainder_delta0_sixth_fast.py"
SCRIPT_SHA = "2fabb0e4e91349b14ee79f8d4be08213be534cad8667d132147b36097496ebad"
DEPENDENCY_SHA = "a00eb5f377eef4dba0efdcc81b5734e0b058fe04eafd7a6b32448776f38ca292"
HEAD = "d2416f03ce011bef2cb94ef08d5db7a1aee72fb9"
COEFFICIENT = ("Y delta coefficient 5 = (8148*c**12 + 17095*c**10 + "
               "10768*c**8 + 634576*c**6 - 2557408*c**4 + "
               "2283296*c**2 - 549376)/(131072*c**18)")


def validate(path=TRANSCRIPT):
    raw = Path(path).read_bytes()
    lines = raw.decode("utf-8").splitlines()
    expected = [
        "PROVENANCE script="+SCRIPT,
        "PROVENANCE script_sha256="+SCRIPT_SHA,
        "PROVENANCE dependency_sha256="+DEPENDENCY_SHA,
        "PROVENANCE git_head="+HEAD,
        "PROVENANCE python=3.12.6",
        "PROVENANCE sympy=1.14.0",
        COEFFICIENT,
        "TARGET MATCH: sixth coefficient r6(c)",
    ]
    if lines != expected:
        raise AssertionError("sixth-head provenance/coefficient mismatch")
    for rel, digest in ((SCRIPT, SCRIPT_SHA), (DEPENDENCY, DEPENDENCY_SHA)):
        if hashlib.sha256((ROOT/rel).read_bytes()).hexdigest() != digest:
            raise AssertionError("sixth-head worktree hash mismatch: "+rel)
        blob = subprocess.check_output(["git", "show", HEAD+":"+rel], cwd=ROOT)
        if hashlib.sha256(blob).hexdigest() != digest:
            raise AssertionError("sixth-head executed blob mismatch: "+rel)
    lf = raw.replace(b"\r\n", b"\n")
    return {"raw_sha256": hashlib.sha256(raw).hexdigest(),
            "lf_sha256": hashlib.sha256(lf).hexdigest()}


if __name__ == "__main__":
    result = validate()
    print("sixth-head transcript OK: raw={raw_sha256} lf={lf_sha256}".format(
        **result))
