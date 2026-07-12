"""Validate the exact fourth-head symbolic transcript and its executed blob."""

import hashlib
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = ROOT/"scripts"/"surface_remainder_delta0_fourth_coefficient_transcript.txt"
EXPECTED = {
    "script": "scripts/surface_remainder_delta0_fourth_coefficient.py",
    "script_sha256": "aba6b6e3cc85b3a21672ee68981dd1e1db32e755fca33e5c35398fd0739ddd6d",
    "git_head": "9999a0f783e8c7d62934b2888697c091361824f8",
    "python": "3.12.6",
    "sympy": "1.14.0",
}
FINAL = "TARGET MATCH: fourth coefficient r4(c)"


def validate(path=TRANSCRIPT):
    raw = Path(path).read_bytes()
    lines = raw.decode("utf-8").splitlines()
    if not lines or lines[-1] != FINAL:
        raise AssertionError("missing exact fourth-head terminal match")
    provenance = {}
    for line in lines:
        if line.startswith("PROVENANCE "):
            key, value = line[len("PROVENANCE "):].split("=", 1)
            provenance[key] = value
    if provenance != EXPECTED:
        raise AssertionError("fourth-head provenance mismatch")
    required = (
        "Y delta coefficient 0 = (2*c - 1)*(2*c + 1)/(8*c**3)",
        "Y delta coefficient 1 = -(8*c**4 - 15*c**2 + 4)/(32*c**6)",
        "Y delta coefficient 2 = -(12*c**6 + 485*c**4 - 796*c**2 + 224)/(1024*c**9)",
        "Y delta coefficient 3 = (28*c**8 + 41*c**6 - 1464*c**4 + 1856*c**2 - 500)/(1024*c**12)",
    )
    if tuple(lines[5:9]) != required:
        raise AssertionError("exact coefficient block mismatch")
    worktree = (ROOT/provenance["script"]).read_bytes()
    if hashlib.sha256(worktree).hexdigest() != provenance["script_sha256"]:
        raise AssertionError("fourth-head worktree hash mismatch")
    blob = subprocess.check_output(
        ["git", "show", provenance["git_head"]+":"+provenance["script"]],
        cwd=ROOT)
    if hashlib.sha256(blob).hexdigest() != provenance["script_sha256"]:
        raise AssertionError("fourth-head executed commit blob mismatch")
    canonical_lf = raw.replace(b"\r\n", b"\n")
    return {
        "transcript_sha256": hashlib.sha256(raw).hexdigest(),
        "transcript_sha256_lf": hashlib.sha256(canonical_lf).hexdigest(),
    }


if __name__ == "__main__":
    result = validate()
    print("fourth-head transcript OK: raw_sha256="
          +result["transcript_sha256"]+" lf_sha256="
          +result["transcript_sha256_lf"])
