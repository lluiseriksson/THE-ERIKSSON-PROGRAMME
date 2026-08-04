"""Validate the current single-cell pair mean-value candidate.

This validator is intentionally narrower than the finite-cover auditor: the
manifest owns one beta/lambda rectangle, not a tiling.  It checks provenance,
replay identity, dependency hashes, and a strict negative Arb upper endpoint,
but it never promotes G2 or G6.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def q(value: str) -> Fraction:
    return Fraction(value)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--precision", type=int, default=500)
    args = parser.parse_args()
    ctx.prec = args.precision
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))

    assert manifest["status"] == "CELL_CERTIFIED_CANDIDATE"
    assert manifest["promotion"] == "NONE"
    assert "no G2 or G6 promotion" in manifest["scope"]
    domain = manifest["domain"]
    cell = manifest["cell"]
    assert q(str(domain["beta"][0])) == q(str(cell["beta_cell"][0]))
    assert q(str(domain["beta"][1])) == q(str(cell["beta_cell"][1]))
    assert q(str(domain["lambda"][0])) == q(str(cell["lambda_cell"][0]))
    assert q(str(domain["lambda"][1])) == q(str(cell["lambda_cell"][1]))
    assert q(str(domain["beta"][0])) < q(str(domain["beta"][1]))
    assert q(str(domain["lambda"][0])) < q(str(domain["lambda"][1]))

    transcript = ROOT / cell["transcript"]
    replay = ROOT / cell["replay"]
    assert transcript.exists() and replay.exists()
    assert transcript.read_bytes() == replay.read_bytes()
    digest = sha256(transcript)
    assert digest == cell["transcript_sha256"] == cell["replay_sha256"]

    lines = transcript.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED PAIR MEAN-VALUE CELL CERTIFICATE"
    assert lines[-2] == "SCALED PAIR MEAN-VALUE CELL PASS"
    assert lines[-1] == "SCOPE one beta/lambda cell only; no G2/G6 promotion"
    total_line = next(line for line in lines if line.startswith("total_upper "))
    assert arb(total_line.split(" ", 1)[1]) < 0

    deps = [line.split() for line in lines if line.startswith("dependency ")]
    assert deps
    for fields in deps:
        assert fields[0] == "dependency" and fields[2] == "sha256"
        assert sha256(ROOT / fields[1]) == fields[3]

    print("CURRENT PAIR MEAN-VALUE CELL VALIDATION PASS")
    print("sha256", digest)
    print("total_upper", total_line.split(" ", 1)[1])
    print("dependencies", len(deps))
    print("SCOPE candidate cell only; no G2/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
