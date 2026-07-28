"""Audit a finite mean-value candidate cover using exact rational endpoints.

This is deliberately a candidate-only audit: it checks that manifested cells
form the declared closed rectangle and that each transcript/replay pair is
byte-identical, hash-consistent, and strictly negative.  It never promotes a
closure gate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]


def q(value: str) -> Fraction:
    return Fraction(value)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cell_bounds(cell: dict[str, object]) -> tuple[Fraction, Fraction, Fraction, Fraction]:
    beta = cell["beta_cell"]
    lam = cell["lambda_cell"]
    assert isinstance(beta, list) and isinstance(lam, list)
    return q(str(beta[0])), q(str(beta[1])), q(str(lam[0])), q(str(lam[1]))


def audit(manifest: dict[str, object]) -> None:
    assert manifest["status"] == "CELL_CERTIFIED_CANDIDATE"
    assert manifest["promotion"] == "NONE"
    cells = manifest["cells"]
    assert isinstance(cells, list) and cells
    domain = manifest["domain"]
    assert isinstance(domain, dict)
    dlo = tuple(q(str(x)) for x in domain["beta"])
    llo = tuple(q(str(x)) for x in domain["lambda"])
    assert len(dlo) == 2 and len(llo) == 2 and dlo[0] < dlo[1] and llo[0] < llo[1]

    intervals: list[tuple[Fraction, Fraction, Fraction, Fraction]] = []
    configs: set[tuple[object, ...]] = set()
    for cell in cells:
        assert isinstance(cell, dict)
        blo, bhi, llo_cell, lhi_cell = cell_bounds(cell)
        assert dlo[0] <= blo < bhi <= dlo[1]
        assert llo[0] <= llo_cell < lhi_cell <= llo[1]
        intervals.append((blo, bhi, llo_cell, lhi_cell))
        configs.add((cell["modes"], cell["beta_order"], cell["lambda_order"], cell["arb_bits"]))

        transcript = ROOT / str(cell["transcript"])
        replay = ROOT / str(cell["replay"])
        assert transcript.exists() and replay.exists()
        assert transcript.read_bytes() == replay.read_bytes()
        digest = sha256(transcript)
        assert digest == cell["transcript_sha256"] == cell["replay_sha256"]
        lines = transcript.read_text(encoding="utf-8").splitlines()
        assert lines[0] == "SCALED PAIR MEAN-VALUE CELL CERTIFICATE"
        assert "SCOPE one beta/lambda cell only; no G2/G6 promotion" in lines
        total = arb(next(line.split(" ", 1)[1] for line in lines if line.startswith("total_upper ")))
        assert total < 0
        for line in lines:
            if line.startswith("dependency "):
                fields = line.split()
                assert sha256(ROOT / fields[1]) == fields[3]
        assert lines[-2] == "SCALED PAIR MEAN-VALUE CELL PASS"

    # A finite cover must be a Cartesian tiling: no gaps, no overlaps, and
    # every beta/lambda boundary is represented by at least one cell edge.
    beta_edges = sorted({x for row in intervals for x in row[:2]})
    lam_edges = sorted({x for row in intervals for x in row[2:]})
    assert beta_edges[0] == dlo[0] and beta_edges[-1] == dlo[1]
    assert lam_edges[0] == llo[0] and lam_edges[-1] == llo[1]
    for left, right in zip(beta_edges, beta_edges[1:]):
        for low, high in zip(lam_edges, lam_edges[1:]):
            owners = sum(blo <= left and right <= bhi and lo <= low and high <= hi
                         for blo, bhi, lo, hi in intervals)
            assert owners == 1, (left, right, low, high, owners)
    assert len(configs) == 1, configs


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--precision", type=int, default=500)
    args = parser.parse_args()
    ctx.prec = args.precision
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    audit(manifest)
    print("SCALED PAIR MEAN-VALUE COVER AUDIT PASS")
    print("cells", len(manifest["cells"]))
    print("SCOPE candidate cover only; no G2/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
