"""Preregistered K4 centred-band continuation below 0.0285."""

from fractions import Fraction
import hashlib
from pathlib import Path

import certify_surface_remainder_k4_centered_band as base

ROOT = Path(__file__).resolve().parents[1]
UNIT = "k4_00280_00285"
base.BANDS = {UNIT: (Fraction(7, 250), Fraction(57, 2000), 9216)}


def run() -> str:
    lines = base.run(UNIT).splitlines()
    digest = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    index = next(i for i, line in enumerate(lines)
                 if line.startswith("DEPENDENCY "))
    lines.insert(index, f"DEPENDENCY scripts/{Path(__file__).name} {digest}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    print(run(), end="")
