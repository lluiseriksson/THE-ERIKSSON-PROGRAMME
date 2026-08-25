#!/usr/bin/env python3
"""Promote the minimal Eq. (3.37) complex-coordinate boundary.

This is a byte-preserving mechanical promotion of three PRE-VALIDATION
source/audit pairs.  It deliberately does not edit ``YangMillsCore.lean`` and
does not remove any PRE-VALIDATION marker.  Refuse to overwrite a destination
whose bytes differ from its draft, so reruns are idempotent but never silent.
"""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
STEMS = (
    "BalabanCMP99Eq337PhysicalRealCovariantDerivative",
    "BalabanCMP99Eq337PhysicalComplexCovariantDerivative",
    "BalabanCMP99Eq337PhysicalComplexPerturbedBackground",
)


def promote(source: Path, destination: Path) -> None:
    payload = source.read_bytes()
    if destination.exists():
        if destination.read_bytes() != payload:
            raise RuntimeError(f"PROMOTION_DESTINATION_DIFFERS={destination}")
        print(f"PROMOTION_ALREADY_IDENTICAL={destination.relative_to(ROOT)}")
        return
    destination.write_bytes(payload)
    print(f"PROMOTION_WRITTEN={destination.relative_to(ROOT)}")


def main() -> int:
    for stem in STEMS:
        promote(
            ROOT / "tmp" / f"{stem}.draft.lean",
            ROOT / "YangMills" / "RG" / f"{stem}.lean",
        )
        promote(
            ROOT / "tmp" / f"{stem}Audit.draft.lean",
            ROOT / "YangMills" / "RG" / f"{stem}Audit.lean",
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
