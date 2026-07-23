"""Independent beta-union audit for paired finite-beta candidate transcripts.

The repository contains several frozen transcript formats.  This checker
normalizes their beta interval headers, requires exact production/replay byte
equality, and reports connected components.  It deliberately never promotes
G2, H_tail, or G6.
"""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MAX_BETA = Fraction(1000, 9)


def parse_fraction(value: str) -> Fraction:
    return Fraction(value.replace("p", "."))


def intervals(text: str) -> list[tuple[Fraction, Fraction]]:
    out: list[tuple[Fraction, Fraction]] = []
    for lo, hi in re.findall(r"^beta_domain (\S+) (\S+)$", text, re.M):
        out.append((parse_fraction(lo), parse_fraction(hi)))
    for lo, hi in re.findall(r"^beta-box \[([0-9.]+),\s*([0-9.]+)\]:", text, re.M):
        out.append((parse_fraction(lo), parse_fraction(hi)))
    for lo, hi in re.findall(r"^beta_unit \S+ lo (\S+) hi (\S+)", text, re.M):
        out.append((parse_fraction(lo), parse_fraction(hi)))
    for lo, hi in re.findall(r"^CONFIG unit \S+ beta (\S+) (\S+)", text, re.M):
        out.append((parse_fraction(lo), parse_fraction(hi)))
    for lo, hi in re.findall(r"^config beta_lo (\S+) beta_hi (\S+)", text, re.M):
        out.append((parse_fraction(lo), parse_fraction(hi)))
    return out


def main() -> int:
    found: list[tuple[Fraction, Fraction, str]] = []
    for path in sorted((ROOT / "scripts").glob("surface_scaled_bulk*.txt")):
        if path.name.endswith(("_rerun.txt", ".failed.txt")):
            continue
        replay = path.with_name(path.stem + "_rerun.txt")
        if not replay.is_file() or replay.read_bytes() != path.read_bytes():
            continue
        text = path.read_text(encoding="utf-8").replace("\r\n", "\n")
        for lo, hi in intervals(text):
            if Fraction(20) <= lo < hi <= MAX_BETA:
                found.append((lo, hi, path.name))

    assert found, "no paired finite-beta candidate transcript intervals found"
    found.sort()
    components: list[list[Fraction]] = []
    for lo, hi, _ in found:
        if not components or lo > components[-1][1]:
            components.append([lo, hi])
        else:
            components[-1][1] = max(components[-1][1], hi)

    print("SCALED-BULK CANDIDATE BETA UNION AUDIT")
    print("PAIRED_INTERVALS", len(found))
    for lo, hi in components:
        print("COMPONENT", lo, hi)
    for left, right in zip(components, components[1:]):
        print("GAP", left[1], right[0])
    print("REPLAY BYTE EQUALITY PASS")
    print("CANDIDATE ONLY; NO H_TAIL/G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
