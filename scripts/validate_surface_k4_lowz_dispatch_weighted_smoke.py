"""Validate the isolated low-z weighted K4 stress smoke and its replay."""

from __future__ import annotations

import hashlib
from pathlib import Path
import re

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
REQUIRED = {
    "muF_main", "nuD_main", "nuF_main", "MD_mirror", "MF_mirror",
    "MD2r_mirror", "MDFr_mirror",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(path: Path) -> tuple[set[str], dict[str, arb], dict[str, str]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    if lines[0] != "SURFACE K4 LOW-Z DISPATCH WEIGHTED SMOKE":
        raise AssertionError("wrong transcript header")
    if "CANDIDATE LOW-Z WEIGHTED SMOKE PASS" not in lines:
        raise AssertionError("candidate smoke did not pass")
    if "no global S1'''/S2''' or K4 promotion" not in lines[-1]:
        raise AssertionError("promotion scope was not quarantined")
    names: set[str] = set()
    fractions: dict[str, arb] = {}
    deps: dict[str, str] = {}
    for line in lines:
        if line.startswith("row "):
            match = re.match(r"row (\S+) .* fraction (.*)$", line)
            if not match:
                raise AssertionError(f"malformed row: {line}")
            name, value = match.groups()
            names.add(name)
            fractions[name] = arb(value)
        elif line.startswith("dependency "):
            _, relative, _, value = line.split()
            deps[relative] = value
    if names != REQUIRED:
        raise AssertionError(f"row set mismatch: {names}")
    if not all(bool(value < 1) for value in fractions.values()):
        raise AssertionError("absolute budget fraction is not strictly below 1")
    for relative, expected in deps.items():
        path_on_disk = ROOT / relative
        if digest(path_on_disk) != expected:
            raise AssertionError(f"dependency hash mismatch: {relative}")
    return names, fractions, deps


def main() -> int:
    production = ROOT / "scripts/surface_k4_lowz_dispatch_weighted_smoke_16384.txt"
    replay = ROOT / "scripts/surface_k4_lowz_dispatch_weighted_smoke_16384_rerun.txt"
    _, production_rows, _ = parse(production)
    _, replay_rows, _ = parse(replay)
    if production.read_bytes() != replay.read_bytes():
        raise AssertionError("production/replay transcript mismatch")
    if {name: value.str(100) for name, value in production_rows.items()} != {
        name: value.str(100) for name, value in replay_rows.items()
    }:
        raise AssertionError("production/replay parsed rows differ")
    print("LOW-Z WEIGHTED SMOKE VALIDATION PASS")
    print("rows", len(production_rows), "cells_per_lane", 16384)
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("CANDIDATE ONLY; NO GLOBAL S1'''/S2'''/K4/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
