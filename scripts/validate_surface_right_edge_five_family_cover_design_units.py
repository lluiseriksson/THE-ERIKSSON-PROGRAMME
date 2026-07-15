"""Validate the complete 15-unit, 600-cell G5 design cover."""

import hashlib
import re
from pathlib import Path

from flint import arb

import run_surface_right_edge_five_family_cover_design_units as launcher
import surface_right_edge_five_family_cover_design as cover


ROOT = Path(__file__).resolve().parents[1]
ROW = re.compile(
    r"^ROW delta_index (\d+) delta (\S+) lambda_index (\d+) "
    r"lambda (\S+) resolution (\w+) B0_lower (.*?) "
    r"P0_lower (.*?) H_lower (.*)$"
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate():
    expected_hashes = {
        relative: sha256(ROOT/relative) for relative in cover.DEPENDENCIES
    }
    cells = {}
    for unit in launcher.units():
        path = launcher.output_path(unit)
        lines = path.read_text(encoding="utf-8").splitlines()
        assert not any("COVER DESIGN FAIL" in line for line in lines)
        dependencies = {
            line.split()[1]: line.split()[2] for line in lines
            if line.startswith("DEPENDENCY ")
        }
        assert dependencies == expected_hashes
        configs = [line for line in lines if line.startswith("CONFIG ")]
        assert len(configs) == 1
        assert "delta_partition 0:1/125:1/1000" in configs[0]
        assert "lambda_partition 0:3/2:1/50" in configs[0]
        assert sum(line.startswith(launcher.terminal(unit))
                   for line in lines) == 1
        matches = [ROW.match(line) for line in lines if line.startswith("ROW ")]
        assert len(matches) == 8*(unit[1]-unit[0])
        assert all(match is not None for match in matches)
        for match in matches:
            di, delta, li, lam, resolution, b0, p0, h = match.groups()
            di, li = int(di), int(li)
            assert 0 <= di < 8 and unit[0] <= li < unit[1]
            assert delta == f"{di}/1000:{di+1}/1000"
            assert lam == f"{li}/50:{li+1}/50"
            assert resolution in {"coarse", "mixed"}
            assert arb(b0) > 0 and arb(p0) > 0 and arb(h) > 0
            assert (di, li) not in cells
            cells[di, li] = h
    assert set(cells) == {(di, li) for di in range(8) for li in range(75)}
    worst = min(cells, key=lambda key: float(arb(cells[key])))
    print("G5 DESIGN UNION PASS: 600/600 cells; worst", worst,
          "H_lower", cells[worst])
    return cells


if __name__ == "__main__":
    validate()
