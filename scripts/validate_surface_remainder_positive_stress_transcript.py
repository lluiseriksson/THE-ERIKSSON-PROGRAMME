"""Validate the terminal K2 positive stress-box transcript."""

import hashlib
from pathlib import Path
import re

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = ROOT/"scripts"/"surface_remainder_positive_stress_terminal_transcript.txt"
DEPENDENCY = re.compile(
    r"^dependency (\S+) sha256 ([0-9a-f]{64}) sha256_lf ([0-9a-f]{64})$")


def digest(path: Path, lf: bool = False) -> str:
    data = path.read_bytes()
    if lf:
        data = data.replace(b"\r\n", b"\n")
    return hashlib.sha256(data).hexdigest()


def main() -> int:
    text = TRANSCRIPT.read_text(encoding="utf-8")
    lines = text.splitlines()
    assert lines[0] == "K2 POSITIVE STRESS TERMINAL"
    assert "git_head 810a140d0724118f2884213db002026962bebdb4" in lines
    dependencies = [DEPENDENCY.fullmatch(line) for line in lines]
    dependencies = [match for match in dependencies if match]
    assert len(dependencies) == 10
    for match in dependencies:
        path = ROOT/match.group(1)
        assert digest(path) == match.group(2)
        assert digest(path, lf=True) == match.group(3)
    assert any(line.startswith("center cells 1024 ") for line in lines)
    assert any(line.startswith("t_box cells 64 ") for line in lines)
    assert any(line.startswith("delta_box cells 64 ") for line in lines)
    kd_line = next(line for line in lines if line.startswith("KD_lower "))
    kd = arb(kd_line.split("KD_lower ", 1)[1].split(" moment_abs ", 1)[0])
    assert kd > 0
    margin_line = next(line for line in lines if line.startswith("total "))
    margin = arb(margin_line.split(" margin ", 1)[1])
    assert margin > 0
    assert "K2 POSITIVE STRESS TERMINAL PASS" in lines
    assert lines[-1] == "SCOPE one born stress box only; G2 remains open"
    print("K2 POSITIVE STRESS TRANSCRIPT VALIDATED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
