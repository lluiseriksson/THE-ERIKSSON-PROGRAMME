"""Compare fresh compact-G5 replay records with production records."""

import re

import certify_right_edge_beta_taylor_cached_extension as cert
import run_right_edge_beta_taylor_cached_extension_units as launcher
import run_right_edge_beta_taylor_cached_extension_independent_rerun as replay


def semantic_lines(text):
    lines = text.splitlines()
    return [line for line in lines
            if line.startswith("beta-box ") or line.startswith("CERTIFIED RIGHT-EDGE COMPACT EXTENSION UNIT ")]


def validate():
    for unit in cert.SEGMENTS:
        production = launcher.output_path(unit).read_text(encoding="utf-8")
        rerun = replay.replay_path(unit).read_text(encoding="utf-8")
        assert semantic_lines(production) == semantic_lines(rerun), unit
        assert "FAIL" not in rerun
    print("RIGHT-EDGE COMPACT EXTENSION REPLAY PASS: four units exact")


if __name__ == "__main__":
    validate()
