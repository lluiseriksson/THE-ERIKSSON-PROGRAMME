#!/usr/bin/env python3
"""Fail if C1's KP radius drifts from the checked correlator theorem."""

from __future__ import annotations

import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
C1 = ROOT / "YangMills/Continuum/TightnessScaleNoGo.lean"
PRODUCER = ROOT / "YangMills/L1_GibbsMeasure/TwoPlaquetteCorrelator.lean"


def extract(pattern: str, text: str, label: str) -> str:
    match = re.search(pattern, text, flags=re.DOTALL)
    if match is None:
        raise SystemExit(f"CONTINUUM-C1 CANARY FAIL: cannot extract {label}")
    return match.group("body")


def canonical(body: str) -> str:
    body = body.replace("N_c", "Nc")
    body = body.replace("Real.exp (t + ε + 1)", "Real.exp (1 + 1 + 1)")
    return re.sub(r"\s+", "", body)


def bodies(producer_text: str) -> tuple[str, str]:
    c1 = extract(
        r"def KPRadiusAtUnit\b.*?: Prop :=(?P<body>.*?)\n\n/--",
        C1.read_text(encoding="utf-8"),
        "KPRadiusAtUnit",
    )
    checked = extract(
        r"theorem sun_two_plaquette_correlator_bound\b.*?"
        r"\(hr\s*:(?P<body>.*?)\)\s*\(hsmall\s*:",
        producer_text,
        "sun_two_plaquette_correlator_bound.hr",
    )
    return canonical(c1), canonical(checked)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    producer = PRODUCER.read_text(encoding="utf-8")
    c1, checked = bodies(producer)
    if c1 != checked:
        raise SystemExit("CONTINUUM-C1 CANARY FAIL: KP radius drift detected")
    if args.self_test:
        start = producer.index("theorem sun_two_plaquette_correlator_bound")
        mutated = producer[:start] + producer[start:].replace(
            "Real.exp (t + ε + 1)", "Real.exp (t + ε + 2)", 1
        )
        if bodies(mutated)[0] == bodies(mutated)[1]:
            raise SystemExit("CONTINUUM-C1 CANARY FAIL: mutation went undetected")
    suffix = " + mutation self-test" if args.self_test else ""
    print(f"CONTINUUM-C1 window canary{suffix}: PASS")


if __name__ == "__main__":
    main()
