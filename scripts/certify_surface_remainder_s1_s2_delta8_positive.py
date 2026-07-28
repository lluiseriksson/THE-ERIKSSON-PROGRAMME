"""One preregistered positive-delta S1 or S2 production unit."""

from __future__ import annotations

import argparse
import hashlib
import platform
import subprocess
import sys
from fractions import Fraction
from pathlib import Path
from time import perf_counter

import flint
from flint import arb, ctx

import surface_remainder_s1_delta8_exact as s1
import surface_remainder_s2_delta8_exact as s2
from surface_remainder_s2_direct_judge import closed_forms


ROOT = Path(__file__).resolve().parents[1]
PRECISION = 180
WORKERS = 4
MESH_POWER = Fraction(3, 2)
T = Fraction(29, 10)
DELTA_FINAL = Fraction(1, 15)

UNITS = tuple(
    [(Fraction(k, 2000), Fraction(k + 1, 2000)) for k in range(61, 133)]
    + [(Fraction(133, 2000), DELTA_FINAL)]
)

CALIBRATION_KNOTS = (
    (
        Fraction(31, 1000),
        (
            "-0.02558658084315849853267816364585336264690",
            "-0.8217654614598047044505896807742706192525",
            "0.1166008547158716583502361174913758031124",
        ),
    ),
    (
        Fraction(1, 25),
        (
            "-0.03297281690292861396976596958184651862485",
            "-0.8195768679837442914121064889386895127998",
            "0.1318725073690613039813660263094183244174",
        ),
    ),
    (
        Fraction(1, 20),
        (
            "-0.041153388497690248593365930",
            "-0.8162559803363880870511532",
            "0.2171657204568843395206",
        ),
    ),
    (
        DELTA_FINAL,
        (
            "-0.054668221249241399411735314",
            "-0.8033617852942335869159901",
            "0.6029338320739366303786",
        ),
    ),
)


def aq(value: Fraction) -> arb:
    return arb(value.numerator) / value.denominator


def unit_name(index: int) -> str:
    if not 0 <= index < len(UNITS):
        raise ValueError("positive campaign unit index is out of range")
    return f"u{index:03d}"


def calibration_at(center: Fraction) -> tuple[arb, arb, arb]:
    if center <= CALIBRATION_KNOTS[0][0]:
        return tuple(arb(value) for value in CALIBRATION_KNOTS[0][1])
    for (left, left_values), (right, right_values) in zip(
        CALIBRATION_KNOTS, CALIBRATION_KNOTS[1:]
    ):
        if center <= right:
            weight = aq((center - left) / (right - left))
            return tuple(
                arb(lo) + weight * (arb(hi) - arb(lo))
                for lo, hi in zip(left_values, right_values)
            )
    return tuple(arb(value) for value in CALIBRATION_KNOTS[-1][1])


def s2_fraction(value: arb, lo: arb, hi: arb) -> arb:
    delta_final = aq(DELTA_FINAL)
    weight = delta_final * (hi - lo) - (hi**2 - lo**2) / 2
    theta3 = closed_forms(aq(T))[3]
    return 15 * 2 * arb(value.abs_upper()) * weight / (theta3 * delta_final)


def repository_dependencies() -> tuple[Path, ...]:
    paths = {Path(__file__).resolve()}
    for module in tuple(sys.modules.values()):
        raw = getattr(module, "__file__", None)
        if not raw:
            continue
        path = Path(raw).resolve()
        try:
            path.relative_to(ROOT)
        except ValueError:
            continue
        if path.suffix == ".py":
            paths.add(path)
    return tuple(sorted(paths))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_head() -> str:
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
    ).strip()


def run(judge: str, index: int) -> str:
    ctx.prec = PRECISION
    name = unit_name(index)
    lo_fraction, hi_fraction = UNITS[index]
    lo, hi, t = aq(lo_fraction), aq(hi_fraction), aq(T)
    started = perf_counter()
    if judge == "s1":
        center_grid, remainder_grid = 16, 4
        enclosures, _, _ = s1.centered_half_second_enclosures(
            lo,
            hi,
            t,
            center_grid,
            remainder_grid,
            workers=WORKERS,
            center_mesh_power=MESH_POWER,
            remainder_mesh_power=MESH_POWER,
        )
        fractions = s1.single_box_fractions(enclosures, lo, hi)
        calibration = None
    elif judge == "s2":
        center_grid = 48 if lo_fraction < Fraction(79, 2000) else 32
        remainder_grid = 8
        center = (lo_fraction + hi_fraction) / 2
        calibration = calibration_at(center)
        enclosure, _, _ = s2.centered_half_second_enclosure(
            lo,
            hi,
            t,
            center_grid,
            remainder_grid,
            calibration,
            workers=WORKERS,
            center_mesh_power=MESH_POWER,
            remainder_mesh_power=MESH_POWER,
        )
        enclosures = {"Y_main": enclosure}
        fractions = {"Y_main": s2_fraction(enclosure, lo, hi)}
    else:
        raise ValueError("judge must be s1 or s2")

    finite = all(
        value.is_finite() and fractions[key].is_finite()
        for key, value in enclosures.items()
    )
    locally_necessary = finite and all(
        arb(fraction.upper()) < 1 for fraction in fractions.values()
    )
    elapsed = perf_counter() - started
    lines = [
        f"SURFACE {judge.upper()} DELTA-EIGHT POSITIVE UNIT",
        f"PROVENANCE git_head {git_head()}",
        f"PROVENANCE python {platform.python_version()}",
        f"PROVENANCE python_flint {flint.__version__}",
        f"PROVENANCE arb_bits {ctx.prec}",
        (
            f"CONFIG unit {name} index {index} delta {lo_fraction}:{hi_fraction} "
            f"t {T} center_grid {center_grid} remainder_grid {remainder_grid} "
            f"mesh_power {MESH_POWER} workers {WORKERS}"
        ),
    ]
    for dependency in repository_dependencies():
        lines.append(
            f"DEPENDENCY {dependency.relative_to(ROOT).as_posix()} "
            f"{sha256(dependency)}"
        )
    if calibration is not None:
        lines.append(
            "CALIBRATION " + " ".join(value.str(80) for value in calibration)
        )
    for key in enclosures:
        lines.append(f"HALF_SECOND {key} {enclosures[key].str(80)}")
        lines.append(f"FRACTION {key} {fractions[key].str(80)}")
    lines.extend(
        [
            f"ELAPSED_SECONDS {elapsed:.9f}",
            (
                f"SURFACE {judge.upper()} DELTA-EIGHT POSITIVE UNIT "
                + ("PASS" if locally_necessary else "FAIL")
            ),
            (
                "SCOPE one preregistered positive-delta stress unit only; "
                "no global S1'''/S2'''/K2/K4/G1/G2/G6/theorem promotion"
            ),
        ]
    )
    if not locally_necessary:
        raise RuntimeError("\n".join(lines))
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--judge", choices=("s1", "s2"), required=True)
    parser.add_argument("--unit", type=int, choices=range(len(UNITS)), required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        transcript = run(args.judge, args.unit)
    except Exception as exc:
        print(f"POSITIVE UNIT FAIL: {exc}", file=sys.stderr)
        return 1
    output = (ROOT / args.output).resolve()
    output.relative_to(ROOT)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(transcript, encoding="utf-8", newline="\n")
    print(
        f"{args.judge.upper()} POSITIVE UNIT PASS",
        unit_name(args.unit),
        output.relative_to(ROOT),
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
