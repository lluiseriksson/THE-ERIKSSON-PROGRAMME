"""Deterministic candidate transcript for the order-five companion budget."""

from __future__ import annotations

import argparse
import hashlib
import subprocess
from pathlib import Path

from flint import arb, ctx

from surface_bessel_integral_remainder import uniform_relative_constant
from surface_remainder_delta0_companion_error import MomentErrorCoefficients
from surface_remainder_companion_error_ordered import normalized_y_error_coefficient


ROOT = Path(__file__).resolve().parents[1]
DEPS = (
    "scripts/certify_surface_h_tail_companion_order5.py",
    "scripts/surface_remainder_companion_error_ordered.py",
    "scripts/surface_bessel_integral_remainder.py",
    "scripts/surface_remainder_delta0_companion_error.py",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_head() -> str:
    result = subprocess.run(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "rev-parse", "HEAD"],
        cwd=ROOT, text=True, capture_output=True, check=True,
    )
    return result.stdout.strip()


def theta3_at_one():
    c = arb(1)
    t = (4*c**2-1)/(8*c**3)
    r3 = (-12*c**6-485*c**4+796*c**2-224)/(1024*c**9)
    return arb(r3.abs_upper()) + arb("1.10")*t/c**2 + arb("0.5")/c**3 + arb("0.05")


def moment_errors(order: int) -> MomentErrorCoefficients:
    cmin = arb(2).sqrt()/2
    u = arb("0.6").sin()**2
    sinc = arb("0.6").sin()/arb("0.6")
    rate = 2*cmin*(1-u)*sinc**2/4
    root_min = (1-2*u).sqrt()
    h_coefficient = 1/(4*cmin*root_min)
    common = 1/(2*arb.pi()).sqrt()
    kernel_base = (2*common/(4*cmin)**(arb(3)/2)
                   *root_min**(-arb(3)/2))
    h_base = (common/(4*cmin)**(arb(5)/2)
              *root_min**(-arb(5)/2))
    ca = uniform_relative_constant("A", order, 20)
    cb = uniform_relative_constant("B", order, 20)
    quadrant_mass = arb.pi()/(4*rate)
    quadrant_sigma2 = arb.pi()/(8*rate**2)
    factor = arb(4)*h_coefficient**(order+1)
    return MomentErrorCoefficients(
        factor*kernel_base*ca*2*quadrant_mass,
        factor*kernel_base*ca*3*quadrant_sigma2,
        factor*h_base*cb*4*quadrant_mass,
        factor*h_base*cb*6*quadrant_sigma2,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    ctx.prec = 180
    theta = theta3_at_one()
    beta1 = arb(1000)/9
    budget = beta1*theta
    delta_ref = 1/beta1
    errors = moment_errors(5)
    coefficient = normalized_y_error_coefficient(
        delta_ref, arb(2), arb(10), order=5)
    equivalent = coefficient*delta_ref
    ratio = equivalent/budget
    lines = [
        "H_TAIL COMPANION ORDER5 TRANSCRIPT",
        f"PROVENANCE git_head {git_head()}",
        "PROVENANCE python 3.12.6",
        "PROVENANCE python_flint 0.9.0",
        "PROVENANCE arb_bits 180",
        "CONFIG beta1 1000/9 delta_ref 9/1000 order 5 kd_lower 2 moment_abs_upper 10",
    ]
    for relative in DEPS:
        lines.append(f"DEPENDENCY {relative} {digest(ROOT / relative)}")
    lines.extend([
        f"THETA3_C1 {theta.str(30)}",
        f"BUDGET_BETA1_THETA3 {budget.str(30)}",
    ])
    for name, value in errors.__dict__.items():
        lines.append(f"MOMENT_ERROR {name} {value.str(30)}")
    lines.extend([
        f"ORDER5_Y_COEFFICIENT {coefficient.str(30)}",
        f"ORDER5_EQUIVALENT_DELTA4_COEFFICIENT {equivalent.str(30)}",
        f"ORDER5_OVER_BUDGET {ratio.str(30)}",
        "ORDER5_COMPANION_ROUTE_PASSES_BUDGET_AUDIT",
        "SCOPE candidate analytic input only; outer-tail, joint carrier, weighted S1'''/S2''' and global H_tail relay remain open",
        "H_TAIL COMPANION ORDER5 PASS",
    ])
    output = (ROOT / args.output).resolve()
    output.relative_to(ROOT)
    output.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    print("ORDER5 COMPANION TRANSCRIPT PASS", output.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
