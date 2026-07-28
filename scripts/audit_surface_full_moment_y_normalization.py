"""Static contract for every live full-moment Y normalization helper.

The symbolic coefficient derivations intentionally use dimensionless
moments and retain ``1/(2*c)``.  The files listed here instead consume full
moments, which already include ``H0/K0=1/(8*c)`` and therefore must use
``Y=4*B/(delta*KD^2)``.
"""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "scripts/surface_remainder_delta0_series_design.py": (
        'return 4*quotient/series["kd"]**2',
    ),
    "scripts/surface_remainder_delta0_r4_extension_probe.py": (
        'return 4*quotient/moments["kd"]**2',
    ),
    "scripts/surface_remainder_delta0_r6_exact_three_witness.py": (
        'return 4*quotient/moments["kd"]**2',
    ),
    "scripts/surface_remainder_delta0_r6_extension_010_cover.py": (
        'return 4*quotient/moments["kd"]**2',
    ),
    "scripts/probe_surface_k2_centered_direct_eval.py": (
        'y = 4*(bilinear/d)/moments["kd"]**2',
    ),
    "scripts/probe_surface_k2_centered_grid_scan.py": (
        'y = 4*(bilinear/d)/moments["kd"]**2',
    ),
    "scripts/probe_surface_k2_centered_split_scan.py": (
        'y = 4*(bilinear/d)/moments["kd"]**2',
    ),
    "scripts/probe_surface_remainder_r6_exact_box_integral.py": (
        'y = 4 * quotient / moments["kd"]**2',
    ),
    "scripts/probe_surface_remainder_r6_nominal_tenth.py": (
        'return 4*quotient/moments["kd"]**2',
    ),
    "scripts/probe_surface_remainder_r6_grouped_determinant.py": (
        'y = 4*quotient/totals["kd"]**2',
    ),
    "scripts/probe_surface_remainder_signed_bilinear_series.py": (
        "d = [value/4 for value in safe_square_series(kd_series, prec)]",
    ),
    "scripts/k2_denominator_leading_term_smoke.py": (
        'denominator = moments["kd"]**2/4',
    ),
}

ERROR_HELPERS = {
    "scripts/surface_remainder_delta0_companion_error.py":
        "return 4 * (",
    "scripts/surface_remainder_companion_error_ordered.py":
        "return 4 * (",
    "scripts/surface_remainder_delta0_outer_domain_v2.py":
        "return 4 * (delta_b/actual_lower**2 + nominal_b*inverse)",
    "scripts/probe_surface_remainder_r6_companion_charge.py":
        "first = 4*A/actual**2",
}

LEGACY_TOKENS = (
    'quotient/(2*c*moments["kd"]**2)',
    'quotient/(2*(t/4).cos()*moments["kd"]**2)',
    '(bilinear/d)/(2*(t/4).cos()*moments["kd"]**2)',
)


def audit(root: Path = ROOT) -> list[str]:
    checked: list[str] = []
    for relative, required in REQUIRED.items():
        text = (root / relative).read_text(encoding="utf-8")
        for token in required:
            if token not in text:
                raise AssertionError(f"{relative}: missing {token!r}")
        for token in LEGACY_TOKENS:
            if token in text:
                raise AssertionError(
                    f"{relative}: legacy full-moment normalization {token!r}"
                )
        checked.append(relative)
    for relative, required in ERROR_HELPERS.items():
        text = (root / relative).read_text(encoding="utf-8")
        if required not in text:
            raise AssertionError(f"{relative}: missing {required!r}")
        if "/(2*cmin)" in text or "/ (2*cmin)" in text:
            raise AssertionError(
                f"{relative}: legacy full-moment error normalization"
            )
        checked.append(relative)
    return checked


def main() -> int:
    checked = audit()
    print(f"FULL_MOMENT_NORMALIZATION_FILES {len(checked)}")
    for relative in checked:
        print(f"FULL_MOMENT_NORMALIZATION_OK {relative}")
    print("SURFACE FULL-MOMENT Y NORMALIZATION AUDIT PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
