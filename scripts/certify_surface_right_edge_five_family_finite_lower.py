"""Authoritative wrapper for the finite five-family bridge ``25<=beta<=30``."""

import certify_surface_right_edge_five_family_finite as base
import surface_right_edge_five_family_finite_lower_cover_design as cover


DEPENDENCIES = (
    "scripts/certify_surface_right_edge_five_family_finite_lower.py",
    "scripts/certify_surface_right_edge_five_family_finite.py",
    *cover.DEPENDENCIES,
)

ROOT = base.ROOT
UNITS = base.UNITS
unit_slug = base.unit_slug
unit_map = base.unit_map
current_head = base.current_head


def main():
    return base.main(cover, DEPENDENCIES)


if __name__ == "__main__":
    raise SystemExit(main())
