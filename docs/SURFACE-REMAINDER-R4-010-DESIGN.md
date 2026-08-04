# Tenth K2 birth: isolated design probe

**Date:** 2026-07-15  
**State:** `DESIGN_ONLY`; `NO_PROMOTION`

This note records an exploratory three-witness probe for the next positive
delta birth, `[9/1000,1/100]`.  It is deliberately not a preregistration: the
probe was started only after the current tree and the independent audit had
been read.  Its output cannot become production evidence without a fresh
frozen contract and a new provenance-bearing run.

The geometry is copied from the successful ninth-birth hybrid pattern:

- exact-r4 regular coverage is assigned to `0 <= t <= 313/100`;
- the complementary moving wedge is assigned to G5;
- the existing 158-unit born-`t` map and grids `(384,192,384)` are retained;
- the regular core is split at `0,1/200,3/500,7/1000,1/125,9/1000,1/100`;
- the outer-domain helper is byte-separated as `v7` and carries the exact cap
  `delta_max = 1/100`.

The executable files are
`scripts/surface_remainder_delta0_r4_extension_010_hybrid_contract.py`,
`scripts/surface_remainder_delta0_r4_extension_010_cover.py`, and
`scripts/surface_remainder_delta0_outer_domain_v7.py`.  The contract tests
check adjacency, wedge ownership, and the exact tenth-birth endpoint.

The only admissible interpretation of a green probe is feasibility of this
architecture at three selected `t` boxes.  Exhaustive 158-unit production,
hash manifests, an order-free union validator, and an independent rerun would
still be required to discharge the regular part of the tenth birth.  The G5
wedge and the later births remain untouched.

## Probe outcome (2026-07-15)

The first registered witness was run with outward Arb arithmetic before any
exhaustive cover was attempted:

```text
index 0, grid 384, band radius 59/5,
margin_lower -328.0599770883987779601628520648909
```

This is a strict design failure.  The three-witness probe was stopped at the
first failed witness, as required by the failure rule; no production unit,
transcript, or theorem claim was created.  The tenth-birth v7 route is
therefore rejected in its current form and the existing ninth-birth boundary
remains the authoritative regular endpoint.
