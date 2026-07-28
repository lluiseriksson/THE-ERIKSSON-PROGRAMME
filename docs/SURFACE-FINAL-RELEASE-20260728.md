# Surface Theorem final release record

Date: 2026-07-28

## Claim

For every `beta > 0` and `0 < t < pi`, the denominator `F_B(t)` is
positive and the bridge ratio `E(t)=F_A(t)/(2F_B(t))` is strictly decreasing.
Equivalently, with the manuscript normalization,
`W=4 F_B^2 E' < 0`.

## Frozen evidence

- Evidence commit:
  `7ac09d96024fd7426a9e0f65bfdb598e636ddc9d`.
- Finite high-coupling cover:
  `20 <= beta <= 1000/9`, all `0 < t < pi`.
- High-beta half-line:
  `beta >= 1000/9`, partitioned by `lambda=beta(pi-t)` into
  `[0,3/2]`, `[3/2,2]`, `[2,3]`, and `[3,infinity)`.
- All shared endpoints and compact/edge interfaces are checked by exact
  rational-domain auditors.
- The finite campaign contains 450 ownership rows.  Its frozen aggregate is
  `f3f76e1d65a9ef825ed78d5cad98ae3ec1a32f3d00068ebad207dfde3fe5ab11`.

The historical partition helper whose recorded hash begins `3abc` is not
available byte-for-byte.  Its mathematical output is independently
reconstructed from all 912 certified intervals and 4,636 production/replay
rows.  This limitation is recorded rather than silently replacing provenance.

## Reproduction

From the repository root:

```text
python scripts/audit_surface_terminal_prerequisites.py
python scripts/audit_surface_g2_terminal_cover.py
python scripts/audit_surface_optional_hcube_removed.py
python scripts/audit_surface_final_seal.py
```

The final seal additionally checks the closure-board states, unresolved
manuscript markers, internal references, bibliography keys, compiled PDF, and
the TeX/PDF hashes in `SURFACE-FINAL-BUILD-20260728.json`.  The binary PDF is
hashed byte-for-byte; the UTF-8 TeX hash is explicitly normalized to LF so it
is stable across Windows and clean Git checkouts.

## Scope

This release concerns the explicit two-dimensional Wilson-action
surface/Bessel theorem stated in the paper.  It is not a proof of the
four-dimensional continuum Yang--Mills mass gap.
