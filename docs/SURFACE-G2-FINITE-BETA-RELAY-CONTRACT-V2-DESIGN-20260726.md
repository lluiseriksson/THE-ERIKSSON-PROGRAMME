# Design amendment: direct finite-beta sign relay (2026-07-26)

This is a design document, not a terminal verdict.  It does not change the
current `DO_NOT_SUBMIT`, `G2=BLOCKED`, or `G6=BLOCKED` states.

## Proposed compact route

On the compact finite-beta lane, the required proposition is the following:

> For every `beta in [20,1000/9]` and
> `t in [3/5, pi-(3/2)/beta]`, the certified scaled quantity satisfies
> `W^J(beta,t)<0` on an exhaustive rational box cover with exact adjacency,
> outward rounding, and independent production/replay equality.

The executable algebra identity already checked by
`scripts/verify_surface_direct_sign_relay.py` is

```text
W^J = exp(-8 beta) W,       W = 4 F_B^2 E'.
```

Together with the independent theorem `F_B>0`, this proposition implies
`E'<0` on the compact lane.  It does **not** imply the extraction hypothesis
`(H_tail)` and it does not affect the noncompact `beta>=1000/9` lane.

## Required changes before any promotion

1. Replace the current audit contract by a new preregistered contract; do
   not edit the 2026-07-21 contract or relabel its verdict.
2. Require an explicit manifest field `admissible_lane: true` and verify the
   preregistration hash in the executable audit.
3. Require the strong moving seam for each beta box, not only the conservative
   endpoint based on `beta_lo`.
4. Derive relay state from a committed algebra/contract artifact rather than
   a hard-coded string.
5. Keep the low-`t` splice, the right collar, and the large-beta
   `(H_tail)`/K2 lane as separate gates.  Compact sign coverage alone cannot
   seal the theorem.

Until all five conditions and the complete beta union pass, all rescue
transcripts remain candidate evidence only.
