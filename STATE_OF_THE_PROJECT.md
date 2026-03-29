# STATE OF THE PROJECT (canonical  29 March 2026)

## Final objective
Close the complete critical chain L0–L8 to obtain a `theorem UnconditionalMassGap : ...` with no unregistered external axioms.

## Actual status (no marketing)
- No node L0–L8 is FORMALIZED.
- All current nodes: OPEN or BLACKBOX (registered).
- Previous repos: audit scaffolds (confirmed by browsing Github).
- Required Mathlib infrastructure: still non-existent for multiscale RG, KP cluster expansion, Riemannian submersions, DLR–LSI.
- Open axioms: 24 active `axiom` declarations in the codebase (all registered in AXIOM_FRONTIER.md).

## Current critical path
L0 → L3.4 (KP criterion) → L5.2 (multiscale uniformity) → L8.3 (spectral gap)

## Permitted black boxes (maximum 5, all registered)
- KP86 (abstract)
- OS75/OS78
- Balaban CMP 1984–89 (29 lemmas)

## Next minimal action
Prove `sun_bakry_emery_cd` (BalabanToLSI.lean, line 97) — first Clay-Core axiom in Phase 2.

Last updated: 29/03/2026
