# STATE OF THE PROJECT (canonical 29 March 2026, post-audit D1–D8)

## Terminology Precision

Two senses of "formalized" are used in this project. They must not be confused:

- **FORMALIZED_KERNEL** (registry status): The Lean code compiles and type-checks
  with 0 errors and 0 `sorry`. The theorem may still depend on named `axiom`
  declarations or `open_hypotheses` listed in `registry/nodes.yaml`. This is
  the status of all nodes L0.1–L8.1 and P2.1–P2.5 in the current registry.

- **FORMALIZED** (mathematical sense): Proved unconditionally — no open axioms,
  no open hypotheses, no external black boxes. **No node currently achieves
  this status.**

The previous version of this file said "No node L0–L8 is FORMALIZED" without
defining the term. That sentence is true in the mathematical sense above, but
it contradicted `registry/nodes.yaml` which uses `FORMALIZED_KERNEL` — a
weaker, purely syntactic status — for every node. Both facts are now stated
explicitly to end the contradiction.

---

## Final Objective

Close the complete critical chain L0–L8 to obtain a `theorem UnconditionalMassGap`
with no unregistered external axioms, no `sorry`, and no `open_hypotheses`.

---

## Actual Status (no marketing)

### Registry status (syntactic — Lean compiles)
All nodes L0.1–L8.1 and P2.1–P2.5: **FORMALIZED_KERNEL**
Meaning: Lean code builds, 0 errors, 0 sorry.
Does NOT mean: unconditional mathematical proof.

### Mathematical status (semantic — what is actually proved)
- No node is proved unconditionally.
- Every terminal theorem (L8.1 `ClayYangMillsTheorem`, P2.5) is conditional
  on `open_hypotheses` and/or named `axiom` declarations.
- The genuine Clay problem content is isolated in a small number of explicit
  named `axiom` declarations; see `AXIOM_FRONTIER.md` for the complete list.

### sorry declarations
- **Main pipeline** (YangMills/L*, YangMills/P*, Lean/): **0 sorry** — enforced by CI
- **Experimental/** (scratch files): **2 sorry** — reported as warnings, non-blocking
  - `Experimental/Semigroup/VarianceDecayFromPoincare.lean:92` (documented blocker)
  - `Experimental/Semigroup/VarianceDecayFromPoincare.lean:117` (documented blocker)
  - These must be converted to named `axiom` declarations before any promotion to main pipeline

### Open axiom count
- Census run 2026-03-29: **18 unique axiom names** across
  `YangMills/P8_PhysicalGap/` (20 files) and `YangMills/Experimental/LieSUN/` (8 files).
- Previous version claimed 10 (two of those were actually proved theorems:
  `sun_gibbs_dlr_lsi` and `clustering_to_spectralGap`).
- An even earlier version claimed 24 — that figure was unverified.
- See `AXIOM_FRONTIER.md` for the complete verified list with file locations.
- `YangMills/L0`–`L8` open hypotheses are tracked as `open_hypotheses` in
  `registry/nodes.yaml` rather than as named `axiom` declarations.

```bash
# Authoritative axiom census command (catches indented AND attributed axioms):
grep -rn "^\s*axiom " YangMills/ --include="*.lean" | grep -v "^\s*--"
# Also run broad scan for @[instance] axiom and similar:
grep -rn "\baxiom\b" YangMills/ --include="*.lean" | grep -v "^\s*--"
```

### Mathlib infrastructure gaps
The following Lean/Mathlib features are not yet available and block
mathematical progress (not just packaging):
- Multiscale RG flow theory in Mathlib
- KP cluster expansion in Lean
- Riemannian submersion theory in Mathlib
- DLR–LSI bridge in Mathlib
These are tracked as Mathlib-gap axioms in `AXIOM_FRONTIER.md`.

---

## Current Critical Path

L0 → L3.4 (KP criterion) → L5.2 (multiscale uniformity) → L8.3 (spectral gap)

Nodes L3.4, L3.5, L7.3, L8.3, L8.4 are on the critical path but currently
have status OPEN (no Lean file). They were added as stubs to `registry/nodes.yaml`
on 2026-03-29 to resolve a registry consistency defect.

---

## Permitted Black Boxes (maximum 5, all registered)

- KP86 (abstract)
- OS75/OS78
- Balaban CMP 1984–89 (29 lemmas)

---

## Next Minimal Action

Prove `sun_bakry_emery_cd` (`BalabanToLSI.lean`, line 97) — first Clay-Core
axiom in Phase 2.

Before resuming Lean work:
1. Run the axiom census command above.
2. Reconcile the count with `AXIOM_FRONTIER.md`.
3. Update both files with the verified number.

---

*Last updated: 2026-03-29*
*Status-doc consistency: verified against `registry/nodes.yaml` (2026-03-29)*
