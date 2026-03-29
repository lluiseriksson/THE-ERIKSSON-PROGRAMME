# STATE OF THE PROJECT (canonical 29 March 2026, post-audit v0.15.0)
<!-- CORRECTED 2026-03-29 v0.16.0: axiom count = 29 (was 26, prime-stripping regex bug fixed) -->

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
- **Total**: **0 sorry** across all Lean source (main pipeline + Experimental/)
- `scripts/check_consistency.py` exits 0 with no warnings
- Two former Experimental sorry converted to named axioms (closure C1, 2026-03-29):
  - `variance_decay_from_bridge_and_poincare_semigroup_gap` (VarianceDecayFromPoincare.lean:79)
  - `gronwall_variance_decay` (VarianceDecayFromPoincare.lean:133)

### Open axiom count (v0.15.0 — live census 2026-03-29)
- **29 axioms declaration names** across all of `YangMills/`
- Census scope: full `YangMills/` tree (corrected from v0.14.0 which missed `ClayCore/`)
- 3 duplicate pairs (same name in two files) — fix pending (run `elimination_structural_v1.py`)
- See `AXIOM_FRONTIER.md` v0.15.0 for complete verified list with file locations

```bash
# Authoritative axiom census command:
grep -rn "\baxiom\b" YangMills/ --include="*.lean" | grep -v "^\s*--"
# Or run:
python3 scripts/census_verify.py
```

### Previous version corrections
| v0.14.0 claim         | v0.15.0 correction                                     |
|-----------------------|--------------------------------------------------------|
| 20 mathematical gaps  | **26** — census scope was wrong (missed ClayCore/)     |
| 23 Lean decl names    | **26** — C3 not committed, no primed names             |
| C3 applied            | **C3 NOT COMMITTED** — duplicates still exist          |
| Scope: P8+LieSUN+Semig| **Scope: all of YangMills/**                           |

### Mathlib infrastructure gaps
The following Lean/Mathlib features are not yet available and block
mathematical progress (not just packaging):
- Multiscale RG flow theory in Mathlib
- KP cluster expansion in Lean
- Riemannian submersion theory in Mathlib
- DLR–LSI bridge in Mathlib
- C₀-semigroup theory (partially absent from Mathlib 4)
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

1. Run `python3 scripts/census_verify.py` to verify 26-axiom baseline.
2. Run `python3 elimination_structural_v1.py` to apply    axiom declarations from `DirichletConcrete.lean`).
3. Verify live census drops to 23 unique names (3 duplicates removed).
4. Then proceed to mathematical axiom elimination (Tier-B targets first):
   - `matExp_traceless_det_one` — candidate proof via `Matrix.det_exp`
   - `instIsTopologicalGroupSUN` — candidate via `Subgroup.toTopologicalGroup`
   - `instIsProbabilityMeasure_sunHaarProb` — candidate via compact Haar measure
   - `gronwall_variance_decay` — candidate via `Mathlib.Analysis.ODE.Gronwall`
5. Prove `sun_bakry_emery_cd` — first Clay-core axiom in Phase 2.

---

*Last updated: 2026-03-29*
*Version: v0.15.0 — live-census corrected; 26 unique names, full YangMills/ scope*
*Census tool: `scripts/census_verify.py` (word-boundary regex, block-comment stripping)*
*C3 status: NOT committed — run elimination_structural_v1.py to fix*
*0 sorry confirmed across all Lean source*
