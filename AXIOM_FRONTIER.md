# AXIOM_FRONTIER.md v0.9.40

## AXIOM 6 — Haar-LSI Package Frontier Closed (2026-03-28)

`BalabanRGPackageWitness.lean` and `HaarLSITransferWitness.lean` are now
in the repository. Together they close the entire `HaarLSIFrontierPackage`
unconditionally at the *packaging layer*.

What closed:

| Target | Theorem | Status |
|---|---|---|
| `BalabanRGUniformLSILiveTarget d N_c` | `balabanRGUniformLSILiveTarget_closed` | ✓ closed |
| `SpecialUnitaryDirectUniformLSITheoremTarget d N_c` | `specialUnitaryDirectUniformLSITheoremTarget_closed` | ✓ closed |
| `SpecialUnitaryScaleLSITarget d N_c` | `specialUnitaryScaleLSITarget_closed` | ✓ closed |
| `HaarLSIFromUniformLSITransfer N_c` | `haarLSIFromUniformLSITransfer_witness` | ✓ trivial |
| `HaarLSIFrontierPackage d N_c` | `haarLSIFrontierPackage_closed` | ✓ closed |
| `HaarLSITarget N_c` | `haarLSITarget_closed` | ✓ trivial |

---

## Soundness Audit — What These Closures Actually Mean

The closures above are **structurally sound at the packaging layer** but
do **not** constitute a proof of the Clay Yang-Mills conjecture.

The reason is that the definitions being discharged are deliberately
weak placeholders:

- `HaarLSITarget n = ∃ α : ℝ, 0 < α` — this is an existence statement with
  no binding to the actual LSI constant; any `α > 0` suffices.
- `BalabanRGPackage` fields end in `True` or `cP ≤ β` — these are tracking
  wrappers, not the full mathematical content.

The **mathematically substantive** targets are:
- `HaarLSIAnalyticTarget N_c` — carries the genuine `LogSobolevInequality`
- `sun_gibbs_dlr_lsi` — DLR-LSI for the SU(N) Gibbs family

---

## Remaining Honest Axioms

### Clay-Core Axioms (Genuine Mathematical Gaps)

| Axiom | File | Content |
|---|---|---|
| `sun_bakry_emery_cd` | `BalabanToLSI.lean` | SU(N) satisfies Bakry-Émery CD(N/4, ∞) |
| `balaban_rg_uniform_lsi` | `BalabanToLSI.lean` | RG promotes per-site Haar-LSI to uniform finite-volume DLR-LSI |
| `sz_lsi_to_clustering` | `BalabanToLSI.lean` | Stroock–Zegarlinski: uniform DLR-LSI → exponential clustering |
| `sun_gibbs_dlr_lsi` | `PhysicalMassGap.lean` | DLR-LSI for SU(N) Yang-Mills (assembled from above) |
| `clustering_to_spectralGap` | `PhysicalMassGap.lean` | Exponential clustering → spectral gap (mass gap) |

### Mathlib Gap Axioms (Formalization Infrastructure Gaps)

| Axiom | File | Content |
|---|---|---|
| `bakry_emery_lsi` | `BalabanToLSI.lean` | Bakry-Émery curvature criterion implies LSI (Mathlib gap) |
| `instIsTopologicalGroupSUN` | `SUN_StateConstruction.lean` | `IsTopologicalGroup ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)` — Lean 4 topology inheritance gap |
| `sunDirichletForm_contraction` | `SUN_DirichletCore.lean` | Beurling-Deny normal contraction for SU(N) Dirichlet form |
| `hille_yosida` | (P8 gap) | Hille-Yosida theorem for Markov semigroups |
| `instIsProbabilityMeasure_sunHaarProb` | `BalabanToLSI.lean` | Haar measure on abstract SU(N) state is a probability measure |

### Notes on Mathlib Gap Axioms

**`instIsTopologicalGroupSUN`**: The pathway to discharge this is:
`Matrix.unitaryGroup (Fin n) ℂ` has `IsTopologicalGroup` via
`[ContinuousMul ℂ] [ContinuousStar ℂ]`. Since `specialUnitaryGroup` is a
closed subgroup of `unitaryGroup`, `Subgroup.instIsTopologicalGroup` should
apply once the subgroup structure is correctly threaded. Requires either a
Mathlib4 PR or a local `instance` declaration using `Subgroup.toTopologicalGroup`.

**`sunDirichletForm_contraction`**: The Beurling-Deny normal contraction
`E(trunc ∘ f, trunc ∘ f) ≤ E(f, f)` follows from the chain rule
`lieD'(trunc ∘ f) = deriv(trunc)(f) · lieD'(f)` with `|deriv(trunc)| ≤ 1`
pointwise (since `trunc` is 1-Lipschitz). Once `lieD'_chain` is available
the proof is immediate.

---

## Previous Axiom Milestones

- **Axiom 5** (2026-03-28): 4 P91 BalabanRG files fully verified (0 errors, 0 warnings, 0 sorry)
- **Axiom 4** (2026-03-28): 16 BalabanRG modules compiled clean
- **Axiom 3** (2026-03-28): `BalabanRGUniformLSIEquivalenceRegistry` clean
- **Axiom 2** (2026-03-28): `HaarLSIDirectBridge` clean

---

## Public Lane Status

```
BalabanRGUniformLSILiveTarget     ← CLOSED (BalabanRGPackageWitness.lean)
  = SpecialUnitaryDirectUniformLSITheoremTarget
  = ∃ _ : BalabanRGPackage d N_c, True

HaarLSIFrontierPackage            ← CLOSED (HaarLSITransferWitness.lean)
  = SpecialUnitaryScaleLSITarget ∧ HaarLSITarget
  (weak placeholder targets only)

HaarLSIAnalyticTarget             ← open (depends on bakry_emery_lsi + sun_bakry_emery_cd)
ClayYangMillsTheorem              ← open (depends on all Clay-core axioms above)
```
