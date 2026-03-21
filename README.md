# THE ERIKSSON PROGRAMME
Lean 4 formalization for the Yang–Mills mass gap programme

> **Current status:** Formal reduction & interface isolation  
> **Claim level:** This repository does **not** claim a finished Clay solution.  
> **Build health:** 8270+ jobs, 0 errors, 0 `sorry`s  
> **Lean / Mathlib:** Lean `v4.29.0-rc6` + Mathlib  
> **Last updated:** March 2026

---

## 1. What this repository is

The Eriksson Programme is a long-horizon formal verification project in Lean 4.

Its purpose is to formalize an **honest reduction programme** for the Clay Yang–Mills and Mass Gap problem: every bridge is named, every dependency is exposed, and every unresolved ingredient is isolated explicitly rather than hidden behind folklore or informal “standard arguments”.

This repository therefore aims at a **fully verified structural pipeline** in which the terminal theorem `ClayYangMillsTheorem` is connected to explicit formal interfaces. The programme should be considered **finished** only when the remaining terminal interfaces are discharged **inconditionally inside Lean 4**, without external witness packages or transfer assumptions.

---

## 2. Mathematical goal

Formalize a complete proof architecture for the Yang–Mills mass gap in Lean 4:

- construct a non-trivial 4D `SU(N)` quantum Yang–Mills theory,
- satisfy the Osterwalder–Schrader / Wightman interface expected by the Clay formulation,
- prove a positive spectral gap / mass gap,
- and verify every formal step in Lean.

---

## 4. Repository snapshot

| Item | Current state |
|---|---|
| Build health | **8270+ jobs, 0 errors, 0 `sorry`s** |
| Clay core | 1 Clay core axiom |
| Named axioms | 8 |
| BalabanRG status | decomposed into independent targets with concrete discharged subpaths |
| Current bridge status | singleton, finite full, concrete `L¹`, weighted `L¹`, direct-budget, native-target, and final-gap lanes all registered |

---

## 5. Unconditionality audit

| Component | Type | State | Meaning |
|---|---|---:|---|
| P91 finite-full small-constants packaging | Honest reduction | 🟢 | The finite-full constants `A_large`, `A_cauchy` are cleanly isolated |
| Direct-budget lane | Honest reduction | 🟢 | The terminal budget route is packaged |
| Native-target lane | Honest reduction | 🟢 | The native-target route is packaged |
| **SmallConstants -> DirectBudget** | **Real mathematical gap** | 🔴 | Need unconditional proof for global weighted budget |
| **SmallConstants -> NativeTarget** | **Real mathematical gap** | 🔴 | Need unconditional proof reaching native target |

---

## 7. Original work and audit trail

| Resource | Link |
|---|---|
| Papers — The Eriksson Programme (viXra [1]–[68]) | Papers organised as a closure tree |
| Full author page | https://ai.vixra.org/author/lluis_eriksson |
| Repository | https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME |

---

## 14. Author

**Lluis Eriksson** Independent researcher  
March 2026

## v1.0.26-alpha

Topological unconditionality phase started.

This milestone opens the first genuine axiom-elimination task in the repository:
formalizing compactness of the special unitary gauge group inside Lean, rather
than leaving it as external mathematical background.

No unconditional Clay claim is made at this stage. The repository remains an
honest reduction program until all terminal transfers and structural axioms are
discharged internally.

## v1.0.28-alpha

Topological assault on `SU(n)` advanced through the honest compactness reduction:
the entrywise-bounded half is now discharged by a direct Mathlib argument using
`Matrix.specialUnitaryGroup_le_unitaryGroup` together with
`entry_norm_bound_of_unitary`.

So the remaining ambient compactness gap is isolated to the closedness of the
special-unitary range.

## v1.0.29-alpha

The local special-unitary compactness assault now includes an honest closedness
layer. The ambient `SU(m)` range is identified with the closed cut
`{A | A ∈ unitaryGroup ∧ det A = 1}`, and together with the existing
entrywise-bounded witness this closes the local compactness target used by the
topological reduction.

## v1.0.30-alpha

The local special-unitary compactness transfer is now targeted as an internal
finite-dimensional theorem: closedness plus entrywise boundedness should imply
compactness of the ambient `SU(m)` range without any external transfer input.

<!-- SU_UNCONDITIONALITY_START -->
## Special-unitary compactness: unconditional status

The local special-unitary compactness block is now closed **unconditionally** inside the repository.

### Public API

Import:

- `YangMills.ClayCore.BalabanRG.SpecialUnitaryCompact`

Public theorems:

- `specialUnitary_compact_range_target`
- `specialUnitary_topology_gap_closed`

### Internal decomposition

The proof path is split into the following layers:

- `SpecialUnitaryCompactCore`
- `SpecialUnitaryCompactReduction`
- `SpecialUnitaryEntrywiseBounded`
- `SpecialUnitaryClosed`
- `SpecialUnitaryClosedEntrywiseBoundedToCompact`
- `SpecialUnitaryCompactUnconditional`

### Internal unconditional closure

Internal unconditional closure is provided by:

- `specialUnitary_compact_unconditional`
- `specialUnitary_topology_package_unconditional`

This means the local compactness route for the ambient special-unitary range is no longer left as an external transfer-only gap: the closedness step, boundedness step, and the closed+bounded ⇒ compact transfer are now all discharged inside the repository.

### Current status

- SU block build: green
- Public API stabilized
- Temporary recon/smoke files removed
- Final sanity build without warnings
<!-- SU_UNCONDITIONALITY_END -->

