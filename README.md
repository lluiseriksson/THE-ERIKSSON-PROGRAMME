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


---

## Complete Paper Corpus

**68 publicly timestamped papers** — full list at [ai.vixra.org/author/lluis_eriksson](https://ai.vixra.org/author/lluis_eriksson).  
Date range: December 16 2025 — February 27 2026.  
SHA-256 hashes: [`ym-audit` repo](https://github.com/lluiseriksson/ym-audit).

| # | Date | ai.viXra ID | Title |
|---|------|-------------|-------|
| 1 | — | [2602.0117](https://ai.vixra.org/abs/2602.0117) |  |
| 2 | — | [2602.0096](https://ai.vixra.org/abs/2602.0096) |  |
| 3 | — | [2602.0092](https://ai.vixra.org/abs/2602.0092) |  |
| 4 | — | [2602.0091](https://ai.vixra.org/abs/2602.0091) |  |
| 5 | — | [2602.0089](https://ai.vixra.org/abs/2602.0089) |  |
| 6 | — | [2602.0088](https://ai.vixra.org/abs/2602.0088) |  |
| 7 | — | [2602.0087](https://ai.vixra.org/abs/2602.0087) |  |
| 8 | — | [2602.0085](https://ai.vixra.org/abs/2602.0085) |  |
| 9 | — | [2602.0084](https://ai.vixra.org/abs/2602.0084) |  |
| 10 | — | [2602.0077](https://ai.vixra.org/abs/2602.0077) |  |
| 11 | — | [2602.0073](https://ai.vixra.org/abs/2602.0073) |  |
| 12 | — | [2602.0072](https://ai.vixra.org/abs/2602.0072) |  |
| 13 | — | [2602.0070](https://ai.vixra.org/abs/2602.0070) |  |
| 14 | — | [2602.0069](https://ai.vixra.org/abs/2602.0069) |  |
| 15 | — | [2602.0063](https://ai.vixra.org/abs/2602.0063) |  |
| 16 | — | [2602.0057](https://ai.vixra.org/abs/2602.0057) |  |
| 17 | — | [2602.0056](https://ai.vixra.org/abs/2602.0056) |  |
| 18 | — | [2602.0055](https://ai.vixra.org/abs/2602.0055) |  |
| 19 | — | [2602.0054](https://ai.vixra.org/abs/2602.0054) |  |
| 20 | — | [2602.0053](https://ai.vixra.org/abs/2602.0053) |  |
| 21 | — | [2602.0052](https://ai.vixra.org/abs/2602.0052) |  |
| 22 | — | [2602.0051](https://ai.vixra.org/abs/2602.0051) |  |
| 23 | — | [2602.0046](https://ai.vixra.org/abs/2602.0046) |  |
| 24 | — | [2602.0041](https://ai.vixra.org/abs/2602.0041) |  |
| 25 | — | [2602.0040](https://ai.vixra.org/abs/2602.0040) |  |
| 26 | — | [2602.0038](https://ai.vixra.org/abs/2602.0038) |  |
| 27 | — | [2602.0036](https://ai.vixra.org/abs/2602.0036) |  |
| 28 | — | [2602.0035](https://ai.vixra.org/abs/2602.0035) |  |
| 29 | — | [2602.0033](https://ai.vixra.org/abs/2602.0033) |  |
| 30 | — | [2602.0032](https://ai.vixra.org/abs/2602.0032) |  |
| 31 | — | [2602.0021](https://ai.vixra.org/abs/2602.0021) |  |
| 32 | — | [2602.0020](https://ai.vixra.org/abs/2602.0020) |  |
| 33 | — | [2601.0115](https://ai.vixra.org/abs/2601.0115) |  |
| 34 | — | [2601.0111](https://ai.vixra.org/abs/2601.0111) |  |
| 35 | — | [2601.0099](https://ai.vixra.org/abs/2601.0099) |  |
| 36 | — | [2601.0066](https://ai.vixra.org/abs/2601.0066) |  |
| 37 | — | [2601.0065](https://ai.vixra.org/abs/2601.0065) |  |
| 38 | — | [2601.0064](https://ai.vixra.org/abs/2601.0064) |  |
| 39 | — | [2601.0051](https://ai.vixra.org/abs/2601.0051) |  |
| 40 | — | [2601.0050](https://ai.vixra.org/abs/2601.0050) |  |
| 41 | — | [2601.0047](https://ai.vixra.org/abs/2601.0047) |  |
| 42 | — | [2601.0046](https://ai.vixra.org/abs/2601.0046) |  |
| 43 | — | [2601.0044](https://ai.vixra.org/abs/2601.0044) |  |
| 44 | — | [2601.0043](https://ai.vixra.org/abs/2601.0043) |  |
| 45 | — | [2601.0042](https://ai.vixra.org/abs/2601.0042) |  |
| 46 | — | [2601.0040](https://ai.vixra.org/abs/2601.0040) |  |
| 47 | — | [2601.0038](https://ai.vixra.org/abs/2601.0038) |  |
| 48 | — | [2601.0035](https://ai.vixra.org/abs/2601.0035) |  |
| 49 | — | [2601.0034](https://ai.vixra.org/abs/2601.0034) |  |
| 50 | — | [2601.0031](https://ai.vixra.org/abs/2601.0031) |  |
| 51 | — | [2601.0023](https://ai.vixra.org/abs/2601.0023) |  |
| 52 | — | [2601.0022](https://ai.vixra.org/abs/2601.0022) |  |
| 53 | — | [2601.0020](https://ai.vixra.org/abs/2601.0020) |  |
| 54 | — | [2601.0007](https://ai.vixra.org/abs/2601.0007) |  |
| 55 | — | [2512.0105](https://ai.vixra.org/abs/2512.0105) |  |
| 56 | — | [2512.0102](https://ai.vixra.org/abs/2512.0102) |  |
| 57 | — | [2512.0101](https://ai.vixra.org/abs/2512.0101) |  |
| 58 | — | [2512.0091](https://ai.vixra.org/abs/2512.0091) |  |
| 59 | — | [2512.0085](https://ai.vixra.org/abs/2512.0085) |  |
| 60 | — | [2512.0084](https://ai.vixra.org/abs/2512.0084) |  |
| 61 | — | [2512.0081](https://ai.vixra.org/abs/2512.0081) |  |
| 62 | — | [2512.0073](https://ai.vixra.org/abs/2512.0073) |  |
| 63 | — | [2512.0072](https://ai.vixra.org/abs/2512.0072) |  |
| 64 | — | [2512.0071](https://ai.vixra.org/abs/2512.0071) |  |
| 65 | — | [2512.0070](https://ai.vixra.org/abs/2512.0070) |  |
| 66 | — | [2512.0064](https://ai.vixra.org/abs/2512.0064) |  |
| 67 | — | [2512.0061](https://ai.vixra.org/abs/2512.0061) |  |
| 68 | — | [2512.0060](https://ai.vixra.org/abs/2512.0060) |  |
