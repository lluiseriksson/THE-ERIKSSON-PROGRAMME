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
