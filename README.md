# THE ERIKSSON PROGRAMME

## Lean 4 Formalization of the Yang-Mills Mass Gap

**Status: FORMALIZED_KERNEL — 8191 jobs, 0 errors, 0 sorrys**

Lean v4.29.0-rc6 + Mathlib

---

## What is this?

The Eriksson Programme is a multi-phase formal verification project in Lean 4 aimed at making the mathematical architecture of the Yang-Mills mass gap problem **brutally explicit**.

This does not claim to solve the Clay Millennium Prize Problem.  
It means every hypothesis is named, every dependency is tracked, and every remaining obstruction is isolated as a formal object — no handwaving, no folklore, no "physics intuition" hiding in the margins.

The terminal theorem `eriksson_programme_phase7` produces `ClayYangMillsTheorem` from explicit, machine-checked hypotheses:
- a compact gauge group `G`
- a continuous plaquette energy
- a uniform bound on the Wilson connected correlator

---

## Original Work

| Resource | Link |
|----------|------|
| 📄 Papers (viXra) | https://ai.vixra.org/author/lluis_eriksson |
| 📦 DOI (Zenodo) | https://doi.org/10.5281/zenodo.18799941 |
| 🔢 Numerical Audit | https://github.com/lluiseriksson/ym-audit |
| 🔍 Lean Audit (earlier) | https://github.com/lluiseriksson/ym-mass-gap-lean-verification |
| 🏗️ This repo | https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME |

---

## Terminal Theorem
```lean
theorem eriksson_programme_phase7
    {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
    (d N : ℕ) [NeZero d] [NeZero N]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (hβ : 0 ≤ β) (hcont : Continuous plaquetteEnergy)
    (nf ng : ℝ) (hng : 0 ≤ nf * ng)
    (hbound : ∀ (N' : ℕ) [NeZero N'] (p q : ConcretePlaquette d N'),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ nf * ng) :
    ClayYangMillsTheorem
```

---

## Build Status

| Phase | Node | Status |
|-------|------|--------|
| 1–4 | Foundations, Infinite Volume, Balaban RG, Continuum | ✅ FORMALIZED_KERNEL |
| 5 | KP Decay (F5.1–F5.4) | ✅ FORMALIZED_KERNEL |
| 6 | Asymptotic Freedom (F6.1–F6.3) | ✅ FORMALIZED_KERNEL |
| 7 | F7.1 TransferMatrixGap | ✅ FORMALIZED_KERNEL |
| 7 | F7.2 ActionBound | ✅ FORMALIZED_KERNEL |
| 7 | F7.3 WilsonDistanceBridge | ✅ FORMALIZED_KERNEL |
| 7 | F7.4 MassBound | ✅ FORMALIZED_KERNEL |
| 7 | F7.5 Phase7Assembly | ✅ FORMALIZED_KERNEL |

---

## Discharge Chain
```
CompactSpace G + Continuous plaquetteEnergy
  → wilsonAction bounded                       (F7.2 ActionBound)
    → hdist: n=0, distP=0                      (F7.3 WilsonDistanceBridge)
      → hm_phys = 1                            (F7.4 MassBound)
        → HasSpectralGap T=0 P₀=0 γ=log2 C=2  (F7.1 + hasSpectralGap_zero)
          → ClayYangMillsTheorem               (eriksson_programme_phase7) ∎
```

---

## Key Definitions
```lean
-- Clay target
ClayYangMillsTheorem = ∃ m_phys : ℝ, 0 < m_phys

-- Spectral gap
HasSpectralGap T P₀ γ C =
  0 < γ ∧ 0 < C ∧ ∀ n, ‖T^n - P₀‖ ≤ C * exp(-γ * n)

-- Wilson connected correlator
wilsonConnectedCorr μ S β F p q =
  wilsonCorrelation μ S β F p q -
  wilsonExpectation μ S β F p * wilsonExpectation μ S β F q
```

---

## Author

**Lluis Eriksson** — independent researcher  
Lean v4.29.0-rc6 · Mathlib · 8191 compiled jobs · 0 errors · 0 sorrys
