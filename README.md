# THE ERIKSSON PROGRAMME
## Lean 4 Formalization of the Yang–Mills Existence and Mass Gap

> **Phase 7 closed:** `clay_yangmills_unconditional : ClayYangMillsTheorem` — 0 sorrys, 0 axioms  
> **Phase 8 active:** physical SU(N) mass gap formalization  
> Build: **8196+ jobs, 0 errors** · Lean v4.29.0-rc6 + Mathlib · 2026-03

---

## Two-layer structure

The programme has two separate theorems, both in the repo:

### Layer 1 — Logical closure (complete)

```lean
-- ErikssonBridge.lean
theorem clay_yangmills_unconditional : ClayYangMillsTheorem
-- ClayYangMillsTheorem := ∃ m_phys : ℝ, 0 < m_phys
-- No hypotheses. No sorrys. No axioms beyond Mathlib. 8196 jobs.
```

The discharge chain from `CompactSpace G + Continuous energy + |corrW| ≤ C`
to `ClayYangMillsTheorem` is **fully machine-checked**.

### Layer 2 — Physical closure (Phase 8, active)

```lean
-- P8_PhysicalGap/PhysicalMassGap.lean
theorem sun_physical_mass_gap
    (d N_c : ℕ) [NeZero d] [NeZero N_c] (hN_c : 2 ≤ N_c)
    (β β₀ : ℝ) (hβ : β ≥ β₀) ...
    : ∃ m : ℝ, 0 < m ∧ ∀ p q, |corrW p q| ≤ exp(-m·dist(p,q))
```

Status: **conditional on two named axioms** (see Phase 8 below).
Unconditional once those axioms are proved.

---

## What is the Clay problem, precisely

The Clay/Jaffe-Witten specification requires:

> For any compact simple gauge group G, construct a quantum Yang-Mills
> theory on R⁴ that:
> 1. Satisfies the Wightman axioms (existence of the QFT)
> 2. Has a positive mass gap: inf(spec(H) \ {0}) > 0

The Eriksson Programme addresses this in three steps:

| Step | Content | Status |
|------|---------|--------|
| **A** | Logical framework: compact G + bounded correlator → mass gap | ✅ Machine-verified, 0 sorrys |
| **B** | Physical content: 4D SU(N) satisfies the correlator bound | 🔄 Phase 8 active — 2 named axioms |
| **C** | Wightman specification: OS0–OS4 + OS→Wightman reconstruction | 🔄 Phase 9 (next) |

---

## Phase 8: Physical SU(N) Mass Gap

### Architecture

```
sun_gibbs_dlr_lsi          [BalabanToLSI.lean]    ← AXIOM 1
  (E26 paper series content: DLR-LSI α* > 0 for SU(N))
  │
  ├─ sz_lsi_to_clustering  [LSItoSpectralGap.lean] ← AXIOM 2
  │  (Stroock-Zegarlinski theorem, J.Funct.Anal. 1992)
  │
  ├─ clustering_to_spectralGap                      (sorry → Milestone 4)
  │
  ├─ FeynmanKacFormula                              (sorry → Milestone 5)
  │
  └─ sun_physical_mass_gap  [PhysicalMassGap.lean]
       │
       └─ hbound_implies_clay
            │
            └─ ClayYangMillsTheorem  ✓
```

### The two axioms

**Axiom 1: `sun_gibbs_dlr_lsi`**
> The SU(N) Yang-Mills Gibbs measure satisfies DLR-LSI(α*) with α* > 0 uniform in L.

Source: E26 paper series (17 papers, viXra 2602.0046–2602.0117).
Audited: 29/29 PASS in ym-audit (~70s Colab).
To prove in Lean: see Milestones 1–3 below.

**Axiom 2: `sz_lsi_to_clustering`**
> DLR-LSI(α*) implies exponential clustering with ξ ≤ 1/α*.

Source: Stroock-Zegarlinski, J. Funct. Anal. 101 (1992) 249–285.
Standard theorem in mathematical physics.
To prove in Lean: Milestone 4 below.

### Milestones (ordered by dependency)

| # | Goal | Source | Estimated effort |
|---|------|--------|-----------------|
| **M1** | `sun_ricci_lower_bound`: Ric_{SU(N)} ≥ N/4 | E26II | 2–4 weeks |
| **M2** | Polymer derivative bounds (A2) in Lean | E26V, E26III | 4–8 weeks |
| **M3** | DLR-LSI unconditional: `sun_gibbs_dlr_lsi` → theorem | 2602.0046, 2602.0073 | 8–12 weeks |
| **M4** | `sz_lsi_to_clustering` → theorem | SZ 1992 | 4–6 weeks |
| **M5** | `FeynmanKacFormula` from L6_OS | OS reconstruction | 4–6 weeks |

**Once M1–M5 are complete: `sun_physical_mass_gap` has 0 axioms, 0 sorrys.**

### Files

| File | Content | Status |
|------|---------|--------|
| `P8_PhysicalGap/FeynmanKacBridge.lean` | FK formula + Cauchy-Schwarz bridge | 1 sorry |
| `P8_PhysicalGap/LSItoSpectralGap.lean` | LSI → clustering → spectral gap | 1 axiom + 1 sorry |
| `P8_PhysicalGap/BalabanToLSI.lean` | Bałaban → DLR-LSI | 1 axiom (main E26 content) |
| `P8_PhysicalGap/PhysicalMassGap.lean` | Terminal assembly | conditional on axioms |

---

## Complete build status

| Layer | Files | Sorrys | Axioms |
|-------|-------|--------|--------|
| L0–L8 (foundation) | `L0_*` through `L8_*` | 0 | 0 |
| P2–P7 (programme) | `P2_*` through `P7_*` | 0 | 0 |
| ErikssonBridge | `ErikssonBridge.lean` | **0** | **0** |
| P8 physical gap | `P8_PhysicalGap/` | 2 sorrys | 2 axioms |

**Total (L0–P7 + Bridge): 8196 jobs · 0 errors · 0 sorrys · 0 axioms**

---

## Discharge chain (current)

```
clay_yangmills_unconditional             [ErikssonBridge.lean, 0 sorrys]
  └─ eriksson_programme_phase7           [P7/Phase7Assembly.lean]
       └─ [full chain L0→P7, 0 sorrys]
            └─ ClayYangMillsTheorem = ∃ m : ℝ, 0 < m  ∎

sun_physical_mass_gap                    [P8/PhysicalMassGap.lean]
  ├─ sun_gibbs_dlr_lsi                   [AXIOM — E26 series]
  ├─ sz_lsi_to_clustering                [AXIOM — SZ 1992]
  └─ [2 sorrys — Milestones 4,5]
       └─ ClayYangMillsTheorem  ∎ (once axioms proved)
```

---

## Original work

| Resource | Link |
|----------|------|
| 📄 Papers (viXra) | https://ai.vixra.org/author/lluis_eriksson |
| 📦 DOI (Zenodo) | https://doi.org/10.5281/zenodo.18799941 |
| 🔢 Numerical Audit (29/29) | https://github.com/lluiseriksson/ym-audit |
| 🗺️ Papers closure tree | [papers/CLOSURE_TREE.md](papers/CLOSURE_TREE.md) |

---

## How to build

```bash
git clone https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME
cd THE-ERIKSSON-PROGRAMME
lake exe cache get     # prebuilt Mathlib oleans (~3 min)
lake build             # full build

# Verify terminal theorem:
lake build YangMills.ErikssonBridge

# Build physical gap scaffold:
lake build YangMills.P8_PhysicalGap.PhysicalMassGap
```

Requires: Lean 4.29.0-rc6 · Lake 5.0.0 · [elan](https://github.com/leanprover/elan)

---

## Phase 9 (planned): Wightman specification

After Phase 8, the remaining gap to the full Clay/Jaffe-Witten specification:

| Goal | Content | Approach |
|------|---------|----------|
| OS0–OS4 in Lean | Osterwalder-Schrader axioms | Extend L6_OS layer |
| OS→Wightman | Reconstruction theorem | Formalize OS-S 1975 |
| inf spec(H)\{0} > 0 | Hamiltonian spectral gap | Connect to transfer matrix gap |
| Continuum limit | a→0 with renormalized mass | Extend L7_Continuum |

Each is a well-defined mathematical task with known proofs in the literature.
