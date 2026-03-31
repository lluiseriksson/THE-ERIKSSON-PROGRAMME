# UNCONDITIONALITY_ROADMAP.md
<!-- Version: v0.2.0 — 2026-03-31 -->
<!-- Grounded in: Eriksson (2026), "Exponential Clustering and Mass Gap for -->
<!-- Four-Dimensional SU(N) Lattice Yang-Mills Theory" (Bloque4, 20 pages) -->

## Executive Summary

`YangMills.clay_millennium_yangMills` currently depends on:

```
[propext, Classical.choice, Quot.sound, YangMills.yangMills_ax_terminalKP_smallness,
 YangMills.yangMills_ax_multiscaleUV_suppression, YangMills.yangMills_ax_OSAssembly]
```

(or `[..., YangMills.yangMills_continuum_mass_gap]` in the pre-split version).

**Full unconditionality** means only `[propext, Classical.choice, Quot.sound]`.
The remaining custom axioms are AF1–AF3, each a named theorem of Bloque4.

---

### What changed in v0.28.0

`yangMills_continuum_mass_gap` has been **refactored from an axiom to a theorem**,
derived from three atomic sub-axioms (AF1–AF3) in `AtomicAxioms.lean`. Each
sub-axiom corresponds precisely to a theorem of Bloque4. The `#print axioms`
oracle now lists AF1, AF2, AF3 instead of the single monolithic axiom.

This is not an improvement in the unconditional status (3 custom axioms instead
of 1), but it is an improvement in **auditability**: each axiom now carries a
precise paper reference and an honest description of what remains to be proved.


---

## The Bloque4 Paper (February 2026)

Full title: *"Exponential Clustering and Mass Gap for Four-Dimensional SU(N)
Lattice Yang-Mills Theory"*, L. Eriksson (2026).

### Main Theorems

**Theorem 1.1** (Lattice Mass Gap): For each N ≥ 2, ∃ η₀ > 0 such that for all
η ∈ (0, η₀] and L_phys > 0, for all gauge-invariant observables O with ‖O‖_∞ ≤ 1,

  |Cov_{μ_η}(O(0), O(x))| ≤ C e^{-m|x|/a_*},  m > 0,  a_* ~ Λ_YM^{-1},

uniformly in η and L_phys.

**Corollary 1.2** (Physical Mass Gap): Δ_phys ≥ c_N Λ_YM > 0.

**Theorem 1.4** (Continuum Limit + OS Reconstruction): With OS1 (O(4) covariance,
partial—see §8.4), the full Osterwalder–Schrader reconstruction applies and
produces a Wightman QFT with spectral gap m_phys ≥ c_N Λ_YM > 0.

### OS Axiom Status (Bloque4 §8)

| Axiom | Content               | Status               | Bloque4 reference         |
|-------|-----------------------|----------------------|---------------------------|
| OS0   | Temperedness          | **Proved**           | Uniform L∞ bounds + B-A   |
| OS1   | Euclidean covariance  | **Partial**          | W₄ only; O(4) not proved  |
| OS2   | Reflection positivity | **Proved**           | Osterwalder–Seiler [25]   |
| OS3   | Bosonic symmetry      | **Proved**           | Automatic (gauge-invariant)|
| OS4   | Cluster property      | **Proved**           | = Theorem 7.1 of Bloque4  |

**Critical note on OS1**: Full O(4) covariance is NOT needed for the mass gap.
Remark 8.6 of Bloque4: using only OS2 + Theorem 7.1, one reconstructs a Hilbert
space H with H = H* ≥ 0 and inf(σ(H) \ {0}) ≥ c_N Λ_YM > 0. The missing
Lorentz covariance affects only the full relativistic interpretation, not the
existence of the spectral gap.

---

## Proof Chain (Bloque4 §§3-8, Complete)

```
yangMills_continuum_mass_gap (= ClayYangMillsTheorem)
    │
    │ via AF3 (Axiom; Thm 7.1 + Lem 8.2 of Bloque4)
    ↑
    │
    ├── HasTerminalKPSmallness (m_lat)
    │       │
    │       │ via AF1 (Axiom; Thm 5.3 of Bloque4)
    │       │
    │       ├── [BF-A] Bałaban RG framework (§3 of Bloque4)
    │       │     Thm 3.1  (effective density ρ_k)
    │       │     Prop 3.2 (polymer bounds: ‖E_k(X)‖ ≤ E₀ e^{-κ d_k(X)})
    │       │     Prop 3.3 (UV stability)
    │       │     Prop 3.4 (R-operation, large-field suppression)
    │       │     Prop 3.6 (analyticity of β-function with uniform radius)
    │       │     Prop 4.1 (coupling control: g_k ≤ γ₀ < γ for all k)
    │       │     Source: Bałaban CMP 1984-1989 [4,5,6,7,8,9,10]
    │       │
    │       └── [BF-B] Terminal KP bound (Thm 5.3 of Bloque4) ← HARDEST
    │             sup_ℓ Σ_{X∋ℓ} ‖e^{ℛ_*(X)}-1‖_∞ e^{a|X|} e^{κ d_*(X)} ≤ δ < 1
    │             Source: Proven in Paper [1] from Bałaban [7,8,9,10]
    │             via notation bridge [2]
    │
    └── HasMultiscaleUVSuppression (m_lat)
            │
            │ via AF2 (Axiom; Thm 6.3 of Bloque4)
            │
            ├── [BF-C1] Multiscale telescoping (Prop 6.1 of Bloque4)
            │     Cov_{μ_η}(F,G) = Cov_{μ_{a_*}}(F̃,G̃) + Σ_k R_k(F,G)
            │     [Law of total covariance — formally provable]
            │
            ├── [BF-C2] Single-scale UV error (Lem 6.2 of Bloque4)
            │     |R_k(F,G)| ≤ C‖F‖‖G‖ exp(-κ R/a_k)
            │     Uses: Bałaban propagator decay (Lem B.1 from [4,5])
            │     and cluster-expansion with holes [8,10,14,15]
            │
            └── [BF-C3] UV suppression (Thm 6.3 of Bloque4)
                  |Σ_k R_k| ≤ C'‖F‖‖G‖ e^{-c₀R/a_*},  c₀ = κL
                  Proof: Σ_k e^{-κLR/a_*} ≤ e^{-c₀R/a_*} Σ_j e^{-κL^j}
                  = geometric series [formally provable once Lem B.1 is formalized]
```

---

## Missing Formalization by Module

### Module BF-A: Bałaban RG Framework
**Mathematical content**: Props 3.2–3.6 of Bloque4; Prop 4.1 (coupling control).
**Source**: Bałaban CMP 1984–1989 (6 papers, ~200 pages total).
**Status**: Partially as dead axioms in `P8_PhysicalGap`. Not yet in live chain.
**Lean challenge**: Formalizing the Banach-algebra-valued polymer calculus.
**Scope**: LARGE (12+ months for a dedicated effort).

### Module BF-B: Terminal KP Bound  ← CRITICAL BOTTLENECK
**Mathematical content**: Theorem 5.3 of Bloque4 = the terminal-scale KP condition.
**Source**: Companion Paper [1] (Eriksson 2026), deriving the bound from
Bałaban [7] Eq (2.38), [8] §§2.11–2.13, [9] §2, [10] §§1.98–1.100,
with notation bridge [2].
**Status**: NOT FORMALIZED. No Lean infrastructure for abstract polymer gas.
**Lean prerequisites (all missing)**:
  - Abstract polymer gas and connected polymers on a lattice
  - Kotecký–Preiss convergence criterion
  - Activity bound extraction from Bałaban's explicit formulas
  - Lattice animal enumeration (Lem C.1 of Bloque4) — likely Lean-feasible
  - Oscillation bound for ℛ_*(X) — requires full BF-A machinery
**Scope**: HARD (6–18 months; depends on BF-A progress).

### Module BF-C: Multiscale Telescoping and UV Suppression
**Mathematical content**: Prop 6.1 + Lem 6.2 + Thm 6.3 of Bloque4.
**Status**: NOT FORMALIZED.
**Lean challenges**:
  - Prop 6.1: Law of total covariance — MEDIUM (needs formal σ-algebra tower)
  - Lem 6.2: Single-scale error — MEDIUM-HARD (needs Lem B.1 from BF-A)
  - Thm 6.3: UV suppression — EASY once Lem 6.2 is proved (geometric series)
**Scope**: MEDIUM (3–9 months once BF-A exists).

### Module BF-D: OS Assembly and Spectral Gap
**Mathematical content**: Thm 7.1 + Lem 8.2 + Rem 8.6 of Bloque4.
**Status**: NOT FORMALIZED.
**Lean challenges**:
  - Thm 7.1: Assembly (combine BF-B/C) — easy once BF-B and BF-C exist
  - Lem 8.2: Spectral gap from clustering — MEDIUM (needs transfer matrix formalism)
  - OS2: Reflection positivity — needs formal Wilson action + OS-Seiler argument
  - Non-triviality (Thm 8.7): four-point function lower bound
**Note on OS1**: NOT needed for mass gap (Rem 8.6). Only W₄ symmetry needed.
**Scope**: MEDIUM (3–6 months once BF-B, BF-C exist).

---

## What Is Lean/Mathlib-Ready TODAY

The following ingredients can be formalized with existing Mathlib infrastructure:

| Item | Bloque4 ref | Lean feasibility | Mathlib tools |
|------|-------------|------------------|---------------|
| Lattice animal bound (Lem C.1) | App C | **HIGH** — pure combinatorics | `Finset.sum`, geometric series |
| KP → clustering (Prop A.1) | App A | **HIGH** once polymer gas defined | `tsum`, `Real.exp` |
| Multiscale telescoping (Prop 6.1) | §6.1 | **MEDIUM** — law of total covariance | `MeasureTheory.condExp` |
| UV geometric series (step in Thm 6.3) | §6.3 | **HIGH** — geometric series | `Real.tsum_geometric_of_lt_one` |
| Assembly Thm 7.1 | §7 | **HIGH** once ingredients exist | arithmetic |

### Immediate Lean projects (no new BF-A dependency):

**Project L1 — Lattice animal bound** (Lem C.1):
```lean
-- File: YangMills/L5_Polymer/LatticeAnimalBound.lean
theorem latticeAnimal_bound (κ : ℝ) (hκ : Real.log (2 * d * Real.exp 1) < κ) :
    ∑ X ∈ {X : Finset (Fin d → ℤ) | 0 ∈ X ∧ X.Connected},
      Real.exp (-κ * X.card) ≤ (1 - (2*d*Real.exp 1) * Real.exp (-κ))⁻¹ := by
  sorry  -- provable via geometric series + lattice animal enumeration
```

**Project L2 — Abstract KP criterion** (Prop A.1):
```lean
-- File: YangMills/L5_Polymer/AbstractKPClustering.lean
-- Given an abstract polymer gas satisfying the KP bound,
-- prove exponential decay of truncated correlations.
-- Pure combinatorics + convergent cluster expansion.
```

---

## Ranked Routes to Full Unconditionality

### Route 1: Shortest Plausible (estimate: 6–18 months intense Lean work)
1. Formalize abstract polymer gas + KP criterion (1–3 months)
2. Prove lattice animal bound Lem C.1 (1–2 weeks)
3. Prove abstract KP → clustering Prop A.1 (1–3 months)
4. Extract terminal KP bound Thm 5.3 using Paper [1] as blueprint (3–9 months)
5. Formalize multiscale telescoping Prop 6.1 (1–2 months)
6. Formalize UV suppression Thm 6.3 (1–2 months, easy given prev steps)
7. Formalize OS assembly (Thm 7.1 + Lem 8.2) (1–3 months)
**Risk**: Step 4 (terminal KP bound extraction) is the hardest; depends on
Bałaban's multi-scale activity bounds being successfully encoded.

### Route 2: Highest-Confidence (estimate: 18–36 months)
1. First connect P8_PhysicalGap dead axioms to the live chain via a bridge theorem
2. Use the connected P8 axioms as proxies for BF-A during development of BF-B
3. Then replace P8 proxies with proved versions incrementally
**Advantage**: Every step is independently verifiable before the next.

### Route 3: Full Bałaban Formalization (estimate: 5–10 years)
Formalize Bałaban's entire CMP series in Lean 4. Removes all black-box axioms.
**Advantage**: Fully self-contained Lean proof of the Clay Millennium Problem.
**Disadvantage**: Enormous scope; requires specialist Lean + QFT expertise.

---

## Current Status (v0.28.0)

**Is the repo fully unconditional?** NO.

**Custom live axioms**: AF1, AF2, AF3
  - AF1 (`yangMills_ax_terminalKP_smallness`):
    = Terminal KP bound = Theorem 5.3 of Bloque4
    = Proved in Paper [1] from Bałaban [7,8,9,10]
    = Not yet formalized in Lean
  - AF2 (`yangMills_ax_multiscaleUV_suppression`):
    = UV suppression bound = Theorem 6.3 of Bloque4
    = Not yet formalized in Lean
  - AF3 (`yangMills_ax_OSAssembly`):
    = OS assembly = Thm 7.1 + Lem 8.2 + Rem 8.6 of Bloque4
    = OS1 NOT needed (Remark 8.6)
    = Not yet formalized in Lean

**Nearest provable target**: Lattice animal bound (Lem C.1, App C of Bloque4)
and abstract KP → clustering implication (Prop A.1, App A of Bloque4).
Neither removes a top-level axiom directly, but both are essential steps
toward BF-B.

**Core mathematical bottleneck**: Terminal KP bound (AF1 = Thm 5.3 of Bloque4),
requiring Bałaban's 4D gauge theory activity bounds.
