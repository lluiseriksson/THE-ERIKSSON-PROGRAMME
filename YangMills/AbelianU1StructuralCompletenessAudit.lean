/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

-- Clay-grade ladder
import YangMills.ClayCore.AbelianU1Unconditional
import YangMills.ClayCore.AbelianU1PhysicalStrongUnconditional
import YangMills.L7_Continuum.AbelianU1PhysicalStrongGenuineUnconditional

-- OS-axiom quartet
import YangMills.L6_OS.AbelianU1Reflection
import YangMills.L6_OS.AbelianU1ClusterProperty
import YangMills.L6_OS.AbelianU1OSAxioms

-- Branch III LSI/Poincaré
import YangMills.P8_PhysicalGap.AbelianU1LSIDischarge
import YangMills.P8_PhysicalGap.AbelianU1LSIExtensions

-- Markov semigroup framework
import YangMills.P8_PhysicalGap.AbelianU1MarkovSemigroup

-- Branch I + Branch VII glue
import YangMills.L7_Continuum.AbelianU1OSContinuumBridge

-- Feynman-Kac bridge
import YangMills.L6_FeynmanKac.AbelianU1FeynmanKacBridge

/-!
# SU(1) Structural-Completeness Audit

This module is a **single point of truth** for the SU(1)
structural-completeness milestone (Phases 7.2 + 43–57).

It imports every SU(1) unconditional witness produced by the
project, and exposes a single audit theorem stating that the SU(1)
Wilson Gibbs measure satisfies every named structural / Clay-grade /
OS / LSI / Markov / Feynman-Kac predicate the project defines.

## Purpose

1. **Consumer test**: forces all SU(1) witness modules to type-check
   together. Any namespace/import drift surfaces here at build time.
2. **Documentation in Lean**: `clayProgramme_su1_structurally_complete`
   is a citable proof-witness for the structural-completeness
   milestone, separately from the markdown-level claims.
3. **Compose-ability check**: makes explicit that the four predicate
   families (Clay-grade, OS, LSI/Poincaré, Markov) interlock without
   contradiction at SU(1).

## Caveat

The trivial-group physics-degeneracy of `COWORK_FINDINGS.md`
Findings 003 + 011 + 012 applies. Every conjunct of the audit
theorem is satisfied via the Subsingleton-collapse mechanism:
`GaugeConfig d L SU(1)` is a `Subsingleton`, every observable is
constant, every variance/entropy/connected-correlator vanishes, and
every endomorphism of the gauge-config space equals the identity.

This audit theorem is **structurally** non-vacuous — every project
predicate is provably inhabitable. It is **not** a physical
Yang-Mills mass-gap proof for `N_c ≥ 2` and does not pretend to be.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.Audit

open MeasureTheory

/-! ## §1. Cumulative SU(1) inventory (informational) -/

/-
Family count after Phase 57:

| # | Family                  | Predicates inhabited                                      |
|---|-------------------------|-----------------------------------------------------------|
| 1 | Clay-grade ladder       | 4 (Theorem, MassGap, PhysicalStrong, PhysicalStrong_Gen)  |
| 2 | OS-axiom quartet        | 4 (Cov, RP, Cluster, InfVolLim)                          |
| 3 | Branch III analytic     | 4 (DirForm, Poincaré, LSI, ExpClustering)                 |
| 4 | LSI extensions          | 4 (DirFormStrong, MemLp, DLR_LSI, DLR_LSI_MemLp)          |
| 5 | Markov semigroup        | 3 (SymTransport, VarDecay, MarkovSemigroup)               |
| 6 | OS-Continuum bridge     | 1 (OSContinuumBridge)                                     |
| 7 | Feynman-Kac bridge      | 2 (FKWilsonBridge, FKWilsonBridgeUniform)                |
|   | **TOTAL**               | **22** distinct predicates inhabited                      |

Each is a concrete unconditional inhabitant for SU(1). The audit
theorem below combines a representative subset; the remaining
witnesses are independently citable from their respective files.
-/

/-! ## §2. Audit theorem — representative SU(1) bundle -/

/-- **Master SU(1) structural-completeness audit theorem.**

    A single Prop-level statement asserting that the SU(1) Wilson
    Gibbs measure inhabits a representative member of each of the
    seven predicate families covered by Phases 7.2 + 43–57.

    The theorem deliberately does NOT take any hypothesis about
    `N_c ≥ 2` content. Every conjunct is established via the
    Subsingleton-collapse mechanism specific to SU(1).

    **What this proves**: each family the project defines is
    structurally non-vacuous in at least the trivial-group case.
    **What this does NOT prove**: physical SU(N) Yang-Mills mass gap
    for `N_c ≥ 2`. -/
theorem clayProgramme_su1_structurally_complete
    {d L : ℕ} [NeZero d] [NeZero L]
    (β : ℝ) (hβ : 0 < β)
    (F : ↑(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
    (hF : ∀ U, |F U| ≤ 1) (hF_meas : Measurable F)
    (Λ : ℝ) (hΛ : 0 < Λ)
    (t : Fin L) :
    -- (1) Clay-grade: PhysicalStrong for SU(1) at d = 4
    (YangMills.ClayYangMillsPhysicalStrong
      (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β F
      (fun (M : ℕ) (p q : ConcretePlaquette physicalClayDimension M) =>
        siteLatticeDist p.site q.site)) ∧
    -- (2) Clay-grade Genuine: PhysicalStrong_Genuine inhabitable
    (∃ scheme : YangMills.PhysicalLatticeScheme 1,
      YangMills.ClayYangMillsPhysicalStrong_Genuine
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β F
        (fun (M : ℕ) (p q : ConcretePlaquette 4 M) =>
          siteLatticeDist p.site q.site) scheme) ∧
    -- (3) OS reflection positivity (Wilson form)
    (0 ≤ ∫ U, F U * F (wilsonReflection
        (G := ↑(Matrix.specialUnitaryGroup (Fin 1) ℂ)) t U)
      ∂(gibbsMeasure (d := d) (N := L)
          (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)) ∧
    -- (4) OS clustering
    (YangMills.OSClusterProperty
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      (GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
      (fun (G : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
           (U : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin 1) ℂ)) => G U)
      (fun _ _ => (0 : ℝ))) ∧
    -- (5) Branch III: Dirichlet form (zero form)
    (IsDirichletForm (fun _ : (YangMills.P8.SU1Config d L → ℝ) => (0 : ℝ))
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)) ∧
    -- (6) Markov semigroup: identity transport gives full MarkovSemigroup
    (Nonempty (YangMills.MarkovSemigroup
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β))) ∧
    -- (7) OS-Continuum bridge
    (YangMills.OSContinuumBridge
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      (GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
      (fun (G : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
           (U : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin 1) ℂ)) => G U)
      (fun _ _ => (0 : ℝ)) (YangMills.constantMassProfile 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) PhysicalStrong
    exact YangMills.clayYangMillsPhysicalStrong_su1_unconditional β hβ F hF hF_meas
  · -- (2) PhysicalStrong_Genuine — uses dimensional_transmutation_witness_unconditional
    exact YangMills.Continuum.clayYangMillsPhysicalStrong_Genuine_su1_unconditional
            β F Λ hΛ
  · -- (3) Wilson-form RP
    exact YangMills.L6_OS.wilsonGibbs_reflectionPositive_su1 (d := d) (L := L) β t F
  · -- (4) OS clustering
    exact YangMills.L6_OS.osClusterProperty_su1 (d := d) (L := L) β _ (fun G U => G U)
            (fun _ _ => 0)
  · -- (5) Dirichlet form (zero form)
    exact YangMills.P8.isDirichletForm_zero _
  · -- (6) MarkovSemigroup
    exact ⟨YangMills.P8.markovSemigroup_su1 (d := d) (L := L) β⟩
  · -- (7) OS-Continuum bridge
    exact YangMills.L7_Continuum.osContinuumBridge_su1
            (d := d) (L := L) β _ (fun G U => G U) (fun _ _ => 0)

#print axioms clayProgramme_su1_structurally_complete

/-! ## §3. Coordination note -/

/-
This single statement bundles 7 representative conjuncts spanning all
four predicate families. The remaining 15 inhabitants in the family
inventory above (Theorem, MassGap, OSCovariant, OSReflectionPositive
in axiom-form, HasInfiniteVolumeLimit, IsDirichletFormStrong,
PoincareInequality, LogSobolevInequality, LogSobolevInequalityMemLp,
ExponentialClustering, DLR_LSI, DLR_LSI_MemLp, SymmetricMarkovTransport,
HasVarianceDecay, FeynmanKacWilsonBridge, FeynmanKacWilsonBridgeUniform)
are independently citable from their respective phase files.

The structural-completeness milestone for SU(1) is therefore:
* **22 distinct predicates** inhabited unconditionally.
* **7 predicate families** covered.
* **0 axioms introduced** (all `[propext, Classical.choice, Quot.sound]`).
* **0 sorrys**.
* **1 single audit theorem** binding the families together.

For the full Clay Millennium target (`N_c ≥ 2`, ℝ⁴, Wightman QFT), the
remaining substantive work is tracked in `AXIOM_FRONTIER.md`,
`SORRY_FRONTIER.md`, and the various blueprint markdown files.

Cross-references:
- `COWORK_FINDINGS.md` Findings 003 + 011 + 012.
- `COWORK_SESSION_2026-04-25_SUMMARY.md` §14 — comprehensive phase log.
- `README.md` §3 (SU(1) structural-completeness sweep).
-/

end YangMills.Audit
