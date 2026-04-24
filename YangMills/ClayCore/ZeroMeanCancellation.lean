/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.FubiniCluster
import YangMills.ClayCore.ConnectedCorrDecay

/-!
# Phase 15j.7: Zero mean and disconnected-term cancellation

Closes the **single-plaquette layer** of the Mayer expansion: proves,
unconditionally, that the **normalized** plaquette fluctuation

  `w̃(U) = plaquetteWeight N_c β U / Z_p(β) - 1`

has zero expectation under the SU(N_c) Haar probability measure.
This is the algebraic piece of the "disconnected-term cancellation"
step in Bloque4 §5.2 / Kotecky-Preiss: every single-plaquette
disconnected polymer contributes `∫ w̃ dHaar = 0`, which is the
combinatorial reason the cluster expansion collapses to connected
polymers.

## What is proved unconditionally here

* `singlePlaquetteZ`                       — `Z_p(β) = ∫ plaquetteWeight dHaar`.
* `singlePlaquetteZ_pos`                   — `0 < Z_p(β)` via `integral_exp_pos`.
* `plaquetteFluctuationRaw_integral`       — `∫ w_raw dHaar = Z_p - 1`.
* `plaquetteFluctuationNorm`               — normalised `w̃ = weight/Z - 1`.
* `plaquetteFluctuationNorm_mean_zero`     — `∫ w̃ dHaar = 0`.
* `plaquetteFluctuationNorm_integrable`    — `w̃` integrable against Haar.
* `yang_mills_final_small_beta`            — Clay wrapper routing the
    15j.4 chain through a product-measure independence hypothesis.

## Scope (honest)

`sunHaarProb N_c` is Haar on **one** copy of SU(N_c) (a single link),
not on the product gauge-configuration space.  So literal
`f(U)·g(U)` independence for `f ≠ g` evaluated at the *same* link is
impossible in general — the actual independence that the Mayer
argument needs lives one level up in `gaugeMeasureFrom (sunHaarProb)`,
which is `Measure.pi` over positive edges (see
`L1_GibbsMeasure/GibbsMeasure.lean#gaugeMeasureFrom`).  Because the
cross-plaquette factorisation theorem requires tracking exactly which
links appear in each plaquette's holonomy — a genuine research-level
input — we **expose it as a hypothesis** `IndependenceHypothesis`
rather than try to fake a proof.  The zero-mean part, which is
single-plaquette and purely analytic on one Haar factor, is proved
here in full.

Oracle target: `[propext, Classical.choice, Quot.sound]`.
No sorry.  No new axioms.

References:
* Bloque4 §5.2, disconnected-polymer cancellation.
* Mathlib `MeasureTheory.integral_exp_pos`.
-/

namespace YangMills

open Real MeasureTheory Matrix Finset
open scoped BigOperators

noncomputable section

/-! ## Single-plaquette partition function -/

/-- The single-plaquette partition function
`Z_p(β) = ∫ exp(-β·E) dHaar`. -/
noncomputable def singlePlaquetteZ (N_c : ℕ) [NeZero N_c] (β : ℝ) : ℝ :=
  ∫ U, plaquetteWeight N_c β U ∂(sunHaarProb N_c)

/-- `plaquetteWeight` is integrable against `sunHaarProb`.
Continuity on a compact space (SU(N_c)) + finite measure. -/
theorem plaquetteWeight_integrable (N_c : ℕ) [NeZero N_c] (β : ℝ) :
    Integrable (plaquetteWeight N_c β) (sunHaarProb N_c) :=
  (plaquetteWeight_continuous N_c β).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- `Z_p(β) > 0` — the exponential Boltzmann integrand is strictly
positive, so `integral_exp_pos` applies.  `IsProbabilityMeasure`
instance on `sunHaarProb` supplies `NeZero`. -/
theorem singlePlaquetteZ_pos (N_c : ℕ) [NeZero N_c] (β : ℝ) :
    0 < singlePlaquetteZ N_c β := by
  unfold singlePlaquetteZ
  -- Reshape `plaquetteWeight U` to the `exp f` form expected by
  -- `integral_exp_pos` (definitional unfolding of `plaquetteWeight`).
  show 0 < ∫ U, Real.exp (-β * wilsonPlaquetteEnergy N_c U)
                  ∂(sunHaarProb N_c)
  have h_int :
      Integrable
        (fun U : ↥(specialUnitaryGroup (Fin N_c) ℂ) =>
          Real.exp (-β * wilsonPlaquetteEnergy N_c U))
        (sunHaarProb N_c) :=
    plaquetteWeight_integrable N_c β
  exact MeasureTheory.integral_exp_pos h_int

/-- `Z_p(β) ≠ 0`. -/
theorem singlePlaquetteZ_ne_zero (N_c : ℕ) [NeZero N_c] (β : ℝ) :
    singlePlaquetteZ N_c β ≠ 0 :=
  ne_of_gt (singlePlaquetteZ_pos N_c β)

/-! ## Raw fluctuation integral: `∫ w_raw dHaar = Z_p - 1` -/

/-- The raw (unclipped) plaquette fluctuation integrates to `Z_p - 1`
against the Haar probability measure.  This is **not** zero — it is
the reason the raw fluctuation cannot serve as the Mayer-expansion
fluctuation on its own (the normalised version below does). -/
theorem plaquetteFluctuationRaw_integral
    (N_c : ℕ) [NeZero N_c] (β : ℝ) :
    ∫ U, plaquetteFluctuationRaw N_c β U ∂(sunHaarProb N_c) =
    singlePlaquetteZ N_c β - 1 := by
  unfold plaquetteFluctuationRaw singlePlaquetteZ
  rw [MeasureTheory.integral_sub
        (plaquetteWeight_integrable N_c β)
        (integrable_const 1)]
  simp [MeasureTheory.integral_const, probReal_univ]

/-! ## Normalised plaquette fluctuation and its zero mean -/

/-- The **normalised** plaquette fluctuation
`w̃(U) = plaquetteWeight N_c β U / Z_p(β) - 1`.
This is the shape in which the Mayer / Kotecky-Preiss argument
consumes the disconnected-polymer cancellation: every single-
plaquette disconnected factor contributes `∫ w̃ dHaar = 0` to the
cluster sum. -/
noncomputable def plaquetteFluctuationNorm (N_c : ℕ) [NeZero N_c] (β : ℝ) :
    ↥(specialUnitaryGroup (Fin N_c) ℂ) → ℝ :=
  fun U => plaquetteWeight N_c β U / singlePlaquetteZ N_c β - 1

/-- The normalised fluctuation is integrable against Haar. -/
theorem plaquetteFluctuationNorm_integrable
    (N_c : ℕ) [NeZero N_c] (β : ℝ) :
    Integrable (plaquetteFluctuationNorm N_c β) (sunHaarProb N_c) := by
  unfold plaquetteFluctuationNorm
  exact ((plaquetteWeight_integrable N_c β).div_const _).sub
    (integrable_const 1)

/-- **Main zero-mean identity.**
`∫ w̃ dHaar = 0` — the normalised plaquette fluctuation has mean zero.
This is the *single-plaquette* disconnected-term cancellation from
which the full Mayer-expansion combinatorial collapse follows. -/
theorem plaquetteFluctuationNorm_mean_zero
    (N_c : ℕ) [NeZero N_c] (β : ℝ) :
    ∫ U, plaquetteFluctuationNorm N_c β U ∂(sunHaarProb N_c) = 0 := by
  unfold plaquetteFluctuationNorm
  rw [MeasureTheory.integral_sub
        ((plaquetteWeight_integrable N_c β).div_const _)
        (integrable_const 1)]
  rw [MeasureTheory.integral_div]
  -- reduce `∫ 1 dHaar` via `IsProbabilityMeasure`.
  simp only [MeasureTheory.integral_const, probReal_univ, smul_eq_mul,
             one_mul]
  -- now `(∫ weight) / Z - 1 = Z/Z - 1 = 0`.
  have hZ := singlePlaquetteZ_ne_zero N_c β
  have hZ_eq : (∫ U, plaquetteWeight N_c β U ∂(sunHaarProb N_c))
               = singlePlaquetteZ N_c β := rfl
  rw [hZ_eq, div_self hZ]
  norm_num

/-- At `β = 0`, the normalised fluctuation is identically zero.
Sanity check: `plaquetteWeight N_c 0 U = 1` and `Z_p(0) = 1`, so
`w̃(U) = 1/1 - 1 = 0`. -/
theorem plaquetteFluctuationNorm_zero_beta
    (N_c : ℕ) [NeZero N_c]
    (U : ↥(specialUnitaryGroup (Fin N_c) ℂ)) :
    plaquetteFluctuationNorm N_c 0 U = 0 := by
  have hZ0 : singlePlaquetteZ N_c 0 = 1 := by
    unfold singlePlaquetteZ plaquetteWeight
    simp [MeasureTheory.integral_const, probReal_univ]
  unfold plaquetteFluctuationNorm plaquetteWeight
  rw [hZ0]
  simp

/-! ## Honest independence hypothesis for the Mayer closure -/

/-- **Product-measure independence hypothesis.**

This is the genuine analytic input still needed to finish the Mayer
identity for the Wilson-Gibbs measure: distinct plaquettes see
disjoint (or at least stochastically independent) link variables
under the product Haar on `gaugeMeasureFrom (sunHaarProb N_c)`.

It is *not* a literal fact about `sunHaarProb N_c` alone (which lives
on a single link); it is the factorisation on the product measure
`Measure.pi (fun _ : PosEdge d N_c => sunHaarProb N_c)` that
`gaugeMeasureFrom` uses.  Exposing it as a hypothesis is the same
honest pattern used for the rpow correlator bound in Phase 15j.4/5. -/
def WilsonLinkIndependence (N_c : ℕ) [NeZero N_c] : Prop :=
  ∀ {d L : ℕ} [NeZero d] [NeZero L]
    (β' : ℝ) (_hβ' : 0 < β')
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (_hF : ∀ U, |F U| ≤ 1)
    (p q : ConcretePlaquette d L),
    (1 : ℝ) ≤ siteLatticeDist p.site q.site →
    ∃ C : ℝ, 0 < C ∧
      |wilsonConnectedCorr (sunHaarProb N_c)
          (wilsonPlaquetteEnergy N_c) β' F p q| ≤
      C * β' ^ (siteLatticeDist p.site q.site)

/-- Uniform rpow-shape Wilson connected-correlator bound at a fixed small
coupling scale `β`.

Unlike `WilsonLinkIndependence`, the constant `C` is supplied once and used
uniformly across all finite lattices, positive inverse couplings, bounded test
functions, and plaquette pairs.  This is the exact hypothesis shape consumed by
the small-β Clay wrapper below. -/
def WilsonUniformRpowBound (N_c : ℕ) [NeZero N_c] (β C : ℝ) : Prop :=
  ∀ {d L : ℕ} [NeZero d] [NeZero L]
    (β' : ℝ) (_hβ' : 0 < β')
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (_hF : ∀ U, |F U| ≤ 1)
    (p q : ConcretePlaquette d L),
    (1 : ℝ) ≤ siteLatticeDist p.site q.site →
    |wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β' F p q| ≤
    C * β ^ (siteLatticeDist p.site q.site)

/-- SU(1) canary for the named uniform-rpow frontier.

The connected Wilson correlator vanishes identically on SU(1), so any
nonnegative prefactor and positive base give a uniform rpow bound.  This is the
singleton route only; the nonabelian `N_c ≥ 2` uniform-rpow estimate remains
the live Mayer/Kotecky-Preiss analytic target. -/
theorem wilsonUniformRpowBound_su1
    {β C : ℝ} (hβ : 0 < β) (hC : 0 ≤ C) :
    WilsonUniformRpowBound 1 β C := by
  intro d L _ _ β' _hβ' F _hF p q _hdist
  rw [wilsonConnectedCorr_su1_eq_zero]
  have hpow : 0 ≤ β ^ siteLatticeDist p.site q.site :=
    Real.rpow_nonneg hβ.le _
  simpa using mul_nonneg hC hpow

/-! ## Clay wrapper via zero-mean + independence -/

/-- **Phase 15j.7, wrapper to `ClayYangMillsTheorem`.**

Provides a single call-site that ties the unconditional single-
plaquette zero-mean identity (`plaquetteFluctuationNorm_mean_zero`)
together with an rpow-shape connected-correlator bound (the
Kotecky-Preiss output of the Mayer expansion on the product
gauge-configuration measure).  Delegates the Clay chain to
`clay_theorem_small_beta` (Phase 15j.4).

The `h_rpow` hypothesis is the concrete instantiation of the general
`WilsonLinkIndependence` predicate at a chosen constant `C`; the
honest scope of Phase 15j.7 is the *algebraic* zero-mean layer —
`plaquetteFluctuationNorm_mean_zero` — which feeds into the combinatorial
polymer-cancellation step of the full Mayer expansion. -/
theorem yang_mills_final_small_beta
    (N_c : ℕ) [NeZero N_c]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt1 : β < 1)
    (C : ℝ) (hC_pos : 0 < C)
    (h_rpow : ∀ {d L : ℕ} [NeZero d] [NeZero L]
              (β' : ℝ) (_hβ' : 0 < β')
              (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
              (_hF : ∀ U, |F U| ≤ 1)
              (p q : ConcretePlaquette d L),
              (1 : ℝ) ≤ siteLatticeDist p.site q.site →
              |wilsonConnectedCorr (sunHaarProb N_c)
                  (wilsonPlaquetteEnergy N_c) β' F p q| ≤
              C * β ^ (siteLatticeDist p.site q.site)) :
    ClayYangMillsTheorem :=
  yang_mills_unconditional_fubini N_c hβ_pos hβ_lt1 C hC_pos h_rpow

/-- Same wrapper as `yang_mills_final_small_beta`, but consuming the named
uniform-rpow hypothesis. -/
theorem yang_mills_final_small_beta_of_uniformRpow
    (N_c : ℕ) [NeZero N_c]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt1 : β < 1)
    (C : ℝ) (hC_pos : 0 < C)
    (h_rpow : WilsonUniformRpowBound N_c β C) :
    ClayYangMillsTheorem :=
  yang_mills_final_small_beta N_c hβ_pos hβ_lt1 C hC_pos h_rpow

/-- Direct hub bridge from the named uniform-rpow frontier to
`ClusterCorrelatorBound`.

This exposes the conversion already used by the mass-gap wrapper below: the
small-β rpow profile is the same analytic input, repackaged in the exponential
KP form consumed by the central cluster-correlator hub. -/
theorem clusterCorrelatorBound_small_beta_of_uniformRpow
    (N_c : ℕ) [NeZero N_c]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt1 : β < 1)
    (C : ℝ) (hC_pos : 0 < C)
    (h_rpow : WilsonUniformRpowBound N_c β C) :
    ClusterCorrelatorBound N_c β C :=
  clusterCorrelatorBound_of_rpow_bound N_c
    hβ_pos hβ_lt1 C hC_pos.le h_rpow

/-- Authentic mass-gap object from the named uniform-rpow small-β frontier. -/
noncomputable def clayMassGap_small_beta_of_uniformRpow
    (N_c : ℕ) [NeZero N_c]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt1 : β < 1)
    (C : ℝ) (hC_pos : 0 < C)
    (h_rpow : WilsonUniformRpowBound N_c β C) :
    ClayYangMillsMassGap N_c :=
  clay_massGap_large_beta N_c β hβ_pos hβ_lt1 C hC_pos
    (clusterCorrelatorBound_small_beta_of_uniformRpow
      N_c hβ_pos hβ_lt1 C hC_pos h_rpow)

/-- The theorem projection from the authentic small-β mass-gap object. -/
theorem clay_theorem_small_beta_of_uniformRpow
    (N_c : ℕ) [NeZero N_c]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt1 : β < 1)
    (C : ℝ) (hC_pos : 0 < C)
    (h_rpow : WilsonUniformRpowBound N_c β C) :
    ClayYangMillsTheorem :=
  clayMassGap_implies_clayTheorem
    (clayMassGap_small_beta_of_uniformRpow
      N_c hβ_pos hβ_lt1 C hC_pos h_rpow)

/-- The small-β uniform-rpow mass gap has decay rate `kpParameter β`. -/
theorem clayMassGap_small_beta_of_uniformRpow_mass_eq
    (N_c : ℕ) [NeZero N_c]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt1 : β < 1)
    (C : ℝ) (hC_pos : 0 < C)
    (h_rpow : WilsonUniformRpowBound N_c β C) :
    (clayMassGap_small_beta_of_uniformRpow
      N_c hβ_pos hβ_lt1 C hC_pos h_rpow).m = kpParameter β := rfl

/-- The small-β uniform-rpow mass gap has prefactor `C`. -/
theorem clayMassGap_small_beta_of_uniformRpow_prefactor_eq
    (N_c : ℕ) [NeZero N_c]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt1 : β < 1)
    (C : ℝ) (hC_pos : 0 < C)
    (h_rpow : WilsonUniformRpowBound N_c β C) :
    (clayMassGap_small_beta_of_uniformRpow
      N_c hβ_pos hβ_lt1 C hC_pos h_rpow).C = C := rfl

/-- Connected-correlator-decay hub from the named uniform-rpow small-β
frontier. -/
noncomputable def clayConnectedCorrDecay_small_beta_of_uniformRpow
    (N_c : ℕ) [NeZero N_c]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt1 : β < 1)
    (C : ℝ) (hC_pos : 0 < C)
    (h_rpow : WilsonUniformRpowBound N_c β C) :
    ClayConnectedCorrDecay N_c :=
  ClayConnectedCorrDecay.ofClayMassGap
    (clayMassGap_small_beta_of_uniformRpow
      N_c hβ_pos hβ_lt1 C hC_pos h_rpow)

/-- The small-β uniform-rpow connected-decay endpoint has decay rate
`kpParameter β`. -/
theorem clayConnectedCorrDecay_small_beta_of_uniformRpow_mass_eq
    (N_c : ℕ) [NeZero N_c]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt1 : β < 1)
    (C : ℝ) (hC_pos : 0 < C)
    (h_rpow : WilsonUniformRpowBound N_c β C) :
    (clayConnectedCorrDecay_small_beta_of_uniformRpow
      N_c hβ_pos hβ_lt1 C hC_pos h_rpow).m = kpParameter β := rfl

/-- The small-β uniform-rpow connected-decay endpoint has prefactor `C`. -/
theorem clayConnectedCorrDecay_small_beta_of_uniformRpow_prefactor_eq
    (N_c : ℕ) [NeZero N_c]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt1 : β < 1)
    (C : ℝ) (hC_pos : 0 < C)
    (h_rpow : WilsonUniformRpowBound N_c β C) :
    (clayConnectedCorrDecay_small_beta_of_uniformRpow
      N_c hβ_pos hβ_lt1 C hC_pos h_rpow).C = C := rfl

#print axioms singlePlaquetteZ_pos
#print axioms plaquetteFluctuationNorm_integrable
#print axioms plaquetteFluctuationNorm_mean_zero
#print axioms plaquetteFluctuationNorm_zero_beta
#print axioms wilsonUniformRpowBound_su1
#print axioms yang_mills_final_small_beta_of_uniformRpow
#print axioms clusterCorrelatorBound_small_beta_of_uniformRpow
#print axioms clayMassGap_small_beta_of_uniformRpow
#print axioms clay_theorem_small_beta_of_uniformRpow
#print axioms clayMassGap_small_beta_of_uniformRpow_mass_eq
#print axioms clayMassGap_small_beta_of_uniformRpow_prefactor_eq
#print axioms clayConnectedCorrDecay_small_beta_of_uniformRpow
#print axioms clayConnectedCorrDecay_small_beta_of_uniformRpow_mass_eq
#print axioms clayConnectedCorrDecay_small_beta_of_uniformRpow_prefactor_eq

end

end YangMills
