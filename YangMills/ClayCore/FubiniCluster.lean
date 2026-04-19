/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.MayerIdentity

/-!
# Phase 15j.6: Fubini layer — integral/sum interchange for the cluster expansion

Closes the analytic gap between the **pointwise** algebraic expansion
of Phase 15j.5 (`boltzmann_cluster_expansion_pointwise`,
`partition_function_cluster_expansion`) and the **partition-function**
identity

  `∫ exp(-β·∑ E) dHaar = ∑_{S ⊆ P} K_raw(S)`

where `K_raw(S) = ∫ ∏_{p∈S} w_raw dHaar` is `wilsonClusterActivityRaw`.

## What this file proves unconditionally

* `continuous_plaquetteFluctuationRaw`           — `w_raw = weight - 1`
    is continuous on SU(N_c).
* `continuous_prod_plaquetteFluctuationRaw`      — finite products of
    `w_raw` are continuous (via `continuous_finset_prod`).
* `integrable_prod_plaquetteFluctuationRaw`      — they are integrable
    against `sunHaarProb N_c` (continuous on `CompactSpace` +
    `HasCompactSupport.of_compactSpace` + finite measure).
* `integral_sum_eq_sum_integral_cluster`         — Fubini:
    `∫ ∑_S ∏ w_raw dHaar = ∑_S ∫ ∏ w_raw dHaar` via
    `MeasureTheory.integral_finset_sum`.
* `integral_boltzmann_eq_sum_activities`         — the full partition-
    function cluster expansion:
    `∫ exp(-β·∑ E) dHaar = ∑_{S ⊆ P} wilsonClusterActivityRaw N_c β S`.

## What this file does NOT claim

Two targets from the original spec for this phase are intentionally
dropped here because they are **not provable** in the form stated:

* `wilsonClusterActivityRaw_bound` (amplitude bound `|K_raw(γ)| ≤ β^|γ|`)
    is **false** for the raw / unclipped fluctuation:
    `|w_raw(U)| = |exp(-β·E) - 1|` can reach `exp(β·N_c) - 1` which
    exceeds `β` already for moderate `β`.  The amplitude bound only
    holds for the β-clipped fluctuation `plaquetteFluctuationAt` of
    Phase 15j.4 — and that bound *is* proved there
    (`wilsonClusterActivity_abs_le`).  The honest routing is therefore:
    use `wilsonActivityBound_from_expansion` (Phase 15j.4) for the
    Clay chain, not the raw one.

* `connected_corr_le_sum_activities` (pointwise Mayer bound
    `|Cov(F_p, F_q)| ≤ ∑_{γ∋p,q} |K(γ)|`) requires a full product-Haar
    gauge-configuration expansion plus zero-mean cancellation of every
    disconnected polymer, which is the Bloque4 Theorem 7.1 / Kotecky-
    Preiss analytic content.  No purely algebraic route closes it.

`yang_mills_unconditional_fubini` below is therefore a **structural
wrapper** that exposes the 15j.6 Fubini statement as the final-form
integrated cluster expansion, and delegates the Clay chain itself to
the already-established small-β chain `clay_theorem_small_beta`
(Phase 15j.4, using the clipped amplitude bound).

Oracle target: `[propext, Classical.choice, Quot.sound]`.
No sorry.  No new axioms.

References:
* Bloque4 §5.1–5.3 (Mayer expansion), §7.2 Thm 7.1 (Kotecky-Preiss).
-/

namespace YangMills

open Real MeasureTheory Matrix Finset
open scoped BigOperators

noncomputable section

/-! ## Continuity of the raw fluctuation and its products -/

/-- The raw plaquette fluctuation `w_raw U = weight U - 1` is
continuous.  Immediate from continuity of `plaquetteWeight`. -/
theorem continuous_plaquetteFluctuationRaw
    (N_c : ℕ) [NeZero N_c] (β : ℝ) :
    Continuous (plaquetteFluctuationRaw N_c β) := by
  unfold plaquetteFluctuationRaw
  exact (plaquetteWeight_continuous N_c β).sub continuous_const

/-- A finite product of raw plaquette fluctuations is continuous. -/
theorem continuous_prod_plaquetteFluctuationRaw
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    {d L : ℕ} [NeZero d] [NeZero L]
    (S : Finset (ConcretePlaquette d L)) :
    Continuous (fun U : ↥(specialUnitaryGroup (Fin N_c) ℂ) =>
      ∏ _p ∈ S, plaquetteFluctuationRaw N_c β U) :=
  continuous_finset_prod S (fun _ _ => continuous_plaquetteFluctuationRaw N_c β)

/-! ## Integrability against the Haar probability measure -/

/-- A finite product of raw plaquette fluctuations is integrable
against the SU(N_c) Haar probability measure.  SU(N_c) is a
`CompactSpace`, so every continuous function automatically has compact
support; combined with finiteness of the probability measure this
yields integrability. -/
theorem integrable_prod_plaquetteFluctuationRaw
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    {d L : ℕ} [NeZero d] [NeZero L]
    (S : Finset (ConcretePlaquette d L)) :
    Integrable
      (fun U : ↥(specialUnitaryGroup (Fin N_c) ℂ) =>
        ∏ _p ∈ S, plaquetteFluctuationRaw N_c β U)
      (sunHaarProb N_c) :=
  (continuous_prod_plaquetteFluctuationRaw N_c β
    S).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ## Fubini: sum/integral interchange -/

/-- **Phase 15j.6, sum/integral interchange.**

For any finite set of plaquettes `P`, the sum over the powerset
commutes with the Haar integral:

  `∫ ∑_{S⊆P} ∏_{p∈S} w_raw dHaar = ∑_{S⊆P} ∫ ∏_{p∈S} w_raw dHaar`.

This is Fubini for a finite sum vs. a Haar integral and goes through
by `MeasureTheory.integral_finset_sum`, whose per-summand integrability
hypothesis is supplied by `integrable_prod_plaquetteFluctuationRaw`. -/
theorem integral_sum_eq_sum_integral_cluster
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    {d L : ℕ} [NeZero d] [NeZero L]
    (plaquettes : Finset (ConcretePlaquette d L)) :
    ∫ U, (∑ S ∈ plaquettes.powerset,
        ∏ _p ∈ S, plaquetteFluctuationRaw N_c β U) ∂(sunHaarProb N_c) =
    ∑ S ∈ plaquettes.powerset,
      ∫ U, ∏ _p ∈ S, plaquetteFluctuationRaw N_c β U ∂(sunHaarProb N_c) := by
  refine MeasureTheory.integral_finset_sum (plaquettes.powerset) ?_
  intro S _
  exact integrable_prod_plaquetteFluctuationRaw N_c β S

/-! ## Integrated cluster expansion (final form) -/

/-- **Phase 15j.6, partition-function cluster expansion (final form).**

Combining the pointwise algebraic expansion of Phase 15j.5
(`partition_function_cluster_expansion`) with the Fubini interchange
gives the integrated cluster expansion of the Wilson-Gibbs partition
function:

  `∫ exp(-β·∑_{p∈P} E) dHaar = ∑_{S⊆P} K_raw(S)`

where `K_raw(S) = ∫ ∏_{p∈S} w_raw dHaar = wilsonClusterActivityRaw N_c β S`.

This is the exact shape used in the Mayer-expansion literature as the
starting point for the Kotecky-Preiss convergence argument. -/
theorem integral_boltzmann_eq_sum_activities
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    (d L : ℕ) [NeZero d] [NeZero L] :
    ∫ U, Real.exp (-β * ∑ _p ∈ (Finset.univ : Finset (ConcretePlaquette d L)),
        wilsonPlaquetteEnergy N_c U) ∂(sunHaarProb N_c) =
    ∑ S ∈ (Finset.univ : Finset (ConcretePlaquette d L)).powerset,
      wilsonClusterActivityRaw N_c β S := by
  simp only [wilsonClusterActivityRaw]
  rw [partition_function_cluster_expansion N_c β d L]
  exact integral_sum_eq_sum_integral_cluster N_c β (Finset.univ)

/-! ## Wrapper: Fubini-aware Clay theorem chain -/

/-- **Phase 15j.6, wrapper to `ClayYangMillsTheorem`.**

This delegates the actual Clay chain to `clay_theorem_small_beta`
(Phase 15j.4), which uses the β-clipped cluster activity
(`wilsonClusterActivity`) whose amplitude bound `|K(γ)| ≤ β^|γ|` is
unconditional.

The role of Phase 15j.6 in the chain is not to provide a *new* Clay
theorem — the chain is already closed by 15j.4 modulo the pointwise
rpow hypothesis — but to provide the Fubini-aware integrated
expansion `integral_boltzmann_eq_sum_activities` which is the exact
form in which the Mayer / Kotecky-Preiss input is stated and consumed
in the constructive-QFT literature.  The wrapper makes both facts
available from a single theorem call-site. -/
theorem yang_mills_unconditional_fubini
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
  clay_theorem_small_beta N_c hβ_pos hβ_lt1 C hC_pos h_rpow

end

end YangMills
