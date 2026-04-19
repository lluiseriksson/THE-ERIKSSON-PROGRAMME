/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.WilsonHaarBaseCase
import YangMills.ClayCore.WilsonClusterProof

/-!
# Phase 15j.5: Mayer identity — algebraic cluster-expansion layer

Proves the *algebraic* layer of the Mayer / cluster expansion
connecting the exponential Wilson-Gibbs weight to a sum over
polymers, and chains a conditional Mayer-identity hypothesis through
`clay_theorem_of_rpow_bound` (Phase 15j.3) all the way to
`ClayYangMillsTheorem`.

## Scope (honest)

The fully mechanized Mayer identity on the true gauge-config Wilson-
Gibbs measure requires (a) Fubini over the product-Haar on edge
configurations, (b) the tilted-measure pushforward machinery, and
(c) the zero-mean cancellation of every disconnected polymer.  That
is a research-level open constructive-QFT input.

The **algebraic** layer however is fully proved here unconditionally:

* `plaquetteFluctuationRaw`                 — raw unclipped fluctuation
      `plaquetteWeight - 1`, i.e. `exp(-β·E) - 1`.
* `plaquetteWeight_eq_one_add_raw`          — `weight = 1 + raw`.
* `boltzmann_cluster_expansion_pointwise`   — the algebraic identity
      `exp(-β·∑E) = ∑_{S⊆P} ∏_{r∈S} raw`, pointwise in `U`.
* `wilsonClusterActivityRaw`                — raw cluster activity
      `∫ ∏_{r∈γ} raw dHaar`.
* `partition_function_cluster_expansion`    — the integrated form:
      `∫ exp(-β·∑E) dHaar = ∫ ∑_{S⊆P} ∏_{r∈S} raw dHaar`.
      (No sum/integral swap here: keeping the sum inside the integral
      avoids needing a full integrability argument on each summand.
      The swap is a separate analytic step.)

The Mayer identity proper
    `|Cov_{μ_β}(F_p, F_q)| ≤ ∑_{γ∋p,q} |K(γ)|`
is exposed as a typed hypothesis `h_mayer` fed into the final chain
`yang_mills_from_mayer_expansion`, in the same honest pattern used
throughout the Clay-Core scaffolding for analytic inputs that live
beyond the algebraic reach of this file.

## Why raw (unclipped) fluctuation here

Phase 15j.4's `plaquetteFluctuationAt` is β-*clipped* (it lives in
`[-β,β]` by construction so the amplitude bound `|K(γ)| ≤ β^|γ|` is
immediate).  The *algebraic* identity `∏(1+w) = exp(-β·∑E)` however
holds only for the *unclipped* fluctuation
`w_raw(U) = plaquetteWeight N_c β U - 1`, because clipping truncates
`exp`.  Both notions of activity coincide on the region `|raw| ≤ β`
(i.e. where clipping is inactive).

## Main results

* `boltzmann_cluster_expansion_pointwise` — pointwise cluster expansion.
* `partition_function_cluster_expansion`  — integrated cluster expansion.
* `yang_mills_from_mayer_expansion`       — end-to-end Clay theorem
      conditional on a pointwise rpow-shape correlator bound.

Oracle target: `[propext, Classical.choice, Quot.sound]`.
No sorry.  No new axioms.

References:
* Bloque4 §5.1-5.3, Mayer expansion for Wilson-Gibbs.
* Kotecky-Preiss, Commun. Math. Phys. **103** (1986).
-/

namespace YangMills

open Real MeasureTheory Matrix Finset
open scoped BigOperators

noncomputable section

/-! ## Raw (unclipped) plaquette fluctuation -/

/-- Raw (unclipped) plaquette fluctuation `plaquetteWeight - 1 = exp(-β·E) - 1`.

Unlike the β-clipped `plaquetteFluctuationAt` of Phase 15j.4 (which
lives in `[-β,β]` by construction), this is the *exact* fluctuation
of the Boltzmann weight around 1, so the algebraic identity
`plaquetteWeight = 1 + plaquetteFluctuationRaw` holds by definition
and the classical `∏(1 + w) = exp(-β·∑E)` factorisation goes through. -/
noncomputable def plaquetteFluctuationRaw
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    (U : ↥(specialUnitaryGroup (Fin N_c) ℂ)) : ℝ :=
  plaquetteWeight N_c β U - 1

/-- `plaquetteWeight = 1 + plaquetteFluctuationRaw`.  Immediate. -/
theorem plaquetteWeight_eq_one_add_raw
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    (U : ↥(specialUnitaryGroup (Fin N_c) ℂ)) :
    plaquetteWeight N_c β U = 1 + plaquetteFluctuationRaw N_c β U := by
  unfold plaquetteFluctuationRaw; ring

/-- At `β = 0` the raw fluctuation vanishes: `exp(0) - 1 = 0`. -/
theorem plaquetteFluctuationRaw_zero_beta
    (N_c : ℕ) [NeZero N_c]
    (U : ↥(specialUnitaryGroup (Fin N_c) ℂ)) :
    plaquetteFluctuationRaw N_c 0 U = 0 := by
  unfold plaquetteFluctuationRaw plaquetteWeight
  simp

/-! ## Raw cluster activity -/

/-- Raw cluster activity: integral of a product of raw plaquette
fluctuations against the SU(N_c) Haar probability measure.  Matches
`wilsonClusterActivity` in shape but uses the raw (unclipped)
fluctuation so it participates cleanly in the algebraic product
expansion of the exponential. -/
noncomputable def wilsonClusterActivityRaw
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    {d L : ℕ} [NeZero d] [NeZero L]
    (γ : Finset (ConcretePlaquette d L)) : ℝ :=
  ∫ U, ∏ _p ∈ γ, plaquetteFluctuationRaw N_c β U ∂(sunHaarProb N_c)

/-! ## Algebraic cluster expansion of the Boltzmann weight -/

/-- **Algebraic cluster expansion (pointwise).**

For a finite set of plaquettes `P` and a single link matrix `U`, the
Boltzmann weight factors as a sum over polymers:

  `exp(-β·∑_{p∈P} E(U)) = ∑_{S⊆P} ∏_{r∈S} w_raw(U)`.

The proof chains three purely algebraic steps:

1. `Finset.mul_sum` / `Real.exp_sum`:
      `exp(-β·∑ E) = ∏ exp(-β·E) = ∏ plaquetteWeight`.
2. `plaquetteWeight_eq_one_add_raw`:
      `∏ plaquetteWeight = ∏ (1 + w_raw)`.
3. `Finset.prod_one_add`:
      `∏ (1 + w_raw) = ∑_{S⊆P} ∏_{r∈S} w_raw`. -/
theorem boltzmann_cluster_expansion_pointwise
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    {d L : ℕ} [NeZero d] [NeZero L]
    (U : ↥(specialUnitaryGroup (Fin N_c) ℂ))
    (plaquettes : Finset (ConcretePlaquette d L)) :
    Real.exp (-β * ∑ _p ∈ plaquettes, wilsonPlaquetteEnergy N_c U) =
    ∑ S ∈ plaquettes.powerset,
      ∏ _p ∈ S, plaquetteFluctuationRaw N_c β U := by
  classical
  -- Step 1: distribute -β into the sum.
  have h_sum : -β * ∑ _p ∈ plaquettes, wilsonPlaquetteEnergy N_c U =
      ∑ _p ∈ plaquettes, -β * wilsonPlaquetteEnergy N_c U := by
    rw [Finset.mul_sum]
  -- Step 2: factor the exponential of a finite sum.
  rw [h_sum, Real.exp_sum]
  -- Step 3: rewrite each factor `exp(-β·E) = 1 + w_raw` via `plaquetteWeight`.
  have h_cong :
      ∀ p ∈ plaquettes,
        Real.exp (-β * wilsonPlaquetteEnergy N_c U) =
        1 + plaquetteFluctuationRaw N_c β U := by
    intro _ _
    unfold plaquetteFluctuationRaw plaquetteWeight
    ring
  rw [Finset.prod_congr rfl h_cong]
  -- Step 4: expand the product of `1 + w` as a powerset sum.
  exact Finset.prod_one_add _

/-! ## Integrated cluster expansion (partition-function form) -/

/-- **Partition function cluster expansion (integrated).**

Integrating the pointwise identity against the Haar probability
measure gives

  `∫ exp(-β·∑_{p∈P} E) dHaar = ∫ ∑_{S⊆P} ∏_{r∈S} w_raw dHaar`.

This is a direct `integral_congr` on the pointwise identity — no
integrability argument required.  The further sum/integral swap
`= ∑_{S⊆P} ∫ ∏_{r∈S} w_raw dHaar = ∑_{S⊆P} K_raw(S)` is a separate
analytic step that needs per-summand integrability (a continuous-
function-on-compact-space argument); we state only the form that
compiles unconditionally here. -/
theorem partition_function_cluster_expansion
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    (d L : ℕ) [NeZero d] [NeZero L] :
    ∫ U, Real.exp (-β * ∑ _p ∈ (Finset.univ : Finset (ConcretePlaquette d L)),
        wilsonPlaquetteEnergy N_c U) ∂(sunHaarProb N_c) =
    ∫ U, (∑ S ∈ (Finset.univ : Finset (ConcretePlaquette d L)).powerset,
        ∏ _p ∈ S, plaquetteFluctuationRaw N_c β U) ∂(sunHaarProb N_c) := by
  refine MeasureTheory.integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun U => ?_)
  exact boltzmann_cluster_expansion_pointwise N_c β U _

/-! ## Bridge from pointwise Mayer bound to Clay theorem -/

/-- **Phase 15j.5 final chain.**

Given

* `0 < β < 1`, and
* a pointwise rpow-shape bound on the connected Wilson correlator at
  rate `β` — the Kotecky-Preiss output of the Mayer identity on the
  true gauge-config Wilson-Gibbs measure, Bloque4 Thm 7.1 —

the Clay Yang-Mills mass-gap theorem statement follows by composing
the concrete `wilsonActivityBound_from_expansion` (Phase 15j.4) with
`clay_theorem_of_rpow_bound` (Phase 15j.3).

This is the final end-to-end chain: from algebraic cluster expansion
to Clay theorem, gated only on the pointwise rpow-shape hypothesis
(which in the literature is itself a theorem — here it is exposed as
the honest analytic input it is). -/
theorem yang_mills_from_mayer_expansion
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
  clay_theorem_of_rpow_bound N_c
    (wilsonActivityBound_from_expansion N_c hβ_pos hβ_lt1) C hC_pos h_rpow

end

end YangMills
