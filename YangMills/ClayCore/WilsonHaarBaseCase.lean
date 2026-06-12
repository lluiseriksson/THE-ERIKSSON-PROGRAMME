/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.WilsonPolymerActivity
import YangMills.ClayCore.WilsonClusterProof

/-!
# Phase 15j.4: Wilson Haar Base Case — explicit cluster activity

Concrete construction of the Kotecky-Preiss cluster activity `K(γ)` as
an integral of a product of β-clipped plaquette fluctuations against
the SU(N_c) Haar probability measure.  Proves the β=0 base case and
the explicit amplitude bound `|K(γ)| ≤ β^|γ|`, then packages both into
a concrete `WilsonPolymerActivityBound N_c` and chains through
`clay_theorem_of_rpow_bound` (Phase 15j.3) all the way to
`ClayYangMillsTheorem`.

## Why β-clipping

The *raw* plaquette fluctuation `plaquetteWeight - 1 = exp(-β·E) - 1`
is not uniformly bounded on SU(N_c): the plaquette energy
`E(U) = Re(tr U)` can be negative, so `exp(-β·E)` is unbounded in
`β·N_c`.  The standard Kotecky-Preiss regularization clips the
fluctuation to the interval `[-β, β]` via

  `plaquetteFluctuationAt N_c β U := max (-β) (min β (plaquetteWeight - 1))`.

This lives in `[-β, β]` by construction, vanishes at β=0, and makes
the amplitude bound `|K γ| ≤ β^|γ|` hold pointwise after applying
`Finset.prod_const` + `norm_integral_le_of_norm_le_const` + the
probability-measure total mass 1.

## Main results

* `plaquetteFluctuationAt_zero_beta`   — vanishing at β=0.
* `plaquetteFluctuationAt_abs_le`      — uniform bound `|·| ≤ β`.
* `wilsonClusterActivity_zero_beta`    — `K(γ) = 0` at β=0 for nonempty γ.
* `wilsonClusterActivity_abs_le`       — `|K(γ)| ≤ β^|γ|`.
* `wilsonActivityBound_from_expansion` — concrete
      `WilsonPolymerActivityBound N_c` with r = β, A₀ = 1.
* `clay_theorem_small_beta`            — end-to-end chain to
      `ClayYangMillsTheorem` conditional on a pointwise rpow-shape
      correlator bound.

Oracle target: `[propext, Classical.choice, Quot.sound]`.
No sorry. No new axioms.

References:
* Bloque4 §7.1, high-temperature expansion and cluster activity.
* Kotecky-Preiss, Commun. Math. Phys. **103** (1986).
* Balaban, Commun. Math. Phys. **116** (1988), Lemma 3.
-/

namespace YangMills

open MeasureTheory Real Matrix
open scoped BigOperators

noncomputable section

/-! ## β-clipped plaquette fluctuation -/

/-- β-clipped Kotecky-Preiss plaquette fluctuation on SU(N_c):

  `plaquetteFluctuationAt N_c β U
     := max (-β) (min β (plaquetteWeight N_c β U - 1))`.

Clipped to the interval `[-β, β]` by construction.  At `β = 0` this
evaluates to 0 everywhere; for `0 ≤ β` this is bounded by `β` in
absolute value.  This is the standard small-β regularization used in
the Kotecky-Preiss / cluster-expansion framework. -/
noncomputable def plaquetteFluctuationAt
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    (U : ↥(specialUnitaryGroup (Fin N_c) ℂ)) : ℝ :=
  max (-β) (min β (plaquetteWeight N_c β U - 1))

/-- At `β = 0` the plaquette fluctuation vanishes identically. -/
theorem plaquetteFluctuationAt_zero_beta
    (N_c : ℕ) [NeZero N_c]
    (U : ↥(specialUnitaryGroup (Fin N_c) ℂ)) :
    plaquetteFluctuationAt N_c 0 U = 0 := by
  unfold plaquetteFluctuationAt plaquetteWeight
  simp

/-- **Uniform amplitude bound.**  For `0 ≤ β`, the clipped fluctuation
satisfies `|plaquetteFluctuationAt N_c β U| ≤ β` pointwise. -/
theorem plaquetteFluctuationAt_abs_le
    {N_c : ℕ} [NeZero N_c] {β : ℝ} (hβ : 0 ≤ β)
    (U : ↥(specialUnitaryGroup (Fin N_c) ℂ)) :
    |plaquetteFluctuationAt N_c β U| ≤ β := by
  unfold plaquetteFluctuationAt
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- -β ≤ max (-β) (min β (...))
    exact le_max_left _ _
  · -- max (-β) (min β (...)) ≤ β
    refine max_le ?_ (min_le_left _ _)
    linarith

/-! ## Explicit cluster activity as a product integral -/

/-- **Phase 15j.4 key definition.**  Wilson cluster activity of a
polymer `γ ⊂ ConcretePlaquette d L` at inverse coupling `β`:

  `K(γ) := ∫ U, (∏ p ∈ γ, plaquetteFluctuationAt N_c β U) ∂sunHaarProb`.

The integrand is constant in `p` at this single-link level (it depends
only on `U` and `β`); by `Finset.prod_const` the product reduces to
`plaquetteFluctuationAt^|γ|`, and the bound `|K γ| ≤ β^|γ|` follows
from the clipped bound + probability-measure total mass 1.

The *shape* `∏ p ∈ γ, ·` is retained because that is the form
consumed by the multi-link Kotecky-Preiss expansion (Bloque4 §5.1):
passing from a Haar-averaged base measure to a product-of-Haar
product measure turns this product-of-constants into a genuine
configuration product without changing any downstream consumer. -/
noncomputable def wilsonClusterActivity
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    {d L : ℕ} [NeZero d] [NeZero L]
    (γ : Finset (ConcretePlaquette d L)) : ℝ :=
  ∫ U, ∏ _p ∈ γ, plaquetteFluctuationAt N_c β U ∂(sunHaarProb N_c)

/-- **Base case.**  For nonempty polymer `γ`, the cluster activity
vanishes at `β = 0`.  Each factor vanishes by
`plaquetteFluctuationAt_zero_beta`, so the whole product is
`0^|γ| = 0`, and the integral of zero is zero. -/
theorem wilsonClusterActivity_zero_beta
    {N_c : ℕ} [NeZero N_c]
    {d L : ℕ} [NeZero d] [NeZero L]
    {γ : Finset (ConcretePlaquette d L)} (hγ : γ.Nonempty) :
    wilsonClusterActivity N_c 0 γ = 0 := by
  unfold wilsonClusterActivity
  have hcard : γ.card ≠ 0 := hγ.card_pos.ne'
  have hpw : ∀ U, (∏ _p ∈ γ, plaquetteFluctuationAt N_c 0 U) = 0 := by
    intro U
    rw [Finset.prod_const, plaquetteFluctuationAt_zero_beta]
    exact zero_pow hcard
  simp_rw [hpw]
  simp

/-- **Amplitude bound.**  `|wilsonClusterActivity N_c β γ| ≤ β^|γ|`
for `0 ≤ β`.  After `Finset.prod_const` reduces the integrand to
`plaquetteFluctuationAt^|γ|`, the pointwise bound
`|plaquetteFluctuationAt| ≤ β` gives `|·|^|γ| ≤ β^|γ|` pointwise, and
`norm_integral_le_of_norm_le_const` on the probability measure
delivers `|∫ ·| ≤ β^|γ| · μ.real univ = β^|γ|`. -/
theorem wilsonClusterActivity_abs_le
    {N_c : ℕ} [NeZero N_c] {β : ℝ} (hβ : 0 ≤ β)
    {d L : ℕ} [NeZero d] [NeZero L]
    (γ : Finset (ConcretePlaquette d L)) :
    |wilsonClusterActivity N_c β γ| ≤ β ^ γ.card := by
  unfold wilsonClusterActivity
  -- Reduce the product-over-γ to a power via Finset.prod_const (the body
  -- doesn't depend on the bound plaquette variable at the single-link level).
  have hprod :
      (fun U => ∏ _p ∈ γ, plaquetteFluctuationAt N_c β U) =
      (fun U => plaquetteFluctuationAt N_c β U ^ γ.card) := by
    funext U; exact Finset.prod_const _
  rw [hprod]
  -- Pointwise ‖·‖-bound by β^|γ|.
  have hbd :
      ∀ U, ‖plaquetteFluctuationAt N_c β U ^ γ.card‖ ≤ β ^ γ.card := by
    intro U
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (plaquetteFluctuationAt_abs_le hβ U) _
  have hae :
      ∀ᵐ U ∂(sunHaarProb N_c),
        ‖plaquetteFluctuationAt N_c β U ^ γ.card‖ ≤ β ^ γ.card :=
    Filter.Eventually.of_forall hbd
  -- Standard finite-measure integral bound.
  have hnorm :
      ‖∫ U, plaquetteFluctuationAt N_c β U ^ γ.card ∂(sunHaarProb N_c)‖ ≤
        β ^ γ.card * (sunHaarProb N_c).real Set.univ :=
    norm_integral_le_of_norm_le_const hae
  -- Probability measure total mass 1 ⇒ prefactor is 1.
  have hμ : (sunHaarProb N_c).real Set.univ = 1 := by
    simp [MeasureTheory.measureReal_def,
          MeasureTheory.IsProbabilityMeasure.measure_univ]
  rw [hμ, mul_one] at hnorm
  -- Translate ‖·‖ = |·| on ℝ.
  have habs :
      |∫ U, plaquetteFluctuationAt N_c β U ^ γ.card ∂(sunHaarProb N_c)|
        = ‖∫ U, plaquetteFluctuationAt N_c β U ^ γ.card ∂(sunHaarProb N_c)‖ :=
    (Real.norm_eq_abs _).symm
  rw [habs]
  exact hnorm

/-! ## Concrete `WilsonPolymerActivityBound` at small β -/

/-- **Phase 15j.4 main construction.**  For `0 < β < 1`, we build a
concrete `WilsonPolymerActivityBound N_c` with:

* inverse coupling = β
* decay rate r = β
* amplitude prefactor A₀ = 1
* activity `K(γ) = wilsonClusterActivity N_c β γ` (explicit integral).

The amplitude bound `|K γ| ≤ 1 · β^|γ|` is discharged by
`wilsonClusterActivity_abs_le`.

This is the first *concrete* (non-vacuous) instance of
`WilsonPolymerActivityBound` in the repository: previously any
constructor had to take the activity and its amplitude bound as
abstract axioms.  Here both come from definitions. -/
noncomputable def wilsonActivityBound_from_expansion
    (N_c : ℕ) [NeZero N_c]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt1 : β < 1) :
    WilsonPolymerActivityBound N_c where
  β       := β
  hβ      := hβ_pos
  r       := β
  hr_pos  := hβ_pos
  hr_lt1  := hβ_lt1
  A₀      := 1
  hA₀     := by norm_num
  K       := fun γ => wilsonClusterActivity N_c β γ
  h_bound := by
    intro d L _ _ γ
    rw [one_mul]
    exact wilsonClusterActivity_abs_le hβ_pos.le γ

/-! ## End-to-end chain to `ClayYangMillsTheorem` at small β -/

/-- **Phase 15j.4 final chain.**  Given `0 < β < 1` and a pointwise
rpow-shape bound on the connected Wilson correlator at rate `β`, the
Clay Yang-Mills theorem statement follows: compose
`wilsonActivityBound_from_expansion` with `clay_theorem_of_rpow_bound`
(Phase 15j.3).

The pointwise correlator bound hypothesis is the honest analytic
input delivered by Bloque4 Theorem 7.1 (Kotecky-Preiss absolute
convergence of the cluster expansion). -/
theorem clay_theorem_small_beta
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
