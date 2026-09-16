/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116WeakenedRandomWalkSeries
import YangMills.RG.BalabanCMP116Eq214CauchyPolydisc

/-!
# CMP116 complex weakened random-walk series

Equation (2.14) applies Cauchy extraction to complex weakening parameters.
The previously constructed random-walk series used real weakening parameters,
as required by the real FTC decoupling argument.  This module supplies the
parallel complex layer without changing that real construction.

The primary domain is the coordinatewise shifted polydisc

`‖sigma d‖ ≤ 1 + radius d`,

which is the actual domain traversed by the source Cauchy circles.  A uniform
cap `1 + radius d ≤ R` on the active carrier converts this source-faithful
bound into the radial majorant already produced by the physical walk
estimates.  The resulting series is exactly affine, hence holomorphic, in
each weakening coordinate.  No differentiation-under-an-infinite-sum theorem
is used.

Honest scope: this file complexifies the weakening scalars and accepts terms
in an already complex normed space.  The source-specific identification of
those terms with the complex CMP116 propagators is a subsequent layer.
-/

open scoped BigOperators

namespace YangMills.RG

universe u v w

variable {Δ : Type u} {ω : Type v} {E : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex weakening monomial attached to one active carrier. -/
def cmp116ComplexWeakeningMonomial
    (active : Finset Δ) (sigma : Δ → ℂ) : ℂ :=
  ∏ d ∈ active, sigma d

/-- The complex weakening monomial restricts exactly to the previous real
monomial on real weakening parameters. -/
@[simp] theorem cmp116ComplexWeakeningMonomial_ofReal
    (active : Finset Δ) (s : Δ → ℝ) :
    cmp116ComplexWeakeningMonomial active (fun d => (s d : ℂ)) =
      (cmp116WeakeningMonomial active s : ℂ) := by
  simp [cmp116ComplexWeakeningMonomial, cmp116WeakeningMonomial,
    Complex.ofReal_prod]

/-- The coordinatewise shifted polydisc traversed by the complex weakening
contours. -/
def cmp116ComplexShiftedWeakeningPolydisc
    (radius : Δ → ℝ) : Set (Δ → ℂ) :=
  {sigma | ∀ d, ‖sigma d‖ ≤ 1 + radius d}

/-- The norm of a complex weakening monomial is bounded by the literal
product of its coordinatewise shifted radii. -/
theorem norm_cmp116ComplexWeakeningMonomial_le_prod
    (active : Finset Δ) (sigma : Δ → ℂ) (radius : Δ → ℝ)
    (hsigma : ∀ d ∈ active, ‖sigma d‖ ≤ 1 + radius d) :
    ‖cmp116ComplexWeakeningMonomial active sigma‖ ≤
      ∏ d ∈ active, (1 + radius d) := by
  rw [cmp116ComplexWeakeningMonomial, norm_prod]
  exact Finset.prod_le_prod
    (fun d _ => norm_nonneg (sigma d))
    hsigma

/-- A uniform cap on the shifted radii over the active carrier gives the
radial power majorant used by the physical walk estimates. -/
theorem norm_cmp116ComplexWeakeningMonomial_le_pow_card
    (active : Finset Δ) (sigma : Δ → ℂ) (radius : Δ → ℝ) (R : ℝ)
    (hR : 0 ≤ R)
    (hsigma : ∀ d ∈ active, ‖sigma d‖ ≤ 1 + radius d)
    (hcap : ∀ d ∈ active, 1 + radius d ≤ R) :
    ‖cmp116ComplexWeakeningMonomial active sigma‖ ≤ R ^ active.card := by
  classical
  induction active using Finset.induction_on with
  | empty => simp [cmp116ComplexWeakeningMonomial]
  | @insert d active hd ih =>
      rw [cmp116ComplexWeakeningMonomial, Finset.prod_insert hd, norm_mul,
        Finset.card_insert_of_notMem hd, pow_succ]
      simpa [cmp116ComplexWeakeningMonomial, mul_comm] using mul_le_mul
        ((hsigma d (Finset.mem_insert_self d active)).trans
          (hcap d (Finset.mem_insert_self d active)))
        (ih
          (fun x hx => hsigma x (Finset.mem_insert_of_mem hx))
          (fun x hx => hcap x (Finset.mem_insert_of_mem hx)))
        (norm_nonneg _) hR

/-- The countable complex weakened random-walk series. -/
noncomputable def cmp116ComplexWeakenedRandomWalkSeries
    (active : ω → Finset Δ) (term : ω → E) (sigma : Δ → ℂ) : E :=
  ∑' walk, cmp116ComplexWeakeningMonomial (active walk) sigma • term walk

/-- One complex weakened term is controlled by the real radial majorant. -/
theorem norm_cmp116ComplexWeakeningTerm_le_radialMajorant
    (active : Finset Δ) (term : E) (sigma : Δ → ℂ)
    (radius : Δ → ℝ) (R : ℝ)
    (hR : 0 ≤ R)
    (hsigma : sigma ∈ cmp116ComplexShiftedWeakeningPolydisc radius)
    (hcap : ∀ d ∈ active, 1 + radius d ≤ R) :
    ‖cmp116ComplexWeakeningMonomial active sigma • term‖ ≤
      R ^ active.card * ‖term‖ := by
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right
    (norm_cmp116ComplexWeakeningMonomial_le_pow_card
      active sigma radius R hR (fun d _ => hsigma d) hcap)
    (norm_nonneg term)

/-- The physical radial majorant makes the complex weakened family summable
at every point of the shifted polydisc. -/
theorem summable_cmp116ComplexWeakenedRandomWalkSeries
    [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E) (sigma : Δ → ℂ)
    (radius : Δ → ℝ) (R : ℝ)
    (hR : 0 ≤ R)
    (hsigma : sigma ∈ cmp116ComplexShiftedWeakeningPolydisc radius)
    (hcap : ∀ walk d, d ∈ active walk → 1 + radius d ≤ R)
    (hmajor : Summable fun walk => R ^ (active walk).card * ‖term walk‖) :
    Summable fun walk =>
      cmp116ComplexWeakeningMonomial (active walk) sigma • term walk :=
  Summable.of_norm_bounded hmajor fun walk =>
    norm_cmp116ComplexWeakeningTerm_le_radialMajorant
      (active walk) (term walk) sigma radius R hR hsigma
      (hcap walk)

/-- The same majorant gives the uniform norm bound consumed by the Cauchy
boundary estimate. -/
theorem norm_cmp116ComplexWeakenedRandomWalkSeries_le_tsum_majorant
    [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E) (sigma : Δ → ℂ)
    (radius : Δ → ℝ) (R : ℝ)
    (hR : 0 ≤ R)
    (hsigma : sigma ∈ cmp116ComplexShiftedWeakeningPolydisc radius)
    (hcap : ∀ walk d, d ∈ active walk → 1 + radius d ≤ R)
    (hmajor : Summable fun walk => R ^ (active walk).card * ‖term walk‖) :
    ‖cmp116ComplexWeakenedRandomWalkSeries active term sigma‖ ≤
      ∑' walk, R ^ (active walk).card * ‖term walk‖ := by
  have hnorm : Summable fun walk =>
      ‖cmp116ComplexWeakeningMonomial (active walk) sigma • term walk‖ :=
    Summable.of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun walk => norm_cmp116ComplexWeakeningTerm_le_radialMajorant
        (active walk) (term walk) sigma radius R hR hsigma (hcap walk))
      hmajor
  rw [cmp116ComplexWeakenedRandomWalkSeries]
  exact (norm_tsum_le_tsum_norm hnorm).trans
    (Summable.tsum_le_tsum
      (fun walk => norm_cmp116ComplexWeakeningTerm_le_radialMajorant
        (active walk) (term walk) sigma radius R hR hsigma (hcap walk))
      hnorm hmajor)

/-- At the fully coupled point the complex weakened series is the original
walk `tsum`. -/
theorem cmp116ComplexWeakenedRandomWalkSeries_one
    (active : ω → Finset Δ) (term : ω → E) :
    cmp116ComplexWeakenedRandomWalkSeries active term (fun _ => 1) =
      ∑' walk, term walk := by
  rw [cmp116ComplexWeakenedRandomWalkSeries]
  apply tsum_congr
  intro walk
  simp [cmp116ComplexWeakeningMonomial]

section DecidableCubes

variable [DecidableEq Δ]

/-- Updating an active complex weakening coordinate exposes that coordinate
as one linear factor. -/
theorem cmp116ComplexWeakeningMonomial_update_of_mem
    (active : Finset Δ) (sigma : Δ → ℂ) (d : Δ)
    (hd : d ∈ active) (t : ℂ) :
    cmp116ComplexWeakeningMonomial active (Function.update sigma d t) =
      t * cmp116ComplexWeakeningMonomial (active.erase d) sigma := by
  calc
    cmp116ComplexWeakeningMonomial active (Function.update sigma d t) =
        Function.update sigma d t d *
          ∏ x ∈ active \ {d}, Function.update sigma d t x := by
      exact Finset.prod_eq_mul_prod_diff_singleton_of_mem hd _
    _ = t * ∏ x ∈ active \ {d}, sigma x := by
      rw [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro x hx
      rw [Function.update_of_ne]
      simpa using (Finset.mem_sdiff.mp hx).2
    _ = t * cmp116ComplexWeakeningMonomial (active.erase d) sigma := by
      simp [cmp116ComplexWeakeningMonomial, Finset.erase_eq]

/-- Updating an inactive complex weakening coordinate leaves the monomial
unchanged. -/
theorem cmp116ComplexWeakeningMonomial_update_of_not_mem
    (active : Finset Δ) (sigma : Δ → ℂ) (d : Δ)
    (hd : d ∉ active) (t : ℂ) :
    cmp116ComplexWeakeningMonomial active (Function.update sigma d t) =
      cmp116ComplexWeakeningMonomial active sigma := by
  simp only [cmp116ComplexWeakeningMonomial]
  apply Finset.prod_congr rfl
  intro x hx
  rw [Function.update_of_ne (ne_of_mem_of_not_mem hx hd)]

/-- The real zero-outside weakening system, embedded in the complex scalar
field, restricts a complex monomial to the same active-carrier indicator. -/
theorem cmp116ComplexWeakeningMonomial_zeroOutside
    (active K : Finset Δ) :
    cmp116ComplexWeakeningMonomial active
        (fun d => (cmp116WeakeningZeroOutside K d : ℂ)) =
      if active ⊆ K then 1 else 0 := by
  calc
    cmp116ComplexWeakeningMonomial active
        (fun d => (cmp116WeakeningZeroOutside K d : ℂ)) =
        (cmp116WeakeningMonomial active
          (cmp116WeakeningZeroOutside K) : ℂ) :=
      cmp116ComplexWeakeningMonomial_ofReal active
        (cmp116WeakeningZeroOutside K)
    _ = ((if active ⊆ K then 1 else 0 : ℝ) : ℂ) := by
      rw [cmp116WeakeningMonomial_zeroOutside]
    _ = if active ⊆ K then 1 else 0 := by
      split_ifs <;> simp

/-- Zeroing complex weakening coordinates outside `K` restricts the infinite
series exactly to walks supported in `K`. -/
theorem cmp116ComplexWeakenedRandomWalkSeries_zeroOutside
    (active : ω → Finset Δ) (term : ω → E) (K : Finset Δ) :
    cmp116ComplexWeakenedRandomWalkSeries active term
        (fun d => (cmp116WeakeningZeroOutside K d : ℂ)) =
      ∑' walk : {walk // active walk ⊆ K}, term walk := by
  rw [cmp116ComplexWeakenedRandomWalkSeries]
  calc
    (∑' walk,
      cmp116ComplexWeakeningMonomial (active walk)
        (fun d => (cmp116WeakeningZeroOutside K d : ℂ)) • term walk) =
        ∑' walk, Set.indicator {walk | active walk ⊆ K} term walk := by
      apply tsum_congr
      intro walk
      rw [Set.indicator_apply]
      by_cases h : active walk ⊆ K
      · rw [cmp116ComplexWeakeningMonomial_zeroOutside]
        simp [h]
      · rw [cmp116ComplexWeakeningMonomial_zeroOutside]
        simp [h]
    _ = ∑' walk : {walk // active walk ⊆ K}, term walk :=
      (tsum_subtype {walk | active walk ⊆ K} term).symm

/-- The coordinate derivative series for complex weakening parameters. -/
noncomputable def cmp116ComplexWeakenedRandomWalkSeriesDerivative
    (active : ω → Finset Δ) (term : ω → E)
    (sigma : Δ → ℂ) (d : Δ) : E :=
  ∑' walk,
    (if d ∈ active walk then
      cmp116ComplexWeakeningMonomial ((active walk).erase d) sigma else 0) •
        term walk

/-- The radial majorant controls the complex coordinate derivative series
when `1 ≤ R`. -/
theorem summable_cmp116ComplexWeakenedRandomWalkSeriesDerivative
    [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E)
    (sigma : Δ → ℂ) (d : Δ) (radius : Δ → ℝ) (R : ℝ)
    (hR : 1 ≤ R)
    (hsigma : sigma ∈ cmp116ComplexShiftedWeakeningPolydisc radius)
    (hcap : ∀ walk x, x ∈ active walk → 1 + radius x ≤ R)
    (hmajor : Summable fun walk => R ^ (active walk).card * ‖term walk‖) :
    Summable fun walk =>
      (if d ∈ active walk then
        cmp116ComplexWeakeningMonomial ((active walk).erase d) sigma else 0) •
          term walk := by
  apply Summable.of_norm_bounded hmajor
  intro walk
  by_cases hd : d ∈ active walk
  · simp only [hd, if_true]
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_cmp116ComplexWeakeningMonomial_le_pow_card
      ((active walk).erase d) sigma radius R (zero_le_one.trans hR)
      (fun x _ => hsigma x)
      (fun x hx => hcap walk x (Finset.mem_of_mem_erase hx))).trans
        (pow_le_pow_right₀ hR Finset.card_erase_le)
  · simp [hd, mul_nonneg (pow_nonneg (zero_le_one.trans hR) _)
      (norm_nonneg _)]

/-- The complex weakened series is exactly affine in one coordinate. -/
theorem cmp116ComplexWeakenedRandomWalkSeries_update_eq_affine
    [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E)
    (sigma : Δ → ℂ) (d : Δ) (radius : Δ → ℝ) (R : ℝ)
    (hradius : ∀ x, 0 ≤ radius x)
    (hR : 1 ≤ R)
    (hsigma : sigma ∈ cmp116ComplexShiftedWeakeningPolydisc radius)
    (hcap : ∀ walk x, x ∈ active walk → 1 + radius x ≤ R)
    (hmajor : Summable fun walk => R ^ (active walk).card * ‖term walk‖)
    (t : ℂ) :
    cmp116ComplexWeakenedRandomWalkSeries active term
        (Function.update sigma d t) =
      t • cmp116ComplexWeakenedRandomWalkSeriesDerivative active term sigma d +
        cmp116ComplexWeakenedRandomWalkSeries active term
          (Function.update sigma d 0) := by
  let derivativeTerm : ω → E := fun walk =>
    (if d ∈ active walk then
      cmp116ComplexWeakeningMonomial ((active walk).erase d) sigma else 0) •
        term walk
  let zeroTerm : ω → E := fun walk =>
    cmp116ComplexWeakeningMonomial (active walk)
      (Function.update sigma d 0) • term walk
  have hsZero :
      Function.update sigma d 0 ∈
        cmp116ComplexShiftedWeakeningPolydisc radius := by
    intro x
    by_cases hx : x = d
    · subst x
      rw [Function.update_self, norm_zero]
      linarith [hradius d]
    · rw [Function.update_of_ne hx]
      exact hsigma x
  have hDerivative : Summable derivativeTerm :=
    summable_cmp116ComplexWeakenedRandomWalkSeriesDerivative
      active term sigma d radius R hR hsigma hcap hmajor
  have hZero : Summable zeroTerm :=
    summable_cmp116ComplexWeakenedRandomWalkSeries
      active term _ radius R (zero_le_one.trans hR) hsZero hcap hmajor
  calc
    cmp116ComplexWeakenedRandomWalkSeries active term
        (Function.update sigma d t) =
        ∑' walk, (t • derivativeTerm walk + zeroTerm walk) := by
      apply tsum_congr
      intro walk
      by_cases hd : d ∈ active walk
      · simp only [derivativeTerm, zeroTerm, hd, if_true]
        rw [cmp116ComplexWeakeningMonomial_update_of_mem
              (active walk) sigma d hd t,
          cmp116ComplexWeakeningMonomial_update_of_mem
              (active walk) sigma d hd 0]
        simp [mul_smul]
      · simp only [derivativeTerm, zeroTerm, hd, if_false, zero_smul]
        rw [cmp116ComplexWeakeningMonomial_update_of_not_mem
              (active walk) sigma d hd t,
          cmp116ComplexWeakeningMonomial_update_of_not_mem
              (active walk) sigma d hd 0]
        simp
    _ = (∑' walk, t • derivativeTerm walk) + ∑' walk, zeroTerm walk :=
      (hDerivative.const_smul t).tsum_add hZero
    _ = t • cmp116ComplexWeakenedRandomWalkSeriesDerivative
          active term sigma d +
        cmp116ComplexWeakenedRandomWalkSeries active term
          (Function.update sigma d 0) := by
      rw [hDerivative.tsum_const_smul]
      rfl

/-- Each complex weakening coordinate is an entire affine function. -/
theorem hasDerivAt_cmp116ComplexWeakenedRandomWalkSeries_update
    [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E)
    (sigma : Δ → ℂ) (d : Δ) (radius : Δ → ℝ) (R : ℝ)
    (hradius : ∀ x, 0 ≤ radius x)
    (hR : 1 ≤ R)
    (hsigma : sigma ∈ cmp116ComplexShiftedWeakeningPolydisc radius)
    (hcap : ∀ walk x, x ∈ active walk → 1 + radius x ≤ R)
    (hmajor : Summable fun walk => R ^ (active walk).card * ‖term walk‖)
    (x : ℂ) :
    HasDerivAt
      (fun t => cmp116ComplexWeakenedRandomWalkSeries active term
        (Function.update sigma d t))
      (cmp116ComplexWeakenedRandomWalkSeriesDerivative active term sigma d)
      x := by
  have hbase : HasDerivAt
      (fun t => t • cmp116ComplexWeakenedRandomWalkSeriesDerivative
          active term sigma d +
        cmp116ComplexWeakenedRandomWalkSeries active term
          (Function.update sigma d 0))
      (cmp116ComplexWeakenedRandomWalkSeriesDerivative active term sigma d)
      x := by
    have hlinear : HasDerivAt
        (fun t : ℂ => t • cmp116ComplexWeakenedRandomWalkSeriesDerivative
          active term sigma d)
        (cmp116ComplexWeakenedRandomWalkSeriesDerivative active term sigma d)
        x := by
      simpa only [id_eq, one_smul] using
        (hasDerivAt_id x).smul_const
          (cmp116ComplexWeakenedRandomWalkSeriesDerivative
            active term sigma d)
    exact hlinear.add_const
      (cmp116ComplexWeakenedRandomWalkSeries active term
        (Function.update sigma d 0))
  apply hbase.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t =>
    cmp116ComplexWeakenedRandomWalkSeries_update_eq_affine
      active term sigma d radius R hradius hR hsigma hcap hmajor t

end DecidableCubes

end YangMills.RG
