import YangMills.RG.BalabanCMP116WeakenedRandomWalkSum
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# CMP116 equation (1.6): absolutely summable weakened random-walk series

This module upgrades the finite weakening algebra to an arbitrary walk index.
The single load-bearing hypothesis is summability of

`R ^ card (active walk) * ‖term walk‖`.

It controls the series uniformly on the radius-`R` polydisc, controls the
coordinate derivative when `1 ≤ R`, and makes the finite truncations converge
to the infinite series.  At a zero-outside weakening system, the result is the
`tsum` over the subtype of walks supported in `K`; it is deliberately not
claimed to be a finite sum, since physical walks may revisit `K` indefinitely.

The derivative proof uses an exact affine decomposition in one weakening
coordinate.  Thus no generic differentiation-under-an-infinite-sum theorem is
needed: absolute summability justifies the two `tsum` operations, and the
resulting function is literally affine on the radius interval.

Honest scope: the physical walk type, its ordered operator term, and the proof
of the radial majorant remain inputs.  This file does not yet construct the
CMP116 propagators `H(s)`, `G(s)`, or `H₀(s)` from their local blocks.
-/

open scoped BigOperators

namespace YangMills.RG

universe u v w

variable {Δ : Type u} {ω : Type v} {E : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The absolute value of one weakening monomial is bounded by the radius to
the number of active cubes. -/
theorem abs_cmp116WeakeningMonomial_le_pow_card
    (active : Finset Δ) (s : Δ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hs : ∀ d ∈ active, |s d| ≤ R) :
    |cmp116WeakeningMonomial active s| ≤ R ^ active.card := by
  classical
  induction active using Finset.induction_on with
  | empty => simp [cmp116WeakeningMonomial]
  | @insert d active hd ih =>
      rw [cmp116WeakeningMonomial, Finset.prod_insert hd, abs_mul,
        Finset.card_insert_of_notMem hd, pow_succ]
      simpa [mul_comm] using mul_le_mul
        (hs d (Finset.mem_insert_self d active))
        (ih (fun x hx => hs x (Finset.mem_insert_of_mem hx)))
        (abs_nonneg _) hR

/-- The countable weakened random-walk series. -/
noncomputable def cmp116WeakenedRandomWalkSeries
    (active : ω → Finset Δ) (term : ω → E) (s : Δ → ℝ) : E :=
  ∑' walk, cmp116WeakeningMonomial (active walk) s • term walk

/-- The closed real weakening polydisc of radius `R`. -/
def cmp116WeakeningPolydisc (R : ℝ) : Set (Δ → ℝ) :=
  {s | ∀ d, |s d| ≤ R}

/-- The radial majorant controls the norm of one weakened walk term. -/
theorem norm_cmp116WeakeningTerm_le_radialMajorant
    (active : Finset Δ) (term : E) (s : Δ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hs : s ∈ cmp116WeakeningPolydisc R) :
    ‖cmp116WeakeningMonomial active s • term‖ ≤
      R ^ active.card * ‖term‖ := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (abs_cmp116WeakeningMonomial_le_pow_card active s R hR
      (fun d _ => hs d))
    (norm_nonneg term)

/-- A summable radial majorant makes the weakened walk family summable at every
point of the corresponding polydisc. -/
theorem summable_cmp116WeakenedRandomWalkSeries
    [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E) (s : Δ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hs : s ∈ cmp116WeakeningPolydisc R)
    (hmajor : Summable fun walk => R ^ (active walk).card * ‖term walk‖) :
    Summable fun walk =>
      cmp116WeakeningMonomial (active walk) s • term walk :=
  Summable.of_norm_bounded hmajor fun walk =>
    norm_cmp116WeakeningTerm_le_radialMajorant
      (active walk) (term walk) s R hR hs

/-- Finite truncations converge uniformly to the weakened series throughout
the closed radius-`R` polydisc. -/
theorem tendstoUniformlyOn_cmp116WeakenedRandomWalkSeries
    [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E) (R : ℝ)
    (hR : 0 ≤ R)
    (hmajor : Summable fun walk => R ^ (active walk).card * ‖term walk‖) :
    TendstoUniformlyOn
      (fun walks : Finset ω => fun s =>
        ∑ walk ∈ walks,
          cmp116WeakeningMonomial (active walk) s • term walk)
      (cmp116WeakenedRandomWalkSeries active term)
      Filter.atTop (cmp116WeakeningPolydisc R) := by
  exact tendstoUniformlyOn_tsum hmajor fun walk s hs =>
    norm_cmp116WeakeningTerm_le_radialMajorant
      (active walk) (term walk) s R hR hs

/-- At the fully coupled point, the infinite weakened series is the original
walk `tsum`. -/
theorem cmp116WeakenedRandomWalkSeries_one
    (active : ω → Finset Δ) (term : ω → E) :
    cmp116WeakenedRandomWalkSeries active term (fun _ => 1) =
      ∑' walk, term walk := by
  rw [cmp116WeakenedRandomWalkSeries]
  apply tsum_congr
  intro walk
  simp [cmp116WeakeningMonomial]

/-- The summable series is the limit of the directed net of all finite
truncations. -/
theorem hasSum_cmp116WeakenedRandomWalkSeries
    [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E) (s : Δ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hs : s ∈ cmp116WeakeningPolydisc R)
    (hmajor : Summable fun walk => R ^ (active walk).card * ‖term walk‖) :
    HasSum
      (fun walk => cmp116WeakeningMonomial (active walk) s • term walk)
      (cmp116WeakenedRandomWalkSeries active term s) := by
  exact (summable_cmp116WeakenedRandomWalkSeries
    active term s R hR hs hmajor).hasSum

section DecidableCubes

variable [DecidableEq Δ]

/-- Zeroing the coordinates outside `K` restricts the infinite series exactly
to the subtype of walks whose active cubes lie in `K`.  The restricted family
remains a `tsum`, not a finite sum. -/
theorem cmp116WeakenedRandomWalkSeries_zeroOutside
    (active : ω → Finset Δ) (term : ω → E) (K : Finset Δ) :
    cmp116WeakenedRandomWalkSeries active term
        (cmp116WeakeningZeroOutside K) =
      ∑' walk : {walk // active walk ⊆ K}, term walk := by
  rw [cmp116WeakenedRandomWalkSeries]
  calc
    (∑' walk,
      cmp116WeakeningMonomial (active walk)
        (cmp116WeakeningZeroOutside K) • term walk) =
        ∑' walk, Set.indicator {walk | active walk ⊆ K} term walk := by
      apply tsum_congr
      intro walk
      rw [Set.indicator_apply]
      by_cases h : active walk ⊆ K
      · simp [h, cmp116WeakeningMonomial_zeroOutside]
      · simp [h, cmp116WeakeningMonomial_zeroOutside]
    _ = ∑' walk : {walk // active walk ⊆ K}, term walk :=
      (tsum_subtype {walk | active walk ⊆ K} term).symm

/-- The coordinate derivative series. -/
noncomputable def cmp116WeakenedRandomWalkSeriesDerivative
    (active : ω → Finset Δ) (term : ω → E)
    (s : Δ → ℝ) (d : Δ) : E :=
  ∑' walk,
    (if d ∈ active walk then
      cmp116WeakeningMonomial ((active walk).erase d) s else 0) • term walk

/-- The same radial majorant controls the derivative series when `1 ≤ R`.
Erasing the differentiated cube can only decrease the power of `R`. -/
theorem summable_cmp116WeakenedRandomWalkSeriesDerivative
    [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E)
    (s : Δ → ℝ) (d : Δ) (R : ℝ)
    (hR : 1 ≤ R) (hs : s ∈ cmp116WeakeningPolydisc R)
    (hmajor : Summable fun walk => R ^ (active walk).card * ‖term walk‖) :
    Summable fun walk =>
      (if d ∈ active walk then
        cmp116WeakeningMonomial ((active walk).erase d) s else 0) • term walk := by
  apply Summable.of_norm_bounded hmajor
  intro walk
  by_cases hd : d ∈ active walk
  · simp only [hd, if_true]
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (abs_cmp116WeakeningMonomial_le_pow_card
      ((active walk).erase d) s R (zero_le_one.trans hR)
      (fun x _ => hs x)).trans
        (pow_le_pow_right₀ hR Finset.card_erase_le)
  · simp [hd, mul_nonneg (pow_nonneg (zero_le_one.trans hR) _)
      (norm_nonneg _)]

/-- The infinite series is exactly affine in one weakening coordinate.  No
bound on the updated coordinate is needed because each active carrier is a
finset and hence contributes at most one copy of that coordinate. -/
theorem cmp116WeakenedRandomWalkSeries_update_eq_affine
    [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E)
    (s : Δ → ℝ) (d : Δ) (R : ℝ)
    (hR : 1 ≤ R) (hs : s ∈ cmp116WeakeningPolydisc R)
    (hmajor : Summable fun walk => R ^ (active walk).card * ‖term walk‖)
    (t : ℝ) :
    cmp116WeakenedRandomWalkSeries active term (Function.update s d t) =
      t • cmp116WeakenedRandomWalkSeriesDerivative active term s d +
        cmp116WeakenedRandomWalkSeries active term
          (Function.update s d 0) := by
  let derivativeTerm : ω → E := fun walk =>
    (if d ∈ active walk then
      cmp116WeakeningMonomial ((active walk).erase d) s else 0) • term walk
  let zeroTerm : ω → E := fun walk =>
    cmp116WeakeningMonomial (active walk) (Function.update s d 0) • term walk
  have hsZero : Function.update s d 0 ∈ cmp116WeakeningPolydisc R := by
    intro x
    by_cases hx : x = d
    · subst x
      simp [zero_le_one.trans hR]
    · rw [Function.update_of_ne hx]
      exact hs x
  have hDerivative : Summable derivativeTerm :=
    summable_cmp116WeakenedRandomWalkSeriesDerivative
      active term s d R hR hs hmajor
  have hZero : Summable zeroTerm :=
    summable_cmp116WeakenedRandomWalkSeries
      active term _ R (zero_le_one.trans hR) hsZero hmajor
  calc
    cmp116WeakenedRandomWalkSeries active term (Function.update s d t) =
        ∑' walk, (t • derivativeTerm walk + zeroTerm walk) := by
      apply tsum_congr
      intro walk
      by_cases hd : d ∈ active walk
      · simp only [derivativeTerm, zeroTerm, hd, if_true]
        rw [cmp116WeakeningMonomial_update_of_mem (active walk) s d hd t,
          cmp116WeakeningMonomial_update_of_mem (active walk) s d hd 0]
        simp [mul_smul]
      · simp only [derivativeTerm, zeroTerm, hd, if_false, zero_smul]
        rw [cmp116WeakeningMonomial_update_of_not_mem (active walk) s d hd t,
          cmp116WeakeningMonomial_update_of_not_mem (active walk) s d hd 0]
        simp
    _ = (∑' walk, t • derivativeTerm walk) + ∑' walk, zeroTerm walk :=
      (hDerivative.const_smul t).tsum_add hZero
    _ = t • cmp116WeakenedRandomWalkSeriesDerivative active term s d +
        cmp116WeakenedRandomWalkSeries active term
          (Function.update s d 0) := by
      rw [hDerivative.tsum_const_smul]
      rfl

/-- Coordinate differentiation of the countable walk series is globally valid
in the updated coordinate. -/
theorem hasDerivAt_cmp116WeakenedRandomWalkSeries_update
    [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E)
    (s : Δ → ℝ) (d : Δ) (R : ℝ)
    (hR : 1 ≤ R) (hs : s ∈ cmp116WeakeningPolydisc R)
    (hmajor : Summable fun walk => R ^ (active walk).card * ‖term walk‖)
    (x : ℝ) :
    HasDerivAt
      (fun t => cmp116WeakenedRandomWalkSeries active term
        (Function.update s d t))
      (cmp116WeakenedRandomWalkSeriesDerivative active term s d)
      x := by
  have hbase : HasDerivAt
      (fun t => t • cmp116WeakenedRandomWalkSeriesDerivative active term s d +
        cmp116WeakenedRandomWalkSeries active term
          (Function.update s d 0))
      (cmp116WeakenedRandomWalkSeriesDerivative active term s d) x := by
    simpa using ((hasDerivAt_id x).smul_const
      (cmp116WeakenedRandomWalkSeriesDerivative active term s d) |>.add_const
        (cmp116WeakenedRandomWalkSeries active term
          (Function.update s d 0)))
  apply hbase.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t =>
    cmp116WeakenedRandomWalkSeries_update_eq_affine
      active term s d R hR hs hmajor t

/-- The global derivative also gives the corresponding derivative within any
chosen set. -/
theorem hasDerivWithinAt_cmp116WeakenedRandomWalkSeries_update
    [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E)
    (s : Δ → ℝ) (d : Δ) (R : ℝ)
    (hR : 1 ≤ R) (hs : s ∈ cmp116WeakeningPolydisc R)
    (hmajor : Summable fun walk => R ^ (active walk).card * ‖term walk‖)
    (set : Set ℝ) (x : ℝ) :
    HasDerivWithinAt
      (fun t => cmp116WeakenedRandomWalkSeries active term
        (Function.update s d t))
      (cmp116WeakenedRandomWalkSeriesDerivative active term s d) set x := by
  exact (hasDerivAt_cmp116WeakenedRandomWalkSeries_update
    active term s d R hR hs hmajor x).hasDerivWithinAt

/-- The literal one-coordinate FTC identity survives passage from finite walk
sums to the absolutely summable walk series. -/
theorem cmp116WeakenedRandomWalkSeries_ftcStep
    [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E)
    (s : Δ → ℝ) (d : Δ) (R : ℝ)
    (hR : 1 ≤ R) (hs : s ∈ cmp116WeakeningPolydisc R)
    (hmajor : Summable fun walk => R ^ (active walk).card * ‖term walk‖) :
    cmp116WeakenedRandomWalkSeries active term (Function.update s d 0) +
        ∫ _t in (0 : ℝ)..1,
          cmp116WeakenedRandomWalkSeriesDerivative active term s d =
      cmp116WeakenedRandomWalkSeries active term
        (Function.update s d 1) := by
  apply cmp116FTC_oneStep
    (fun t => cmp116WeakenedRandomWalkSeries active term
      (Function.update s d t))
    (fun _ => cmp116WeakenedRandomWalkSeriesDerivative active term s d)
  · intro t _ht
    exact hasDerivAt_cmp116WeakenedRandomWalkSeries_update
      active term s d R hR hs hmajor t
  · exact continuous_const.intervalIntegrable 0 1

end DecidableCubes

end YangMills.RG
