import YangMills.RG.BalabanCMP116FTCInterpolation
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# CMP116 equation (1.6): finite weakened random-walk sums

The CMP116 decoupling parameters are inserted into a generalized random-walk
expansion by multiplying the term for a walk `ω` by

`∏ Δ ∈ active(ω), s(Δ)`.

This file formalizes that literal finite mechanism.  It proves recovery of the
original walk sum at `s = 1`, exact restriction to walks supported in `K` when
`s` is zero outside `K`, the coordinate derivative, and the corresponding
one-coordinate FTC identity.

Honest scope: a finite walk index, its active cube carrier, and its operator
value remain inputs.  The module does not yet construct Balaban's generalized
random walks or prove their kernel decay.  It is the algebraic/analytic producer
that those physical data must instantiate; it is not itself the physical
propagator `H(s)`, `G(s)`, or `H₀(s)`.
-/

open scoped BigOperators

namespace YangMills.RG

universe u v w

variable {Δ : Type u} {ω : Type v} {E : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The weakening monomial attached to the active cubes of one walk. -/
def cmp116WeakeningMonomial (active : Finset Δ) (s : Δ → ℝ) : ℝ :=
  ∏ d ∈ active, s d

/-- A finite generalized random-walk sum with the literal CMP116 weakening
monomial. -/
def cmp116WeakenedRandomWalkSum
    (walks : Finset ω) (active : ω → Finset Δ)
    (term : ω → E) (s : Δ → ℝ) : E :=
  ∑ walk ∈ walks, cmp116WeakeningMonomial (active walk) s • term walk

/-- At the fully coupled point `s = 1`, the weakened sum is the original walk
sum. -/
theorem cmp116WeakenedRandomWalkSum_one
    (walks : Finset ω) (active : ω → Finset Δ) (term : ω → E) :
    cmp116WeakenedRandomWalkSum walks active term (fun _ => 1) =
      ∑ walk ∈ walks, term walk := by
  simp [cmp116WeakenedRandomWalkSum, cmp116WeakeningMonomial]

section DecidableCubes

variable [DecidableEq Δ]

/-- Updating an active weakening coordinate exposes that coordinate as one
linear factor. -/
theorem cmp116WeakeningMonomial_update_of_mem
    (active : Finset Δ) (s : Δ → ℝ) (d : Δ)
    (hd : d ∈ active) (t : ℝ) :
    cmp116WeakeningMonomial active (Function.update s d t) =
      t * cmp116WeakeningMonomial (active.erase d) s := by
  calc
    cmp116WeakeningMonomial active (Function.update s d t) =
        Function.update s d t d *
          ∏ x ∈ active \ {d}, Function.update s d t x := by
      exact Finset.prod_eq_mul_prod_diff_singleton_of_mem hd _
    _ = t * ∏ x ∈ active \ {d}, s x := by
      rw [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro x hx
      rw [Function.update_of_ne]
      simpa using (Finset.mem_sdiff.mp hx).2
    _ = t * cmp116WeakeningMonomial (active.erase d) s := by
      simp [cmp116WeakeningMonomial, Finset.erase_eq]

/-- Updating an inactive weakening coordinate leaves the monomial unchanged. -/
theorem cmp116WeakeningMonomial_update_of_not_mem
    (active : Finset Δ) (s : Δ → ℝ) (d : Δ)
    (hd : d ∉ active) (t : ℝ) :
    cmp116WeakeningMonomial active (Function.update s d t) =
      cmp116WeakeningMonomial active s := by
  simp only [cmp116WeakeningMonomial]
  apply Finset.prod_congr rfl
  intro x hx
  rw [Function.update_of_ne (ne_of_mem_of_not_mem hx hd)]

/-- The derivative of one weakening monomial in a chosen coordinate. -/
theorem hasDerivAt_cmp116WeakeningMonomial_update
    (active : Finset Δ) (s : Δ → ℝ) (d : Δ) (x : ℝ) :
    HasDerivAt
      (fun t => cmp116WeakeningMonomial active (Function.update s d t))
      (if d ∈ active then cmp116WeakeningMonomial (active.erase d) s else 0) x := by
  by_cases hd : d ∈ active
  · simp only [hd, if_true]
    have hfun :
        (fun t => cmp116WeakeningMonomial active (Function.update s d t)) =
          fun t => t * cmp116WeakeningMonomial (active.erase d) s := by
      funext t
      exact cmp116WeakeningMonomial_update_of_mem active s d hd t
    rw [hfun]
    simpa using
      (hasDerivAt_id x).mul_const (cmp116WeakeningMonomial (active.erase d) s)
  · simp only [hd, if_false]
    have hfun :
        (fun t => cmp116WeakeningMonomial active (Function.update s d t)) =
          fun _ => cmp116WeakeningMonomial active s := by
      funext t
      exact cmp116WeakeningMonomial_update_of_not_mem active s d hd t
    rw [hfun]
    exact hasDerivAt_const x _

/-- The exact derivative coefficient of a weakened finite walk sum. -/
def cmp116WeakenedRandomWalkDerivative
    (walks : Finset ω) (active : ω → Finset Δ)
    (term : ω → E) (s : Δ → ℝ) (d : Δ) : E :=
  ∑ walk ∈ walks,
    (if d ∈ active walk then
      cmp116WeakeningMonomial ((active walk).erase d) s else 0) • term walk

/-- Coordinate differentiation of the finite weakened walk sum is exact. -/
theorem hasDerivAt_cmp116WeakenedRandomWalkSum_update
    (walks : Finset ω) (active : ω → Finset Δ)
    (term : ω → E) (s : Δ → ℝ) (d : Δ) (x : ℝ) :
    HasDerivAt
      (fun t => cmp116WeakenedRandomWalkSum walks active term
        (Function.update s d t))
      (cmp116WeakenedRandomWalkDerivative walks active term s d) x := by
  unfold cmp116WeakenedRandomWalkSum cmp116WeakenedRandomWalkDerivative
  exact HasDerivAt.fun_sum fun walk hwalk =>
    (hasDerivAt_cmp116WeakeningMonomial_update (active walk) s d x).smul_const
      (term walk)

/-- A weakening system that is one on `K` and zero outside `K`. -/
def cmp116WeakeningZeroOutside (K : Finset Δ) : Δ → ℝ :=
  fun d => if d ∈ K then 1 else 0

/-- At a zero-outside weakening system, one walk monomial is exactly the
indicator that all of its active cubes lie in `K`. -/
theorem cmp116WeakeningMonomial_zeroOutside
    (active K : Finset Δ) :
    cmp116WeakeningMonomial active (cmp116WeakeningZeroOutside K) =
      if active ⊆ K then 1 else 0 := by
  by_cases h : active ⊆ K
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro d hd
    simp [cmp116WeakeningZeroOutside, h hd]
  · rw [if_neg h]
    obtain ⟨d, hdActive, hdK⟩ := Finset.not_subset.mp h
    apply Finset.prod_eq_zero hdActive
    simp [cmp116WeakeningZeroOutside, hdK]

/-- Setting all coordinates outside `K` to zero removes exactly the walks whose
active carrier is not contained in `K`. -/
theorem cmp116WeakenedRandomWalkSum_zeroOutside
    (walks : Finset ω) (active : ω → Finset Δ)
    (term : ω → E) (K : Finset Δ) :
    cmp116WeakenedRandomWalkSum walks active term
        (cmp116WeakeningZeroOutside K) =
      ∑ walk ∈ walks.filter fun walk => active walk ⊆ K, term walk := by
  classical
  rw [Finset.sum_filter]
  simp [cmp116WeakenedRandomWalkSum, cmp116WeakeningMonomial_zeroOutside]

/-- The literal one-coordinate FTC identity for a finite weakened walk sum. -/
theorem cmp116WeakenedRandomWalkSum_ftcStep
    [CompleteSpace E]
    (walks : Finset ω) (active : ω → Finset Δ)
    (term : ω → E) (s : Δ → ℝ) (d : Δ) :
    cmp116WeakenedRandomWalkSum walks active term (Function.update s d 0) +
        ∫ _t in (0 : ℝ)..1,
          cmp116WeakenedRandomWalkDerivative walks active term s d =
      cmp116WeakenedRandomWalkSum walks active term (Function.update s d 1) := by
  apply cmp116FTC_oneStep
    (fun t => cmp116WeakenedRandomWalkSum walks active term
      (Function.update s d t))
    (fun _ => cmp116WeakenedRandomWalkDerivative walks active term s d)
  · intro t ht
    exact hasDerivAt_cmp116WeakenedRandomWalkSum_update walks active term s d t
  · exact continuous_const.intervalIntegrable 0 1

end DecidableCubes

end YangMills.RG
