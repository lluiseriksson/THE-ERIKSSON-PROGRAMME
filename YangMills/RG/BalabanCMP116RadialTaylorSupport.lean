import YangMills.RG.BalabanCMP116RadialTaylorOperator
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Exact support of the CMP116 radial Taylor operator

For a functional on a finite Euclidean coordinate space that depends only on
a finite set `S`, this file proves that its first derivative vanishes in every
direction supported outside `S`.  Differentiating that exact identity and
using symmetry of the `C^2` Hessian gives two-sided support of every Hessian
along the radial segment.

The conclusion is inherited by the radial Taylor operator: its matrix element
vanishes whenever either coordinate lies outside `S`.  Thus averaging the
Hessian along `tB` preserves the exact localization support required for the
CMP116 operator `Q(Y,B)`.
-/

open MeasureTheory Set
open scoped Interval RealInnerProductSpace

namespace YangMills.RG

noncomputable section

/-- A localized functional has zero derivative in a direction that vanishes
on all active coordinates. -/
theorem cmp116EuclideanFDeriv_eq_zero_of_direction_vanishesOn
    {I : Type*} [Fintype I]
    (S : Finset I) (f : EuclideanSpace ℝ I → ℝ)
    (x u : EuclideanSpace ℝ I)
    (hf : Differentiable ℝ f)
    (hlocal : ∀ {z w : EuclideanSpace ℝ I},
      (∀ i ∈ S, z i = w i) → f z = f w)
    (hu : ∀ i ∈ S, u i = 0) :
    fderiv ℝ f x u = 0 := by
  have hline : (fun t : ℝ => f (x + t • u)) = fun _ => f x := by
    funext t
    apply hlocal
    intro i hi
    simp [hu i hi]
  have hdir : HasDerivAt (fun t : ℝ => f (x + t • u))
      (fderiv ℝ f x u) 0 := by
    have hlineDeriv : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
      convert (hasDerivAt_const (x := (0 : ℝ)) x).add
        ((hasDerivAt_id (0 : ℝ)).smul_const u) using 1 <;> simp
    have hfat : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • u) := by
      simpa using (hf x).hasFDerivAt
    exact hfat.comp_hasDerivAt 0 hlineDeriv
  rw [hline] at hdir
  exact hdir.unique (hasDerivAt_const (x := (0 : ℝ)) (f x))

/-- Right support of the Hessian of a localized `C^2` functional. -/
theorem cmp116EuclideanHessian_eq_zero_of_right_vanishesOn
    {I : Type*} [Fintype I]
    (S : Finset I) (f : EuclideanSpace ℝ I → ℝ)
    (x u v : EuclideanSpace ℝ I)
    (hf : ContDiff ℝ 2 f)
    (hlocal : ∀ {z w : EuclideanSpace ℝ I},
      (∀ i ∈ S, z i = w i) → f z = f w)
    (hv : ∀ i ∈ S, v i = 0) :
    cmp116FDerivHessian f x u v = 0 := by
  have hfirst : (fun y : EuclideanSpace ℝ I => fderiv ℝ f y v) = fun _ => 0 := by
    funext y
    exact cmp116EuclideanFDeriv_eq_zero_of_direction_vanishesOn S f y v
      (hf.differentiable two_ne_zero) hlocal hv
  have hfderivCont : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have hhess : HasFDerivAt (fderiv ℝ f)
      (cmp116FDerivHessian f x) x :=
    hfderivCont.differentiable_one.differentiableAt.hasFDerivAt
  have heval : HasFDerivAt
      (fun y : EuclideanSpace ℝ I => fderiv ℝ f y v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp
        (cmp116FDerivHessian f x)) x := by
    simpa [Function.comp_def] using
      (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hhess
  have heq := heval.fderiv
  rw [hfirst] at heq
  have happ := congrArg (fun L : EuclideanSpace ℝ I →L[ℝ] ℝ => L u) heq
  simpa [cmp116FDerivHessian] using happ.symm

/-- Left support follows from symmetry of the `C^2` Hessian. -/
theorem cmp116EuclideanHessian_eq_zero_of_left_vanishesOn
    {I : Type*} [Fintype I]
    (S : Finset I) (f : EuclideanSpace ℝ I → ℝ)
    (x u v : EuclideanSpace ℝ I)
    (hf : ContDiff ℝ 2 f)
    (hlocal : ∀ {z w : EuclideanSpace ℝ I},
      (∀ i ∈ S, z i = w i) → f z = f w)
    (hu : ∀ i ∈ S, u i = 0) :
    cmp116FDerivHessian f x u v = 0 := by
  have hsymmAt : IsSymmSndFDerivAt ℝ f x :=
    hf.contDiffAt.isSymmSndFDerivAt
      (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
  have hsymm := hsymmAt.eq u v
  change fderiv ℝ (fderiv ℝ f) x u v = 0
  rw [hsymm]
  exact cmp116EuclideanHessian_eq_zero_of_right_vanishesOn
    S f x v u hf hlocal hu

/-- Every matrix element of the radial Taylor operator vanishes when either
direction is supported outside the active coordinate set. -/
theorem inner_cmp116RadialTaylorOperator_eq_zero_of_vanishesOn
    {I : Type*} [Fintype I]
    (S : Finset I) (f : EuclideanSpace ℝ I → ℝ)
    (B A A' : EuclideanSpace ℝ I)
    (hf : ContDiff ℝ 2 f)
    (hlocal : ∀ {z w : EuclideanSpace ℝ I},
      (∀ i ∈ S, z i = w i) → f z = f w)
    (hAA' : (∀ i ∈ S, A i = 0) ∨ (∀ i ∈ S, A' i = 0)) :
    inner ℝ A (cmp116RadialTaylorOperator f B hf A') = 0 := by
  rw [inner_cmp116RadialTaylorOperator]
  rcases hAA' with hA | hA'
  · have hzero : (fun t : ℝ =>
        (1 - t) * cmp116FDerivHessian f (t • B) A' A) = fun _ => 0 := by
      funext t
      rw [cmp116EuclideanHessian_eq_zero_of_right_vanishesOn
        S f (t • B) A' A hf hlocal hA]
      simp
    rw [hzero]
    simp
  · have hzero : (fun t : ℝ =>
        (1 - t) * cmp116FDerivHessian f (t • B) A' A) = fun _ => 0 := by
      funext t
      rw [cmp116EuclideanHessian_eq_zero_of_left_vanishesOn
        S f (t • B) A' A hf hlocal hA']
      simp
    rw [hzero]
    simp

/-- Coordinate form of exact two-sided support for `Q_f(B)`. -/
theorem cmp116RadialTaylorOperator_coordinateSupport
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (f : EuclideanSpace ℝ I → ℝ)
    (B : EuclideanSpace ℝ I)
    (hf : ContDiff ℝ 2 f)
    (hlocal : ∀ {z w : EuclideanSpace ℝ I},
      (∀ i ∈ S, z i = w i) → f z = f w)
    {i j : I} (a b : ℝ) (hij : i ∉ S ∨ j ∉ S) :
    inner ℝ (EuclideanSpace.single i a)
      (cmp116RadialTaylorOperator f B hf (EuclideanSpace.single j b)) = 0 := by
  apply inner_cmp116RadialTaylorOperator_eq_zero_of_vanishesOn
    S f B _ _ hf hlocal
  rcases hij with hi | hj
  · left
    intro k hk
    simp [EuclideanSpace.single_apply, ne_of_mem_of_not_mem hk hi]
  · right
    intro k hk
    simp [EuclideanSpace.single_apply, ne_of_mem_of_not_mem hk hj]

end

end YangMills.RG
