import YangMills.RG.BalabanCMP116RadialTaylorOperator
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open MeasureTheory Set
open scoped Interval

namespace YangMills.RG

noncomputable section

theorem testFDeriv_eq_zero_of_direction_vanishesOn
    {I V : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : Finset I) (f : (I → V) → ℝ) (x u : I → V)
    (hf : Differentiable ℝ f)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
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

theorem testHessian_eq_zero_of_right_vanishesOn
    {I V : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : Finset I) (f : (I → V) → ℝ) (x u v : I → V)
    (hf : ContDiff ℝ 2 f)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    (hv : ∀ i ∈ S, v i = 0) :
    cmp116FDerivHessian f x u v = 0 := by
  have hfirst : (fun y : I → V => fderiv ℝ f y v) = fun _ => 0 := by
    funext y
    exact testFDeriv_eq_zero_of_direction_vanishesOn S f y v
      (hf.differentiable two_ne_zero) hlocal hv
  have hfderivCont : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have hhess : HasFDerivAt (fderiv ℝ f)
      (cmp116FDerivHessian f x) x :=
    hfderivCont.differentiable_one.differentiableAt.hasFDerivAt
  have heval : HasFDerivAt
      (fun y : I → V => fderiv ℝ f y v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp
        (cmp116FDerivHessian f x)) x := by
    simpa [Function.comp_def] using
      (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hhess
  have heq := heval.fderiv
  rw [hfirst] at heq
  have happ := congrArg (fun L : (I → V) →L[ℝ] ℝ => L u) heq
  simpa [cmp116FDerivHessian] using happ.symm

theorem testHessian_eq_zero_of_left_vanishesOn
    {I V : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : Finset I) (f : (I → V) → ℝ) (x u v : I → V)
    (hf : ContDiff ℝ 2 f)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    (hu : ∀ i ∈ S, u i = 0) :
    cmp116FDerivHessian f x u v = 0 := by
  have hsymmAt : IsSymmSndFDerivAt ℝ f x :=
    hf.contDiffAt.isSymmSndFDerivAt
      (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
  have hsymm := hsymmAt.eq u v
  change fderiv ℝ (fderiv ℝ f) x u v = 0
  rw [hsymm]
  exact testHessian_eq_zero_of_right_vanishesOn S f x v u hf hlocal hu

theorem testRadialTaylorBilinear_eq_zero_of_left_vanishesOn
    {I V : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ (I → V)]
    (S : Finset I) (f : (I → V) → ℝ) (B A A' : I → V)
    (hf : ContDiff ℝ 2 f)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    (hA : ∀ i ∈ S, A i = 0) :
    cmp116RadialTaylorBilinear f B hf A A' = 0 := by
  rw [cmp116RadialTaylorBilinear_apply]
  have hzero : (fun t : ℝ =>
      (1 - t) * cmp116FDerivHessian f (t • B) A A') = fun _ => 0 := by
    funext t
    rw [testHessian_eq_zero_of_left_vanishesOn S f (t • B) A A' hf hlocal hA]
    simp
  rw [hzero]
  simp

theorem testRadialTaylorBilinear_eq_zero_of_right_vanishesOn
    {I V : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ (I → V)]
    (S : Finset I) (f : (I → V) → ℝ) (B A A' : I → V)
    (hf : ContDiff ℝ 2 f)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    (hA' : ∀ i ∈ S, A' i = 0) :
    cmp116RadialTaylorBilinear f B hf A A' = 0 := by
  rw [cmp116RadialTaylorBilinear_apply]
  have hzero : (fun t : ℝ =>
      (1 - t) * cmp116FDerivHessian f (t • B) A A') = fun _ => 0 := by
    funext t
    rw [testHessian_eq_zero_of_right_vanishesOn S f (t • B) A A' hf hlocal hA']
    simp
  rw [hzero]
  simp

theorem testRadialTaylorOperator_inner_eq_zero_of_vanishesOn
    {I V : Type*} [Fintype I]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ (I → V)] [CompleteSpace (I → V)]
    (S : Finset I) (f : (I → V) → ℝ) (B A A' : I → V)
    (hf : ContDiff ℝ 2 f)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    (hAA' : (∀ i ∈ S, A i = 0) ∨ (∀ i ∈ S, A' i = 0)) :
    inner ℝ A (cmp116RadialTaylorOperator f B hf A') = 0 := by
  rw [inner_cmp116RadialTaylorOperator]
  rcases hAA' with hA | hA'
  · have hzero : (fun t : ℝ =>
        (1 - t) * cmp116FDerivHessian f (t • B) A' A) = fun _ => 0 := by
      funext t
      rw [testHessian_eq_zero_of_right_vanishesOn S f (t • B) A' A hf hlocal hA]
      simp
    rw [hzero]
    simp
  · have hzero : (fun t : ℝ =>
        (1 - t) * cmp116FDerivHessian f (t • B) A' A) = fun _ => 0 := by
      funext t
      rw [testHessian_eq_zero_of_left_vanishesOn S f (t • B) A' A hf hlocal hA']
      simp
    rw [hzero]
    simp

theorem testRadialTaylorOperator_coordinate_support
    {I V : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ (I → V)] [CompleteSpace (I → V)]
    (S : Finset I) (f : (I → V) → ℝ) (B : I → V)
    (hf : ContDiff ℝ 2 f)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    {i j : I} (a b : V) (hij : i ∉ S ∨ j ∉ S) :
    inner ℝ (Pi.single i a)
      (cmp116RadialTaylorOperator f B hf (Pi.single j b)) = 0 := by
  apply testRadialTaylorOperator_inner_eq_zero_of_vanishesOn S f B _ _ hf hlocal
  rcases hij with hi | hj
  · left
    intro k hk
    simp [ne_of_mem_of_not_mem hk hi]
  · right
    intro k hk
    simp [ne_of_mem_of_not_mem hk hj]

end

end YangMills.RG
