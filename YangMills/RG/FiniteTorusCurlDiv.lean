import YangMills.L0_Lattice.FiniteLatticeGeometryInstance

/-!
# Periodic curl/divergence kernel on a finite torus

This file isolates the source-facing finite-difference theorem needed by the
flat physical Poincare path.  The main proposition is deliberately stated for
plain positive-bond fields on `FinBox d N`, with the current ordered plaquette
and backward-divergence conventions.  It carries no Yang--Mills, Hilbert-space,
or Wilson-Hessian terminology.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

/-- Source-facing classification theorem for periodic positive-bond fields.

The hypotheses are the ordered plaquette curl stencil and the outgoing-minus-
incoming backward divergence stencil.  The conclusion is direction-wise
constancy. -/
def PeriodicCurlDivKernelClassified
    (d N : ℕ) [NeZero N]
    (V : Type*) [AddCommGroup V] : Prop :=
  ∀ A : FinBox d N → Fin d → V,
    (∀ (x : FinBox d N) (i j : Fin d), i < j →
      A x i
        + A (x.shift i) j
        - A (x.shift j) i
        - A x j = 0) →
    (∀ x : FinBox d N,
      ∑ i : Fin d,
        (A x i - A (x.shiftBack i) i) = 0) →
    ∃ v : Fin d → V,
      ∀ x i, A x i = v i

/-- Forward finite difference in a periodic coordinate direction. -/
def torusForwardDiff {d N : ℕ} [NeZero N]
    {V : Type*} [AddCommGroup V]
    (i : Fin d) (f : FinBox d N → V) (x : FinBox d N) : V :=
  f (x.shift i) - f x

/-- Backward finite difference in a periodic coordinate direction. -/
def torusBackwardDiff {d N : ℕ} [NeZero N]
    {V : Type*} [AddCommGroup V]
    (i : Fin d) (f : FinBox d N → V) (x : FinBox d N) : V :=
  f x - f (x.shiftBack i)

/-- Backward divergence of a positive-bond field. -/
def torusDivergence {d N : ℕ} [NeZero N]
    {V : Type*} [AddCommGroup V]
    (A : FinBox d N → Fin d → V) (x : FinBox d N) : V :=
  ∑ i : Fin d, torusBackwardDiff i (fun y => A y i) x

/-- Periodic scalar Laplacian written as `backward ∘ forward`. -/
def torusLaplacian {d N : ℕ} [NeZero N]
    {V : Type*} [AddCommGroup V]
    (f : FinBox d N → V) (x : FinBox d N) : V :=
  ∑ i : Fin d, torusBackwardDiff i (torusForwardDiff i f) x

/-- Forward and backward finite differences commute on the periodic torus. -/
theorem torusForwardDiff_torusBackwardDiff_comm
    {d N : ℕ} [NeZero N]
    {V : Type*} [AddCommGroup V]
    (f : FinBox d N → V) (i j : Fin d) (x : FinBox d N) :
    torusForwardDiff i (torusBackwardDiff j f) x =
      torusBackwardDiff j (torusForwardDiff i f) x := by
  simp [torusForwardDiff, torusBackwardDiff, FinBox.shift_shiftBack_comm]
  abel

/-- Periodic summation by parts: the backward difference is the negative
adjoint of the forward difference on the finite torus. -/
theorem sum_inner_torusBackwardDiff
    {d N : ℕ} [NeZero N]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f g : FinBox d N → V) (i : Fin d) :
    (∑ x : FinBox d N, inner ℝ (f x) (torusBackwardDiff i g x)) =
      -∑ x : FinBox d N, inner ℝ (torusForwardDiff i f x) (g x) := by
  have hshift :
      (∑ x : FinBox d N, inner ℝ (f x) (g (x.shiftBack i))) =
        ∑ x : FinBox d N, inner ℝ (f (x.shift i)) (g x) := by
    let h : FinBox d N → ℝ := fun y => inner ℝ (f (y.shift i)) (g y)
    have hs := FinBox.sum_shiftBack h i
    simpa [h, FinBox.shift_shiftBack] using hs
  calc
    (∑ x : FinBox d N, inner ℝ (f x) (torusBackwardDiff i g x))
        = ∑ x : FinBox d N,
            (inner ℝ (f x) (g x) - inner ℝ (f x) (g (x.shiftBack i))) := by
          simp [torusBackwardDiff, inner_sub_right]
    _ = (∑ x : FinBox d N, inner ℝ (f x) (g x)) -
          ∑ x : FinBox d N, inner ℝ (f x) (g (x.shiftBack i)) := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ x : FinBox d N, inner ℝ (f x) (g x)) -
          ∑ x : FinBox d N, inner ℝ (f (x.shift i)) (g x) := by
          rw [hshift]
    _ = -∑ x : FinBox d N,
          (inner ℝ (f (x.shift i)) (g x) - inner ℝ (f x) (g x)) := by
          rw [Finset.sum_sub_distrib]
          abel
    _ = -∑ x : FinBox d N,
          inner ℝ (f (x.shift i) - f x) (g x) := by
          simp [inner_sub_left]
    _ = -∑ x : FinBox d N,
          inner ℝ (torusForwardDiff i f x) (g x) := by
          simp [torusForwardDiff]

/-- Energy identity for the periodic scalar Laplacian. -/
theorem sum_inner_torusLaplacian_eq_neg_sum_norm_sq
    {d N : ℕ} [NeZero N]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : FinBox d N → V) :
    (∑ x : FinBox d N, inner ℝ (f x) (torusLaplacian f x)) =
      -∑ i : Fin d, ∑ x : FinBox d N,
        ‖torusForwardDiff i f x‖ ^ 2 := by
  calc
    (∑ x : FinBox d N, inner ℝ (f x) (torusLaplacian f x))
        = ∑ x : FinBox d N, ∑ i : Fin d,
            inner ℝ (f x) (torusBackwardDiff i (torusForwardDiff i f) x) := by
          apply Finset.sum_congr rfl
          intro x _
          simp [torusLaplacian, inner_sum]
    _ = ∑ i : Fin d, ∑ x : FinBox d N,
            inner ℝ (f x) (torusBackwardDiff i (torusForwardDiff i f) x) := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin d, -∑ x : FinBox d N,
            inner ℝ (torusForwardDiff i f x) (torusForwardDiff i f x) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [sum_inner_torusBackwardDiff]
    _ = ∑ i : Fin d, -∑ x : FinBox d N,
            ‖torusForwardDiff i f x‖ ^ 2 := by
          simp
    _ = -∑ i : Fin d, ∑ x : FinBox d N,
            ‖torusForwardDiff i f x‖ ^ 2 := by
          rw [← Finset.sum_neg_distrib]

/-- Curl symmetry identifies the component Laplacian with the forward
difference of the divergence. -/
theorem torusLaplacian_component_eq_forwardDiff_divergence
    {d N : ℕ} [NeZero N]
    {V : Type*} [AddCommGroup V]
    (A : FinBox d N → Fin d → V)
    (hcurl :
      ∀ x i j,
        torusForwardDiff i (fun y => A y j) x =
          torusForwardDiff j (fun y => A y i) x)
    (i : Fin d) (x : FinBox d N) :
    torusLaplacian (fun y => A y i) x =
      torusForwardDiff i (torusDivergence A) x := by
  calc
    torusLaplacian (fun y => A y i) x
        = ∑ j : Fin d,
            torusBackwardDiff j (torusForwardDiff j (fun y => A y i)) x := by
          rfl
    _ = ∑ j : Fin d,
            torusBackwardDiff j (torusForwardDiff i (fun y => A y j)) x := by
          apply Finset.sum_congr rfl
          intro j _
          have hfun :
              torusForwardDiff j (fun y => A y i) =
                torusForwardDiff i (fun y => A y j) := by
            funext y
            exact hcurl y j i
          rw [hfun]
    _ = ∑ j : Fin d,
            torusForwardDiff i (torusBackwardDiff j (fun y => A y j)) x := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← torusForwardDiff_torusBackwardDiff_comm]
    _ = torusForwardDiff i (torusDivergence A) x := by
          simp [torusForwardDiff, torusDivergence, Finset.sum_sub_distrib]

/-- A periodic field with zero torus Laplacian is constant. -/
theorem eq_default_of_torusLaplacian_eq_zero
    {d N : ℕ} [NeZero N]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : FinBox d N → V)
    (hlap : ∀ x, torusLaplacian f x = 0) :
    ∀ x, f x = f (default : FinBox d N) := by
  let S : ℝ :=
    ∑ i : Fin d, ∑ x : FinBox d N, ‖torusForwardDiff i f x‖ ^ 2
  have hleft :
      (∑ x : FinBox d N, inner ℝ (f x) (torusLaplacian f x)) = 0 := by
    simp [hlap]
  have hneg : -S = 0 := by
    rw [← sum_inner_torusLaplacian_eq_neg_sum_norm_sq f, hleft]
  have hS : S = 0 := neg_eq_zero.mp hneg
  have hdir :
      ∀ i : Fin d,
        (∑ x : FinBox d N, ‖torusForwardDiff i f x‖ ^ 2) = 0 := by
    intro i
    have hnonneg :
        ∀ j ∈ (Finset.univ : Finset (Fin d)),
          0 ≤ (∑ x : FinBox d N, ‖torusForwardDiff j f x‖ ^ 2) := by
      intro j _
      exact Finset.sum_nonneg fun x _ => sq_nonneg _
    exact
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hS
        i (Finset.mem_univ i)
  have hdiff :
      ∀ (i : Fin d) (x : FinBox d N), torusForwardDiff i f x = 0 := by
    intro i x
    have hnonneg :
        ∀ y ∈ (Finset.univ : Finset (FinBox d N)),
          0 ≤ ‖torusForwardDiff i f y‖ ^ 2 := by
      intro y _
      exact sq_nonneg _
    have hxzero :
        ‖torusForwardDiff i f x‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp (hdir i)
        x (Finset.mem_univ x)
    have hnorm : ‖torusForwardDiff i f x‖ = 0 :=
      sq_eq_zero_iff.mp hxzero
    exact norm_eq_zero.mp hnorm
  refine FinBox.eq_default_of_shift_invariant f ?_
  intro x i
  exact sub_eq_zero.mp (by simpa [torusForwardDiff] using hdiff i x)

/-- Periodic curl-zero and backward-divergence-zero positive-bond fields are
exactly direction-wise constants. -/
theorem periodicCurlDivKernelClassified
    {d N : ℕ} [NeZero N]
    {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    PeriodicCurlDivKernelClassified d N V := by
  intro A hcurlOrdered hdiv
  have hcurl :
      ∀ x i j,
        torusForwardDiff i (fun y => A y j) x =
          torusForwardDiff j (fun y => A y i) x := by
    intro x i j
    by_cases hijEq : i = j
    · subst j
      rfl
    · rcases lt_or_gt_of_ne hijEq with hij | hji
      · have h := hcurlOrdered x i j hij
        change A (x.shift i) j - A x j =
          A (x.shift j) i - A x i
        rw [← sub_eq_zero]
        have hgoal :
            A (x.shift i) j - A x j -
                (A (x.shift j) i - A x i) =
              A x i + A (x.shift i) j - A (x.shift j) i - A x j := by
          abel
        rw [hgoal]
        exact h
      · have h := hcurlOrdered x j i hji
        change A (x.shift i) j - A x j =
          A (x.shift j) i - A x i
        rw [← sub_eq_zero]
        have hgoal :
            A (x.shift i) j - A x j -
                (A (x.shift j) i - A x i) =
              -(A x j + A (x.shift j) i - A (x.shift i) j - A x i) := by
          abel
        rw [hgoal, h, neg_zero]
  have hlap :
      ∀ (i : Fin d) (x : FinBox d N),
        torusLaplacian (fun y => A y i) x = 0 := by
    intro i x
    rw [torusLaplacian_component_eq_forwardDiff_divergence A hcurl i x]
    have hdiv_shift : torusDivergence A (x.shift i) = 0 := by
      simpa [torusDivergence, torusBackwardDiff] using hdiv (x.shift i)
    have hdiv_x : torusDivergence A x = 0 := by
      simpa [torusDivergence, torusBackwardDiff] using hdiv x
    simp [torusForwardDiff, hdiv_shift, hdiv_x]
  refine ⟨fun i => A (default : FinBox d N) i, ?_⟩
  intro x i
  exact eq_default_of_torusLaplacian_eq_zero (fun y => A y i) (hlap i) x

end YangMills.RG
