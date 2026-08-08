import YangMills.RG.BalabanCMP116Localization

/-!
# Exact second-derivative support of CMP116 localized activities

If a function depends only on a finite coordinate set `S`, then its mixed
line derivative vanishes whenever either direction is zero on `S`.  This file
proves that statement directly by identifying the corresponding scalar line
with a constant function.  No differentiability hypothesis is needed: Lean's
total `deriv` is zero on the resulting constant line.

Applied to `BalabanCMP116LocalizedActivityFamily`, this gives the exact support
statement expected of the quadratic kernel obtained by differentiating a
localized activity:

`b notin activeSupport or b' notin activeSupport -> Q(b,b') = 0`.

Honest scope: the quadratic operator supplied to
`cmp116Eq142PhysicalPotentialTerm` is not yet definitionally identified with
this mixed derivative.  The theorem below closes the calculus consequence of
locality; the physical equation-(1.42) dictionary remains a separate task.
-/

namespace YangMills.RG

noncomputable section

/-- Nested real line derivative in two field directions.  The codomain may be
real or complex (regarded as a real normed space). -/
def cmp116MixedLineSecondDerivative
    {I V W : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : (I → V) → W) (x u v : I → V) : W :=
  deriv (fun s : ℝ => deriv (fun t : ℝ => f (x + s • u + t • v)) 0) 0

/-- If the inner direction vanishes on every coordinate seen by `f`, the
inner line is constant and the mixed derivative is zero. -/
theorem cmp116MixedLineSecondDerivative_eq_zero_of_innerDirection
    {I V W : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : Finset I) (f : (I → V) → W) (x u v : I → V)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    (hv : ∀ i ∈ S, v i = 0) :
    cmp116MixedLineSecondDerivative f x u v = 0 := by
  unfold cmp116MixedLineSecondDerivative
  have hinner :
      (fun s : ℝ => deriv (fun t : ℝ => f (x + s • u + t • v)) 0) =
        fun _ => 0 := by
    funext s
    have hline :
        (fun t : ℝ => f (x + s • u + t • v)) =
          fun _ => f (x + s • u) := by
      funext t
      apply hlocal
      intro i hi
      simp [hv i hi]
    rw [hline]
    simp
  rw [hinner]
  simp

/-- If the outer direction vanishes on every coordinate seen by `f`, all
inner derivatives are equal and the outer derivative is zero. -/
theorem cmp116MixedLineSecondDerivative_eq_zero_of_outerDirection
    {I V W : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : Finset I) (f : (I → V) → W) (x u v : I → V)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    (hu : ∀ i ∈ S, u i = 0) :
    cmp116MixedLineSecondDerivative f x u v = 0 := by
  unfold cmp116MixedLineSecondDerivative
  have houter :
      (fun s : ℝ => deriv (fun t : ℝ => f (x + s • u + t • v)) 0) =
        fun _ => deriv (fun t : ℝ => f (x + t • v)) 0 := by
    funext s
    congr 1
    funext t
    apply hlocal
    intro i hi
    simp [hu i hi]
  rw [houter]
  simp

/-- Coordinate kernel obtained by taking the mixed line derivative in two
single-coordinate directions. -/
def cmp116LocalizedQuadraticKernel
    {I V W : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : (I → V) → W) (x : I → V)
    (i : I) (a : V) (j : I) (b : V) : W :=
  cmp116MixedLineSecondDerivative f x (Pi.single i a) (Pi.single j b)

theorem cmp116LocalizedQuadraticKernel_eq_zero_of_left_not_mem
    {I V W : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : Finset I) (f : (I → V) → W) (x : I → V)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    {i j : I} (a b : V) (hi : i ∉ S) :
    cmp116LocalizedQuadraticKernel f x i a j b = 0 := by
  apply cmp116MixedLineSecondDerivative_eq_zero_of_outerDirection S
  · exact hlocal
  · intro k hk
    simp [ne_of_mem_of_not_mem hk hi]

theorem cmp116LocalizedQuadraticKernel_eq_zero_of_right_not_mem
    {I V W : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : Finset I) (f : (I → V) → W) (x : I → V)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    {i j : I} (a b : V) (hj : j ∉ S) :
    cmp116LocalizedQuadraticKernel f x i a j b = 0 := by
  apply cmp116MixedLineSecondDerivative_eq_zero_of_innerDirection S
  · exact hlocal
  · intro k hk
    simp [ne_of_mem_of_not_mem hk hj]

/-- Exact two-sided kernel support: an entry vanishes when either coordinate
lies outside the dependency set. -/
theorem cmp116LocalizedQuadraticKernel_eq_zero_of_not_mem
    {I V W : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : Finset I) (f : (I → V) → W) (x : I → V)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    {i j : I} (a b : V) (hij : i ∉ S ∨ j ∉ S) :
    cmp116LocalizedQuadraticKernel f x i a j b = 0 := by
  rcases hij with hi | hj
  · exact cmp116LocalizedQuadraticKernel_eq_zero_of_left_not_mem
      S f x hlocal a b hi
  · exact cmp116LocalizedQuadraticKernel_eq_zero_of_right_not_mem
      S f x hlocal a b hj

/-- Mixed coordinate derivative of the literal global evaluation of one
localized CMP116 activity. -/
noncomputable def BalabanCMP116LocalizedActivityFamily.activityQuadraticKernel
    {Bond : Type*} [Fintype Bond] [DecidableEq Bond]
    {lieDim : ℕ} {Psi : Bond → Type*} {I : Type*}
    (F : BalabanCMP116LocalizedActivityFamily Bond lieDim Psi I)
    (i : I) (psi : ∀ b, Psi b)
    (X : ∀ _ : Bond, Fin lieDim → ℝ)
    (b : Bond) (a : Fin lieDim → ℝ)
    (b' : Bond) (a' : Fin lieDim → ℝ) : ℂ :=
  cmp116LocalizedQuadraticKernel
    (fun X' => (F.activity i).globalEval psi X') X b a b' a'

/-- The quadratic kernel obtained by differentiating a localized activity has
the exact bond support asserted by the source locality statement. -/
theorem BalabanCMP116LocalizedActivityFamily.activityQuadraticKernel_eq_zero_of_not_mem
    {Bond : Type*} [Fintype Bond] [DecidableEq Bond]
    {lieDim : ℕ} {Psi : Bond → Type*} {I : Type*}
    (F : BalabanCMP116LocalizedActivityFamily Bond lieDim Psi I)
    (i : I) (psi : ∀ b, Psi b)
    (X : ∀ _ : Bond, Fin lieDim → ℝ)
    {b b' : Bond} (a a' : Fin lieDim → ℝ)
    (h : b ∉ F.activeSupport i ∨ b' ∉ F.activeSupport i) :
    F.activityQuadraticKernel i psi X b a b' a' = 0 := by
  apply cmp116LocalizedQuadraticKernel_eq_zero_of_not_mem
      (F.activeSupport i) _ X _ a a' h
  intro z w hzw
  exact F.activity_globalEval_eq_of_agreeOn_activeSupport i
    (fun _ _ => rfl) hzw

end

end YangMills.RG
