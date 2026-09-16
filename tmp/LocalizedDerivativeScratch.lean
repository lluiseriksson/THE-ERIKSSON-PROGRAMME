import YangMills.RG.BalabanCMP116Eq219SourceGeometry
import YangMills.RG.BalabanCMP116Localization

namespace YangMills.RG

open scoped BigOperators

noncomputable section

def testMixedLineSecondDerivative
    {I V W : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : (I → V) → W) (x u v : I → V) : W :=
  deriv (fun s : ℝ => deriv (fun t : ℝ => f (x + s • u + t • v)) 0) 0

theorem testMixedLineSecondDerivative_eq_zero_of_innerDirection
    {I V W : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : Finset I) (f : (I → V) → W) (x u v : I → V)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    (hv : ∀ i ∈ S, v i = 0) :
    testMixedLineSecondDerivative f x u v = 0 := by
  unfold testMixedLineSecondDerivative
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

theorem testMixedLineSecondDerivative_eq_zero_of_outerDirection
    {I V W : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : Finset I) (f : (I → V) → W) (x u v : I → V)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    (hu : ∀ i ∈ S, u i = 0) :
    testMixedLineSecondDerivative f x u v = 0 := by
  unfold testMixedLineSecondDerivative
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

def testLocalizedQuadraticKernel
    {I V W : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : (I → V) → W) (x : I → V)
    (i : I) (a : V) (j : I) (b : V) : W :=
  testMixedLineSecondDerivative f x (Pi.single i a) (Pi.single j b)

theorem testLocalizedQuadraticKernel_eq_zero_of_left_not_mem
    {I V W : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : Finset I) (f : (I → V) → W) (x : I → V)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    {i j : I} (a b : V) (hi : i ∉ S) :
    testLocalizedQuadraticKernel f x i a j b = 0 := by
  apply testMixedLineSecondDerivative_eq_zero_of_outerDirection S
  · exact hlocal
  · intro k hk
    simp [ne_of_mem_of_not_mem hk hi]

theorem testLocalizedQuadraticKernel_eq_zero_of_right_not_mem
    {I V W : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : Finset I) (f : (I → V) → W) (x : I → V)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    {i j : I} (a b : V) (hj : j ∉ S) :
    testLocalizedQuadraticKernel f x i a j b = 0 := by
  apply testMixedLineSecondDerivative_eq_zero_of_innerDirection S
  · exact hlocal
  · intro k hk
    simp [ne_of_mem_of_not_mem hk hj]

theorem testLocalizedQuadraticKernel_eq_zero_of_not_mem
    {I V W : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : Finset I) (f : (I → V) → W) (x : I → V)
    (hlocal : ∀ {z w : I → V}, (∀ i ∈ S, z i = w i) → f z = f w)
    {i j : I} (a b : V) (hij : i ∉ S ∨ j ∉ S) :
    testLocalizedQuadraticKernel f x i a j b = 0 := by
  rcases hij with hi | hj
  · exact testLocalizedQuadraticKernel_eq_zero_of_left_not_mem
      S f x hlocal a b hi
  · exact testLocalizedQuadraticKernel_eq_zero_of_right_not_mem
      S f x hlocal a b hj

noncomputable def BalabanCMP116LocalizedActivityFamily.testActivityQuadraticKernel
    {Bond : Type*} [Fintype Bond] [DecidableEq Bond]
    {lieDim : ℕ} {Psi : Bond → Type*} {I : Type*}
    (F : BalabanCMP116LocalizedActivityFamily Bond lieDim Psi I)
    (i : I) (psi : ∀ b, Psi b)
    (X : ∀ _ : Bond, Fin lieDim → ℝ)
    (b : Bond) (a : Fin lieDim → ℝ)
    (b' : Bond) (a' : Fin lieDim → ℝ) : ℂ :=
  testLocalizedQuadraticKernel
    (fun X' => (F.activity i).globalEval psi X') X b a b' a'

theorem BalabanCMP116LocalizedActivityFamily.testActivityQuadraticKernel_eq_zero_of_not_mem
    {Bond : Type*} [Fintype Bond] [DecidableEq Bond]
    {lieDim : ℕ} {Psi : Bond → Type*} {I : Type*}
    (F : BalabanCMP116LocalizedActivityFamily Bond lieDim Psi I)
    (i : I) (psi : ∀ b, Psi b)
    (X : ∀ _ : Bond, Fin lieDim → ℝ)
    {b b' : Bond} (a a' : Fin lieDim → ℝ)
    (h : b ∉ F.activeSupport i ∨ b' ∉ F.activeSupport i) :
    F.testActivityQuadraticKernel i psi X b a b' a' = 0 := by
  apply testLocalizedQuadraticKernel_eq_zero_of_not_mem
      (F.activeSupport i) _ X _ a a' h
  intro z w hzw
  exact F.activity_globalEval_eq_of_agreeOn_activeSupport i
    (fun _ _ => rfl) hzw

end

end YangMills.RG
