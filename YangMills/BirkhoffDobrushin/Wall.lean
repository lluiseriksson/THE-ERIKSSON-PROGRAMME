import Mathlib

/-!
# Birkhoff--Dobrushin tensor wall

Machine-checked algebraic core of the paper *Local Tanh, Global Wall*.

The file formalizes:

* the scalar identity forcing reciprocal extrema in the sharp
  total-variation--Hilbert comparison;
* the endpoint rigidity of equality in the chord bound, including its
  finite weighted-sum form;
* factorization of projective cross-ratios under tensor products;
* preservation of a realized cross-ratio maximum under tensor products;
* the hyperbolic addition law for Birkhoff coefficients;
* the finite conditioning step behind volume-independent coordinate
  contraction.

The probability normalization and analytic Birkhoff--Hopf theorem remain
external classical inputs. No claim about a volume-uniform projective gap is
made.
-/

namespace YangMills.BirkhoffDobrushin

section SharpEquality

/-- The pointwise slack in the chord estimate for the positive part of r - 1. -/
noncomputable def chordSlack (m M r : ℝ) : ℝ :=
  (M - 1) * (r - m) - (M - m) * max (r - 1) 0

/-- The elementary square identity behind the sharp Hilbert-to-TV bound. -/
theorem hilbertGapIdentity (a b : ℝ) :
    (a - b) ^ 2 - (a ^ 2 - 1) * (1 - b ^ 2) = (a * b - 1) ^ 2 := by
  ring

/-- Equality in the scalar Hilbert gap forces reciprocal square-root extrema. -/
theorem hilbertGapEquality_iff (a b : ℝ) :
    (a - b) ^ 2 = (a ^ 2 - 1) * (1 - b ^ 2) ↔ a * b = 1 := by
  constructor
  · intro h
    have hsquare : (a * b - 1) ^ 2 = 0 := by
      nlinarith [hilbertGapIdentity a b]
    nlinarith [sq_nonneg (a * b - 1)]
  · intro h
    nlinarith [hilbertGapIdentity a b]

/-- The chord slack is nonnegative between the two likelihood-ratio extrema. -/
theorem chordSlack_nonneg {m M r : ℝ}
    (hm : m < 1) (hM : 1 < M) (hmr : m ≤ r) (hrM : r ≤ M) :
    0 ≤ chordSlack m M r := by
  unfold chordSlack
  by_cases hr : r ≤ 1
  · rw [max_eq_right (sub_nonpos.mpr hr)]
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hM)) (sub_nonneg.mpr hmr)]
  · have h1r : 1 ≤ r := le_of_not_ge hr
    rw [max_eq_left (sub_nonneg.mpr h1r)]
    have hid :
        (M - 1) * (r - m) - (M - m) * (r - 1) =
          (1 - m) * (M - r) := by
      ring
    rw [hid]
    exact mul_nonneg (sub_nonneg.mpr (le_of_lt hm)) (sub_nonneg.mpr hrM)

/-- Equality in the pointwise chord bound occurs only at an endpoint. -/
theorem chordSlack_eq_zero_iff {m M r : ℝ}
    (hm : m < 1) (hM : 1 < M) (hmr : m ≤ r) (hrM : r ≤ M) :
    chordSlack m M r = 0 ↔ r = m ∨ r = M := by
  constructor
  · intro hz
    unfold chordSlack at hz
    by_cases hr : r ≤ 1
    · rw [max_eq_right (sub_nonpos.mpr hr)] at hz
      left
      nlinarith
    · have h1r : 1 ≤ r := le_of_not_ge hr
      rw [max_eq_left (sub_nonneg.mpr h1r)] at hz
      right
      nlinarith
  · intro hr
    rcases hr with rfl | rfl
    · unfold chordSlack
      rw [max_eq_right (sub_nonpos.mpr (le_of_lt hm))]
      ring
    · unfold chordSlack
      rw [max_eq_left (sub_nonneg.mpr (le_of_lt hM))]
      ring

/--
If a strictly positive weighted sum of chord slacks vanishes, every
likelihood ratio is one of the two extrema.
-/
theorem endpoint_of_weighted_chord_equality
    {ι : Type*} [Fintype ι] (q r : ι → ℝ) {m M : ℝ}
    (hq : ∀ i, 0 < q i)
    (hm : m < 1) (hM : 1 < M)
    (hmr : ∀ i, m ≤ r i) (hrM : ∀ i, r i ≤ M)
    (hsum : ∑ i, q i * chordSlack m M (r i) = 0) :
    ∀ i, r i = m ∨ r i = M := by
  intro i
  have hnonneg :
      ∀ j ∈ (Finset.univ : Finset ι),
        0 ≤ q j * chordSlack m M (r j) := by
    intro j _
    exact mul_nonneg (le_of_lt (hq j))
      (chordSlack_nonneg hm hM (hmr j) (hrM j))
  have hterm : q i * chordSlack m M (r i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
      i (Finset.mem_univ i)
  have hslack : chordSlack m M (r i) = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hq i))
  exact (chordSlack_eq_zero_iff hm hM (hmr i) (hrM i)).mp hslack

end SharpEquality

section TensorCrossRatios

variable {X Y U V : Type*}

/-- Projective cross-ratio of four entries of a positive matrix. -/
noncomputable def crossRatio (A : X → Y → ℝ)
    (x x' : X) (y y' : Y) : ℝ :=
  A x y * A x' y' / (A x y' * A x' y)

/-- Kronecker product in function form. -/
noncomputable def tensorMatrix
    (A : X → Y → ℝ) (B : U → V → ℝ) :
    X × U → Y × V → ℝ :=
  fun xu yv => A xu.1 yv.1 * B xu.2 yv.2

/-- Positive matrices have positive projective cross-ratios. -/
theorem crossRatio_pos (A : X → Y → ℝ)
    (hA : ∀ x y, 0 < A x y)
    (x x' : X) (y y' : Y) :
    0 < crossRatio A x x' y y' := by
  unfold crossRatio
  exact div_pos (mul_pos (hA x y) (hA x' y'))
    (mul_pos (hA x y') (hA x' y))

/-- Every tensor cross-ratio factors into the cross-ratios of its factors. -/
theorem crossRatio_tensor
    (A : X → Y → ℝ) (B : U → V → ℝ)
    (hA : ∀ x y, 0 < A x y) (hB : ∀ u v, 0 < B u v)
    (x x' : X) (u u' : U) (y y' : Y) (v v' : V) :
    crossRatio (tensorMatrix A B) (x, u) (x', u') (y, v) (y', v') =
      crossRatio A x x' y y' * crossRatio B u u' v v' := by
  unfold crossRatio tensorMatrix
  field_simp [ne_of_gt (hA x y'), ne_of_gt (hA x' y),
    ne_of_gt (hB u v'), ne_of_gt (hB u' v)]

/-- A number is a realized global maximum of the matrix cross-ratios. -/
def IsCrossRatioMaximum (A : X → Y → ℝ) (θ : ℝ) : Prop :=
  (∀ x x' y y', crossRatio A x x' y y' ≤ θ) ∧
    ∃ x x' y y', crossRatio A x x' y y' = θ

/--
Realized projective cross-ratio maxima multiply under tensor products.
This is the order-theoretic content of theta(A tensor B) = theta(A) theta(B).
-/
theorem isCrossRatioMaximum_tensor
    (A : X → Y → ℝ) (B : U → V → ℝ)
    (hA : ∀ x y, 0 < A x y) (hB : ∀ u v, 0 < B u v)
    {θA θB : ℝ}
    (hmaxA : IsCrossRatioMaximum A θA)
    (hmaxB : IsCrossRatioMaximum B θB) :
    IsCrossRatioMaximum (tensorMatrix A B) (θA * θB) := by
  rcases hmaxA with ⟨hupperA, ⟨x, x', y, y', hattainA⟩⟩
  rcases hmaxB with ⟨hupperB, ⟨u, u', v, v', hattainB⟩⟩
  have hθA : 0 ≤ θA := by
    rw [← hattainA]
    exact le_of_lt (crossRatio_pos A hA x x' y y')
  constructor
  · rintro ⟨x₁, u₁⟩ ⟨x₂, u₂⟩ ⟨y₁, v₁⟩ ⟨y₂, v₂⟩
    rw [crossRatio_tensor A B hA hB]
    exact mul_le_mul
      (hupperA x₁ x₂ y₁ y₂)
      (hupperB u₁ u₂ v₁ v₂)
      (le_of_lt (crossRatio_pos B hB u₁ u₂ v₁ v₂))
      hθA
  · refine ⟨(x, u), (x', u'), (y, v), (y', v'), ?_⟩
    rw [crossRatio_tensor A B hA hB, hattainA, hattainB]

end TensorCrossRatios

section HyperbolicLaw

/--
The rational form of the Birkhoff coefficient when s is the square root of
the maximal cross-ratio.
-/
noncomputable def birkhoffRatio (s : ℝ) : ℝ := (s - 1) / (s + 1)

/-- The denominator in hyperbolic addition is positive for positive inputs. -/
theorem hyperbolicDenominator_pos {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    0 < 1 + birkhoffRatio s * birkhoffRatio t := by
  have hs1 : s + 1 ≠ 0 := ne_of_gt (by linarith)
  have ht1 : t + 1 ≠ 0 := ne_of_gt (by linarith)
  have hid :
      1 + birkhoffRatio s * birkhoffRatio t =
        2 * (s * t + 1) / ((s + 1) * (t + 1)) := by
    unfold birkhoffRatio
    field_simp [hs1, ht1]
    ring
  rw [hid]
  positivity

/--
Multiplication of square-root cross-ratios becomes hyperbolic addition of
Birkhoff coefficients.
-/
theorem birkhoffRatio_mul {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    birkhoffRatio (s * t) =
      (birkhoffRatio s + birkhoffRatio t) /
        (1 + birkhoffRatio s * birkhoffRatio t) := by
  apply (eq_div_iff (ne_of_gt (hyperbolicDenominator_pos hs ht))).2
  unfold birkhoffRatio
  field_simp [ne_of_gt (by positivity : 0 < s + 1),
    ne_of_gt (by positivity : 0 < t + 1),
    ne_of_gt (by positivity : 0 < s * t + 1)]
  ring

end HyperbolicLaw

section LocalContraction

/--
A fiberwise contraction bound survives averaging over all outside
coordinates. This is the finite conditioning step used to lift a one-site
Dobrushin bound to a coordinate oscillation bound in a product kernel.
-/
theorem coordinateContraction_of_fiberwise
    {Z : Type*} [Fintype Z]
    (w g : Z → ℝ) {δ B : ℝ}
    (hw : ∀ z, 0 ≤ w z)
    (hsumw : ∑ z, w z = 1)
    (hg : ∀ z, |g z| ≤ δ * B) :
    |∑ z, w z * g z| ≤ δ * B := by
  calc
    |∑ z, w z * g z|
        ≤ ∑ z, |w z * g z| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z, w z * |g z| := by
      apply Finset.sum_congr rfl
      intro z _
      rw [abs_mul, abs_of_nonneg (hw z)]
    _ ≤ ∑ z, w z * (δ * B) := by
      exact Finset.sum_le_sum fun z _ =>
        mul_le_mul_of_nonneg_left (hg z) (hw z)
    _ = (∑ z, w z) * (δ * B) := by
      rw [Finset.sum_mul]
    _ = δ * B := by
      rw [hsumw, one_mul]

/--
The averaging step is exact on a function independent of the outside
coordinates, which is the standard saturation witness for coordinate
contraction.
-/
theorem weightedAverage_constant
    {Z : Type*} [Fintype Z] (w : Z → ℝ)
    (hsumw : ∑ z, w z = 1) (c : ℝ) :
    ∑ z, w z * c = c := by
  calc
    ∑ z, w z * c = (∑ z, w z) * c := by rw [Finset.sum_mul]
    _ = c := by rw [hsumw, one_mul]

end LocalContraction

end YangMills.BirkhoffDobrushin
