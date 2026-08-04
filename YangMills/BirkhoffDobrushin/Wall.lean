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
* the probability-normalized finite total-variation--Hilbert comparison,
  including its if-and-only-if equality classification.

The analytic Birkhoff--Hopf theorem remains an external classical input. No
claim about a volume-uniform projective gap is made.
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

section FiniteProbabilityComparison

/-- Total variation of two finite real vectors, in the probability convention. -/
noncomputable def totalVariation {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, |p i - q i|

/-- Likelihood ratio, used only under a strictly positive denominator. -/
noncomputable def likelihoodRatio {ι : Type*} (p q : ι → ℝ) (i : ι) : ℝ :=
  p i / q i

/-- The rational chord envelope between likelihood-ratio bounds `m` and `M`. -/
noncomputable def chordEnvelope (m M : ℝ) : ℝ :=
  (M - 1) * (1 - m) / (M - m)

/-- The square-root form of the Hilbert envelope. -/
noncomputable def rootEnvelope (a b : ℝ) : ℝ :=
  (a - b) / (a + b)

/-- Scalar positive-part decomposition of absolute value. -/
theorem abs_eq_two_mul_max_sub_self (x : ℝ) :
    |x| = 2 * max x 0 - x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_left hx]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', max_eq_right hx']
    ring

/-- A positive denominator recovers the numerator from its likelihood ratio. -/
theorem mul_likelihoodRatio {p q : ℝ} (hq : 0 < q) :
    q * (p / q) = p := by
  field_simp [ne_of_gt hq]

/-- Normalized likelihood ratios have weighted mean one. -/
theorem weighted_likelihoodRatio_sum
    {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hq : ∀ i, 0 < q i) (hsump : ∑ i, p i = 1) :
    ∑ i, q i * likelihoodRatio p q i = 1 := by
  calc
    ∑ i, q i * likelihoodRatio p q i = ∑ i, p i := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_likelihoodRatio (hq i)
    _ = 1 := hsump

/-- The centered likelihood ratio has weighted mean zero. -/
theorem weighted_likelihoodRatio_sub_one_sum
    {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hq : ∀ i, 0 < q i)
    (hsump : ∑ i, p i = 1) (hsumq : ∑ i, q i = 1) :
    ∑ i, q i * (likelihoodRatio p q i - 1) = 0 := by
  calc
    ∑ i, q i * (likelihoodRatio p q i - 1) =
        (∑ i, q i * likelihoodRatio p q i) - ∑ i, q i := by
      calc
        _ = ∑ i, (q i * likelihoodRatio p q i - q i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (∑ i, q i * likelihoodRatio p q i) - ∑ i, q i := by
          rw [Finset.sum_sub_distrib]
    _ = 0 := by rw [weighted_likelihoodRatio_sum p q hq hsump, hsumq, sub_self]

/-- For normalized positive vectors, total variation is the positive-part expectation. -/
theorem totalVariation_eq_positivePart
    {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hq : ∀ i, 0 < q i)
    (hsump : ∑ i, p i = 1) (hsumq : ∑ i, q i = 1) :
    totalVariation p q =
      ∑ i, q i * max (likelihoodRatio p q i - 1) 0 := by
  have hpoint : ∀ i, |p i - q i| =
      q i * |likelihoodRatio p q i - 1| := by
    intro i
    have hid : p i - q i = q i * (likelihoodRatio p q i - 1) := by
      unfold likelihoodRatio
      rw [mul_sub, mul_one, mul_likelihoodRatio (hq i)]
    rw [hid, abs_mul, abs_of_pos (hq i)]
  have hrewrite :
      ∑ i, q i * |likelihoodRatio p q i - 1| =
        2 * (∑ i, q i * max (likelihoodRatio p q i - 1) 0) -
          ∑ i, q i * (likelihoodRatio p q i - 1) := by
    calc
      ∑ i, q i * |likelihoodRatio p q i - 1| =
          ∑ i, (2 * (q i * max (likelihoodRatio p q i - 1) 0) -
            q i * (likelihoodRatio p q i - 1)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_eq_two_mul_max_sub_self]
        ring
      _ = (∑ i, 2 * (q i * max (likelihoodRatio p q i - 1) 0)) -
          ∑ i, q i * (likelihoodRatio p q i - 1) := by
        rw [Finset.sum_sub_distrib]
      _ = 2 * (∑ i, q i * max (likelihoodRatio p q i - 1) 0) -
          ∑ i, q i * (likelihoodRatio p q i - 1) := by
        rw [Finset.mul_sum]
  unfold totalVariation
  calc
    (1 / 2 : ℝ) * ∑ i, |p i - q i| =
        (1 / 2 : ℝ) * ∑ i, q i * |likelihoodRatio p q i - 1| := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact hpoint i
    _ = (1 / 2 : ℝ) *
        (2 * (∑ i, q i * max (likelihoodRatio p q i - 1) 0) -
          ∑ i, q i * (likelihoodRatio p q i - 1)) := by rw [hrewrite]
    _ = ∑ i, q i * max (likelihoodRatio p q i - 1) 0 := by
      rw [weighted_likelihoodRatio_sub_one_sum p q hq hsump hsumq]
      ring

/-- Exact sum identity whose nonnegativity gives the chord bound. -/
theorem weighted_chordSlack_sum
    {ι : Type*} [Fintype ι] (p q : ι → ℝ) (m M : ℝ)
    (hq : ∀ i, 0 < q i)
    (hsump : ∑ i, p i = 1) (hsumq : ∑ i, q i = 1) :
    ∑ i, q i * chordSlack m M (likelihoodRatio p q i) =
      (M - 1) * (1 - m) - (M - m) * totalVariation p q := by
  have hcenter :
      ∑ i, q i * (likelihoodRatio p q i - m) = 1 - m := by
    calc
      ∑ i, q i * (likelihoodRatio p q i - m) =
          (∑ i, q i * likelihoodRatio p q i) - m * ∑ i, q i := by
        calc
          _ = ∑ i, (q i * likelihoodRatio p q i - m * q i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = (∑ i, q i * likelihoodRatio p q i) - ∑ i, m * q i := by
            rw [Finset.sum_sub_distrib]
          _ = (∑ i, q i * likelihoodRatio p q i) - m * ∑ i, q i := by
            rw [Finset.mul_sum]
      _ = 1 - m := by rw [weighted_likelihoodRatio_sum p q hq hsump, hsumq, mul_one]
  rw [totalVariation_eq_positivePart p q hq hsump hsumq]
  unfold chordSlack
  calc
    ∑ i, q i *
        ((M - 1) * (likelihoodRatio p q i - m) -
          (M - m) * max (likelihoodRatio p q i - 1) 0) =
        (M - 1) * (∑ i, q i * (likelihoodRatio p q i - m)) -
          (M - m) *
            (∑ i, q i * max (likelihoodRatio p q i - 1) 0) := by
      calc
        _ = ∑ i, ((M - 1) * (q i * (likelihoodRatio p q i - m)) -
            (M - m) * (q i * max (likelihoodRatio p q i - 1) 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (∑ i, (M - 1) * (q i * (likelihoodRatio p q i - m))) -
            ∑ i, (M - m) * (q i * max (likelihoodRatio p q i - 1) 0) := by
          rw [Finset.sum_sub_distrib]
        _ = (M - 1) * (∑ i, q i * (likelihoodRatio p q i - m)) -
            (M - m) *
              (∑ i, q i * max (likelihoodRatio p q i - 1) 0) := by
          rw [Finset.mul_sum, Finset.mul_sum]
    _ = (M - 1) * (1 - m) - (M - m) *
        (∑ i, q i * max (likelihoodRatio p q i - 1) 0) := by rw [hcenter]

/-- The normalized finite chord estimate in total variation. -/
theorem totalVariation_le_chordEnvelope
    {ι : Type*} [Fintype ι] (p q : ι → ℝ) {m M : ℝ}
    (hq : ∀ i, 0 < q i)
    (hsump : ∑ i, p i = 1) (hsumq : ∑ i, q i = 1)
    (hm : m < 1) (hM : 1 < M)
    (hmr : ∀ i, m ≤ likelihoodRatio p q i)
    (hrM : ∀ i, likelihoodRatio p q i ≤ M) :
    totalVariation p q ≤ chordEnvelope m M := by
  have hnonneg : 0 ≤ ∑ i, q i * chordSlack m M (likelihoodRatio p q i) := by
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (le_of_lt (hq i))
        (chordSlack_nonneg hm hM (hmr i) (hrM i))
  rw [weighted_chordSlack_sum p q m M hq hsump hsumq] at hnonneg
  unfold chordEnvelope
  apply (le_div_iff₀ (sub_pos.mpr (lt_trans hm hM))).2
  nlinarith

/-- The chord envelope lies below the square-root Hilbert envelope. -/
theorem chordEnvelope_le_rootEnvelope {a b : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (h1a : 1 < a) :
    chordEnvelope (b ^ 2) (a ^ 2) ≤ rootEnvelope a b := by
  have hab : 0 < a - b := by linarith
  have habsum : 0 < a + b := by linarith
  have hsqdiff : 0 < a ^ 2 - b ^ 2 := by nlinarith
  unfold chordEnvelope rootEnvelope
  apply (div_le_div_iff₀ hsqdiff habsum).2
  nlinarith [hilbertGapIdentity a b, sq_nonneg (a * b - 1)]

/-- Equality between the two envelopes is exactly reciprocal square-root extrema. -/
theorem chordEnvelope_eq_rootEnvelope_iff {a b : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (h1a : 1 < a) :
    chordEnvelope (b ^ 2) (a ^ 2) = rootEnvelope a b ↔ a * b = 1 := by
  have hab : 0 < a - b := by linarith
  have habsum : 0 < a + b := by linarith
  have hsqdiff : 0 < a ^ 2 - b ^ 2 := by nlinarith
  constructor
  · intro h
    unfold chordEnvelope rootEnvelope at h
    field_simp [ne_of_gt hsqdiff, ne_of_gt habsum] at h
    apply (hilbertGapEquality_iff a b).mp
    nlinarith
  · intro h
    have hid := (hilbertGapEquality_iff a b).2 h
    unfold chordEnvelope rootEnvelope
    field_simp [ne_of_gt hsqdiff, ne_of_gt habsum]
    nlinarith

/--
Finite probability-normalized TV--Hilbert comparison with its complete
if-and-only-if equality classification.  The bounds `b^2` and `a^2` become
the likelihood-ratio extrema when the theorem is applied to the paper.
-/
theorem finite_totalVariation_hilbert_with_equality
    {ι : Type*} [Fintype ι] (p q : ι → ℝ) {a b : ℝ}
    (_hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hsump : ∑ i, p i = 1) (hsumq : ∑ i, q i = 1)
    (hb : 0 < b) (hb1 : b < 1) (h1a : 1 < a)
    (hlower : ∀ i, b ^ 2 ≤ likelihoodRatio p q i)
    (hupper : ∀ i, likelihoodRatio p q i ≤ a ^ 2) :
    totalVariation p q ≤ rootEnvelope a b ∧
      (totalVariation p q = rootEnvelope a b ↔
        a * b = 1 ∧
          ∀ i, likelihoodRatio p q i = b ^ 2 ∨
            likelihoodRatio p q i = a ^ 2) := by
  have hm : b ^ 2 < 1 := by nlinarith
  have hM : 1 < a ^ 2 := by nlinarith
  have htvChord := totalVariation_le_chordEnvelope p q hq hsump hsumq
    hm hM hlower hupper
  have hchordRoot := chordEnvelope_le_rootEnvelope hb hb1 h1a
  constructor
  · exact le_trans htvChord hchordRoot
  · constructor
    · intro heq
      have henv : chordEnvelope (b ^ 2) (a ^ 2) = rootEnvelope a b := by
        apply le_antisymm hchordRoot
        rw [← heq]
        exact htvChord
      have hab : a * b = 1 :=
        (chordEnvelope_eq_rootEnvelope_iff hb hb1 h1a).mp henv
      have htvEnv : totalVariation p q = chordEnvelope (b ^ 2) (a ^ 2) :=
        heq.trans henv.symm
      have hsumzero :
          ∑ i, q i * chordSlack (b ^ 2) (a ^ 2)
            (likelihoodRatio p q i) = 0 := by
        rw [weighted_chordSlack_sum p q (b ^ 2) (a ^ 2) hq hsump hsumq,
          htvEnv]
        unfold chordEnvelope
        field_simp [ne_of_gt (by nlinarith : 0 < a ^ 2 - b ^ 2)]
        ring
      refine ⟨hab, ?_⟩
      exact endpoint_of_weighted_chord_equality q (likelihoodRatio p q) hq
        hm hM hlower hupper hsumzero
    · rintro ⟨hab, hendpoint⟩
      have henv : chordEnvelope (b ^ 2) (a ^ 2) = rootEnvelope a b :=
        (chordEnvelope_eq_rootEnvelope_iff hb hb1 h1a).2 hab
      have hsumzero :
          ∑ i, q i * chordSlack (b ^ 2) (a ^ 2)
            (likelihoodRatio p q i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [(chordSlack_eq_zero_iff hm hM (hlower i) (hupper i)).2
          (hendpoint i), mul_zero]
      have hidentity := weighted_chordSlack_sum p q (b ^ 2) (a ^ 2)
        hq hsump hsumq
      rw [hsumzero] at hidentity
      have htvEnv : totalVariation p q = chordEnvelope (b ^ 2) (a ^ 2) := by
        unfold chordEnvelope
        apply (eq_div_iff (ne_of_gt (by nlinarith : 0 < a ^ 2 - b ^ 2))).2
        nlinarith
      exact htvEnv.trans henv

/-- A realized maximum formulation of the finite-kernel Dobrushin coefficient. -/
def IsDobrushinMaximum {X Y : Type*} [Fintype Y]
    (P : X → Y → ℝ) (δ : ℝ) : Prop :=
  (∀ x x', totalVariation (P x) (P x') ≤ δ) ∧
    ∃ x x', totalVariation (P x) (P x') = δ

/--
Kernel lift of the probability-normalized comparison.  The functions `a` and
`b` encode the square roots of the pairwise likelihood-ratio extrema; `τ` is
any common projective envelope.  Equality in the global comparison is
equivalent to a maximizing row pair that both reaches the global envelope and
has reciprocal two-block likelihood ratios.
-/
theorem finite_kernel_comparison_with_equality
    {X Y : Type*} [Fintype Y]
    (P : X → Y → ℝ) (a b : X → X → ℝ) {δ τ : ℝ}
    (hP : ∀ x y, 0 < P x y)
    (hstoch : ∀ x, ∑ y, P x y = 1)
    (hb : ∀ x x', 0 < b x x')
    (hb1 : ∀ x x', b x x' < 1)
    (h1a : ∀ x x', 1 < a x x')
    (hlower : ∀ x x' y,
      b x x' ^ 2 ≤ likelihoodRatio (P x) (P x') y)
    (hupper : ∀ x x' y,
      likelihoodRatio (P x) (P x') y ≤ a x x' ^ 2)
    (hglobal : ∀ x x', rootEnvelope (a x x') (b x x') ≤ τ)
    (hmax : IsDobrushinMaximum P δ) :
    δ ≤ τ ∧
      (δ = τ ↔
        ∃ x x',
          rootEnvelope (a x x') (b x x') = τ ∧
          a x x' * b x x' = 1 ∧
          ∀ y, likelihoodRatio (P x) (P x') y = b x x' ^ 2 ∨
            likelihoodRatio (P x) (P x') y = a x x' ^ 2) := by
  have hpair : ∀ x x',
      totalVariation (P x) (P x') ≤ rootEnvelope (a x x') (b x x') ∧
        (totalVariation (P x) (P x') = rootEnvelope (a x x') (b x x') ↔
          a x x' * b x x' = 1 ∧
            ∀ y, likelihoodRatio (P x) (P x') y = b x x' ^ 2 ∨
              likelihoodRatio (P x) (P x') y = a x x' ^ 2) := by
    intro x x'
    exact finite_totalVariation_hilbert_with_equality (P x) (P x')
      (hP x) (hP x') (hstoch x) (hstoch x')
      (hb x x') (hb1 x x') (h1a x x')
      (hlower x x') (hupper x x')
  rcases hmax with ⟨hdeltaUpper, ⟨xmax, xmax', hdeltaAttain⟩⟩
  have hδτ : δ ≤ τ := by
    rw [← hdeltaAttain]
    exact le_trans (hpair xmax xmax').1 (hglobal xmax xmax')
  constructor
  · exact hδτ
  · constructor
    · intro heq
      have htvTau : totalVariation (P xmax) (P xmax') = τ :=
        hdeltaAttain.trans heq
      have hrootTau : rootEnvelope (a xmax xmax') (b xmax xmax') = τ := by
        apply le_antisymm (hglobal xmax xmax')
        rw [← htvTau]
        exact (hpair xmax xmax').1
      have htvRoot : totalVariation (P xmax) (P xmax') =
          rootEnvelope (a xmax xmax') (b xmax xmax') :=
        htvTau.trans hrootTau.symm
      rcases (hpair xmax xmax').2.mp htvRoot with ⟨hab, hend⟩
      exact ⟨xmax, xmax', hrootTau, hab, hend⟩
    · rintro ⟨x, x', hrootTau, hab, hend⟩
      have htvRoot : totalVariation (P x) (P x') =
          rootEnvelope (a x x') (b x x') :=
        (hpair x x').2.mpr ⟨hab, hend⟩
      have htvTau : totalVariation (P x) (P x') = τ :=
        htvRoot.trans hrootTau
      apply le_antisymm hδτ
      rw [← htvTau]
      exact hdeltaUpper x x'

end FiniteProbabilityComparison

end YangMills.BirkhoffDobrushin
