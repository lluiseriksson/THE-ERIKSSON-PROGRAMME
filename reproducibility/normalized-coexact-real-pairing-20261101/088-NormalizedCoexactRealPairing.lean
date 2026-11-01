import YangMills.RG.NormalizedCoexactPacket

/-! Real linearity and the full coefficient inner-product identity for the
actual normalized coexact synthesis. No Gram field is assumed. -/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]

noncomputable def normalizedScalarSynthesis (R : ℕ) :
    (CoexactPositiveIndex d R → ℂ) →ₗ[ℂ] ((Fin (d + 2) → ZMod n) → ℂ) where
  toFun c := characterSynthesis (positiveCoexactCharacter (n := n) R)
    (fun k => c k / (positiveCoexactNormalization (n := n) R k : ℂ))
  map_add' c b := by
    funext x
    simp [characterSynthesis, add_div, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext x
    simp only [characterSynthesis, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      mul_div_assoc, mul_assoc, Finset.mul_sum]

noncomputable def normalizedCoexactRealLinear (hNc : 2 ≤ Nc) (R : ℕ) :
    (CoexactPositiveIndex d R → ℂ) →ₗ[ℝ] PhysicalGaugeOneCochain (d + 2) n Nc :=
  (coexactFlatMap hNc (0 : Fin (d + 2)) (Fin.succ 0)).comp
    ((normalizedScalarSynthesis (n := n) R).restrictScalars ℝ)

theorem normalizedCoexactSynthesis_add (hNc : 2 ≤ Nc) (R : ℕ)
    (c b : CoexactPositiveIndex d R → ℂ) :
    normalizedCoexactSynthesis (n := n) hNc R (c + b) =
      normalizedCoexactSynthesis (n := n) hNc R c +
        normalizedCoexactSynthesis (n := n) hNc R b :=
  (normalizedCoexactRealLinear (n := n) hNc R).map_add c b

theorem normalizedCoexactSynthesis_real_smul (hNc : 2 ≤ Nc) (R : ℕ)
    (a : ℝ) (c : CoexactPositiveIndex d R → ℂ) :
    normalizedCoexactSynthesis (n := n) hNc R (a • c) =
      a • normalizedCoexactSynthesis (n := n) hNc R c :=
  (normalizedCoexactRealLinear (n := n) hNc R).map_smul a c

theorem normalizedCoexactSynthesis_real_pairing (hNc : 2 ≤ Nc)
    (R : ℕ) (hR : 2 * R < n) (c b : CoexactPositiveIndex d R → ℂ) :
    inner ℝ (normalizedCoexactSynthesis (n := n) hNc R c)
      (normalizedCoexactSynthesis (n := n) hNc R b) =
        ∑ k, inner ℝ (c k) (b k) := by
  have h := normalizedCoexactSynthesis_norm_sq (n := n) hNc R hR (c + b)
  rw [normalizedCoexactSynthesis_add] at h
  simp only [← real_inner_self_eq_norm_sq, Pi.add_apply, inner_add_left,
    inner_add_right, Finset.sum_add_distrib] at h
  have hs : (∑ k, inner ℝ (b k) (c k)) = ∑ k, inner ℝ (c k) (b k) := by
    apply Finset.sum_congr rfl
    intro k _
    exact real_inner_comm _ _
  rw [real_inner_comm (normalizedCoexactSynthesis (n := n) hNc R b)
    (normalizedCoexactSynthesis (n := n) hNc R c), hs] at h
  have hc := normalizedCoexactSynthesis_norm_sq (n := n) hNc R hR c
  have hb := normalizedCoexactSynthesis_norm_sq (n := n) hNc R hR b
  simp only [← real_inner_self_eq_norm_sq] at hc hb
  linarith
end YangMills.RG
