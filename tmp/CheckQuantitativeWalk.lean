import YangMills.RG.BalabanCMP99PatchedParametrixFixedRateSummability

open scoped BigOperators

namespace YangMills.RG

universe u v w z

theorem test_tsum_cmp99AnchoredWalk_radialMajorant_of_term_le
    {Label : Type u} {Domain : Type v} {Cube : Type w} {E : Type z}
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Cube]
    [NormedAddCommGroup E]
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (X0 : Domain) (domainActive : Domain → Finset Cube)
    (term : CMP99AnchoredWalk successors X0 → E)
    (K B : ℕ) (A rho Rweak : ℝ)
    (hK : ∀ X, (successors X).card ≤ K)
    (hB : ∀ X, (domainActive X).card ≤ B)
    (hA : 0 ≤ A) (hrho : 0 ≤ rho) (hRweak : 1 ≤ Rweak)
    (hsmall : (K : ℝ) * rho * Rweak ^ B < 1)
    (hterm : ∀ walk, ‖term walk‖ ≤ A * rho ^ walk.1) :
    (∑' walk : CMP99AnchoredWalk successors X0,
      Rweak ^ (walk.active domainActive).card * ‖term walk‖) ≤
      (A * Rweak ^ B) *
        (1 - (K : ℝ) * rho * Rweak ^ B)⁻¹ := by
  let q : ℝ := (K : ℝ) * rho * Rweak ^ B
  let f : CMP99AnchoredWalk successors X0 → ℝ := fun walk =>
    Rweak ^ (walk.active domainActive).card * ‖term walk‖
  have hq : 0 ≤ q := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg K) hrho)
    (pow_nonneg (by linarith) B)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq]
    exact hsmall
  have hf : Summable f := by
    exact summable_cmp99AnchoredWalk_radialMajorant_of_term
      successors X0 domainActive term K B A rho Rweak
      hK hB hA hrho hRweak hsmall hterm
  have hgeom : Summable fun n : ℕ => A * Rweak ^ B * q ^ n := by
    exact (summable_geometric_of_norm_lt_one hqnorm).mul_left
      (A * Rweak ^ B)
  rw [show (∑' walk : CMP99AnchoredWalk successors X0,
      Rweak ^ (walk.active domainActive).card * ‖term walk‖) =
      ∑' walk : CMP99AnchoredWalk successors X0, f walk by rfl]
  rw [hf.tsum_sigma]
  calc
    (∑' n : ℕ, ∑' walk : ↥(cmp99AdmissibleTails successors X0 n),
        f ⟨n, walk⟩) ≤
        ∑' n : ℕ, A * Rweak ^ B * q ^ n := by
      apply Summable.tsum_le_tsum
      · intro n
        rw [tsum_fintype]
        dsimp [f]
        calc
          ∑ walk : ↥(cmp99AdmissibleTails successors X0 n),
              Rweak ^ (CMP99AnchoredWalk.active domainActive
                (⟨n, walk⟩ : CMP99AnchoredWalk successors X0)).card *
                ‖term (⟨n, walk⟩ : CMP99AnchoredWalk successors X0)‖
              ≤ ∑ _walk : ↥(cmp99AdmissibleTails successors X0 n),
                Rweak ^ (B * (n + 1)) * (A * rho ^ n) := by
            apply Finset.sum_le_sum
            intro walk _
            exact mul_le_mul
              (pow_le_pow_right₀ hRweak
                (CMP99AnchoredWalk.card_active_le_mul_length_add_one
                  domainActive B hB
                  (⟨n, walk⟩ : CMP99AnchoredWalk successors X0)))
              (hterm ⟨n, walk⟩) (norm_nonneg _)
              (pow_nonneg (by linarith) _)
          _ = ((cmp99AdmissibleTails successors X0 n).card : ℝ) *
              (Rweak ^ (B * (n + 1)) * (A * rho ^ n)) := by simp
          _ ≤ ((K ^ n : ℕ) : ℝ) *
              (Rweak ^ (B * (n + 1)) * (A * rho ^ n)) := by
            gcongr
            exact_mod_cast
              card_cmp99AdmissibleTails_le_pow successors K hK n X0
          _ = A * Rweak ^ B * q ^ n := by
            dsimp [q]
            push_cast
            rw [pow_mul, pow_succ]
            ring
      · exact hf.sigma
      · exact hgeom
    _ = (A * Rweak ^ B) * (1 - q)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hqnorm]
    _ = (A * Rweak ^ B) *
        (1 - (K : ℝ) * rho * Rweak ^ B)⁻¹ := by
      rfl

end YangMills.RG
