import YangMills.RG.TorusFiniteSumEnergy

/-! Counting-measure Gram/Parseval and energy for actual character sums.
No orthogonality, norm comparison or energy bound is supplied as a hypothesis.
The physical real-cochain embedding and the quantitative multiplier estimate
are separate obligations. -/

namespace YangMills.RG

open scoped BigOperators

variable {G I J : Type*} [AddCommGroup G] [Fintype G] [Fintype I] [Fintype J]

theorem addChar_counting_gram (chi psi : AddChar G ℂ) :
    (∑ x, (starRingEnd ℂ) (chi x) * psi x) =
      if chi = psi then (Fintype.card G : ℂ) else 0 := by
  classical
  calc
    _ = ∑ x, (psi - chi) x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [AddChar.sub_apply', div_eq_mul_inv,
        Complex.inv_eq_conj (AddChar.norm_apply chi x)]
      ring
    _ = _ := by simpa [sub_eq_zero, eq_comm] using (AddChar.sum_eq_ite (psi - chi))

noncomputable def characterSynthesis (chi : I → AddChar G ℂ) (c : I → ℂ) : G → ℂ :=
  fun x => ∑ i, c i * chi i x

theorem character_synthesis_pairing (chi : I → AddChar G ℂ)
    (hc : Function.Injective chi) (c b : I → ℂ) :
    (∑ x, (starRingEnd ℂ) (characterSynthesis chi c x) * characterSynthesis chi b x) =
      (Fintype.card G : ℂ) * ∑ i, (starRingEnd ℂ) (c i) * b i := by
  classical
  calc
    _ = ∑ x, ∑ i, ∑ j,
        ((starRingEnd ℂ) (c i) * b j) * ((starRingEnd ℂ) (chi i x) * chi j x) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [characterSynthesis, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, ∑ j, ((starRingEnd ℂ) (c i) * b j) *
        (∑ x, (starRingEnd ℂ) (chi i x) * chi j x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = _ := by
      simp [addChar_counting_gram, hc.eq_iff, Finset.mul_sum,
        mul_comm, mul_left_comm, mul_assoc]

theorem character_synthesis_mass (chi : I → AddChar G ℂ)
    (hc : Function.Injective chi) (c : I → ℂ) :
    countingL2Mass (characterSynthesis chi c) =
      (Fintype.card G : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
  unfold countingL2Mass
  have h := character_synthesis_pairing chi hc c c
  simp only [Complex.conj_mul'] at h
  exact_mod_cast h

theorem character_synthesis_forwardEnergy (chi : I → AddChar G ℂ)
    (hc : Function.Injective chi) (c : I → ℂ) (a : G) :
    forwardShiftEnergy (characterSynthesis chi c) a =
      (Fintype.card G : ℝ) * ∑ i, ‖c i‖ ^ 2 * ‖chi i a - 1‖ ^ 2 := by
  classical
  have hf : (fun x => characterSynthesis chi c (x + a) - characterSynthesis chi c x) =
      characterSynthesis chi (fun i => c i * (chi i a - 1)) := by
    funext x
    simp only [characterSynthesis]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_sub, character_forward_difference]
    ring
  change countingL2Mass (fun x => characterSynthesis chi c (x + a) -
    characterSynthesis chi c x) = _
  rw [hf, character_synthesis_mass chi hc]
  simp only [norm_mul, mul_pow]

theorem character_synthesis_stencilEnergy [DecidableEq J] (chi : I → AddChar G ℂ)
    (hc : Function.Injective chi) (c : I → ℂ) (a : J → G) (j : J) :
    oneComponentStencilEnergy (characterSynthesis chi c) a j =
      (Fintype.card G : ℝ) * ∑ i, ‖c i‖ ^ 2 * (∑ t, ‖chi i (a t) - 1‖ ^ 2) := by
  classical
  rw [oneComponentStencilEnergy_eq]
  simp_rw [character_synthesis_forwardEnergy chi hc]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

variable {d n : ℕ} [NeZero n]

theorem centeredFourier_counting_mass (R : ℕ) (hR : 2 * R < n)
    (c : (Fin d → Fin (2 * R + 1)) → ℂ) :
    countingL2Mass (fun x => ∑ k, c k * centeredFourierProfile (d := d) (n := n) R k x) =
      (n ^ d : ℝ) * ∑ k, ‖c k‖ ^ 2 := by
  let chi := fun k : Fin d → Fin (2 * R + 1) =>
    torusFourierCharacter (centeredFourierFrequency (n := n) R k)
  have hc : Function.Injective chi := torusFourierCharacter_injective.comp
    (centeredFourierFrequency_injective R hR)
  simpa [characterSynthesis, chi, centeredFourierProfile] using
    (character_synthesis_mass chi hc c)

theorem centeredFourier_stencilEnergy (R : ℕ) (hR : 2 * R < n)
    (c : (Fin d → Fin (2 * R + 1)) → ℂ) (j : Fin d) :
    oneComponentStencilEnergy
      (fun x => ∑ k, c k * centeredFourierProfile (d := d) (n := n) R k x)
      (fun t => Pi.single t (1 : ZMod n)) j =
      (n ^ d : ℝ) * ∑ k, ‖c k‖ ^ 2 *
        (∑ t : Fin d, ‖centeredFourierProfile (d := d) (n := n) R k
          (Pi.single t (1 : ZMod n)) - 1‖ ^ 2) := by
  let chi := fun k : Fin d → Fin (2 * R + 1) =>
    torusFourierCharacter (centeredFourierFrequency (n := n) R k)
  have hc : Function.Injective chi := torusFourierCharacter_injective.comp
    (centeredFourierFrequency_injective R hR)
  simpa [characterSynthesis, chi, centeredFourierProfile] using
    (character_synthesis_stencilEnergy chi hc c (fun t => Pi.single t (1 : ZMod n)) j)

end YangMills.RG
