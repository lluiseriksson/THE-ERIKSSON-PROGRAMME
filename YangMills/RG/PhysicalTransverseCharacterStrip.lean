import YangMills.RG.PhysicalCharacterWeightDensity

/-! Constructed normalized transverse physical characters and their actual
orthonormality/dimension/energy sum. Positive trace/rank composition remains
separate; none of these conclusions is supplied as a band certificate. -/
namespace YangMills.RG
open Module
open scoped BigOperators RealInnerProductSpace

section Pairing
variable {d n Nc : ℕ} [NeZero d] [NeZero n] [NeZero Nc]

theorem sunComplexPlane_real_inner (hNc : 2 ≤ Nc) (z v : ℂ) :
    inner ℝ (sunComplexPlane hNc z) (sunComplexPlane hNc v) =
      z.re * v.re + z.im * v.im := by
  have h := norm_sub_sq_real (sunComplexPlane hNc z) (sunComplexPlane hNc v)
  rw [← sunComplexPlane_sub] at h
  simp only [sunComplexPlane_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at h
  nlinarith

theorem torusPhysicalEmbed_real_inner (hNc : 2 ≤ Nc) (j : Fin d)
    (f g : (Fin d → ZMod n) → ℂ) :
    inner ℝ (torusPhysicalEmbed hNc j f) (torusPhysicalEmbed hNc j g) =
      (∑ x, (starRingEnd ℂ) (f x) * g x).re := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  have hp (x : FinBox d n) (l : Fin d) :
      inner ℝ (torusPhysicalEmbed hNc j f (x,l)) (torusPhysicalEmbed hNc j g (x,l)) =
      if l = j then (f (finBoxZModEquiv d n x)).re * (g (finBoxZModEquiv d n x)).re +
        (f (finBoxZModEquiv d n x)).im * (g (finBoxZModEquiv d n x)).im else 0 := by
    by_cases hl : l = j <;> simp [torusPhysicalEmbed, hl, sunComplexPlane_real_inner]
  simp_rw [hp]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc
    _ = ∑ x : Fin d → ZMod n, ((f x).re * (g x).re + (f x).im * (g x).im) :=
      Equiv.sum_comp (finBoxZModEquiv d n) _
    _ = _ := by
      rw [show (∑ x, (starRingEnd ℂ) (f x) * g x).re =
        ∑ x, ((starRingEnd ℂ) (f x) * g x).re from map_sum Complex.reAddGroupHom _ _]
      apply Finset.sum_congr rfl
      intro x _
      simp [Complex.mul_re]

theorem physicalCharacter_real_inner (hNc : 2 ≤ Nc) (j : Fin d)
    (chi psi : AddChar (Fin d → ZMod n) ℂ) (z v : ℂ) :
    inner ℝ (physicalCharacterField hNc j chi z) (physicalCharacterField hNc j psi v) =
      if chi = psi then (n : ℝ)^d * (z.re * v.re + z.im * v.im) else 0 := by
  classical
  rw [physicalCharacterField, physicalCharacterField, torusPhysicalEmbed_real_inner]
  have hc : (∑ x, (starRingEnd ℂ) (z * chi x) * (v * psi x)) =
      ((starRingEnd ℂ) z * v) *
        (if chi = psi then (Fintype.card (Fin d → ZMod n) : ℂ) else 0) := by
    calc
      _ = ((starRingEnd ℂ) z * v) * ∑ x, (starRingEnd ℂ) (chi x) * psi x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [map_mul]
        ring
      _ = _ := by rw [addChar_counting_gram]
  rw [hc]
  by_cases heq : chi = psi
  · simp only [if_pos heq]
    have hcard : (Fintype.card (Fin d → ZMod n) : ℂ) = (((n : ℝ)^d : ℝ) : ℂ) := by simp
    rw [hcard, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    simp [Complex.mul_re] <;> ring
  · simp [heq]
end Pairing

section Strip
variable {d n Nc R : ℕ} [NeZero d] [NeZero n] [NeZero Nc]

def transversePhysicalFrequency (i : Fin d) (r : Fin R) : Fin d → ZMod n :=
  Pi.single i ((r.val + 1 : ℕ) : ZMod n)

noncomputable def transversePhysicalCharacter (i : Fin d) (r : Fin R) :
    AddChar (Fin d → ZMod n) ℂ :=
  torusFourierCharacter (transversePhysicalFrequency i r)

theorem transversePhysicalCharacter_step (i l : Fin d) (r : Fin R) :
    transversePhysicalCharacter (n := n) i r (Pi.single l (1 : ZMod n)) =
      if l = i then ZMod.stdAddChar ((r.val + 1 : ℕ) : ZMod n) else 1 := by
  classical
  have hu (k : Fin d → ZMod n) :
      torusFourierCharacter k (Pi.single l (1 : ZMod n)) = ZMod.stdAddChar (k l) := by
    simp [torusFourierCharacter, Pi.single_apply]
  rw [transversePhysicalCharacter, hu]
  by_cases hl : l = i <;> simp [transversePhysicalFrequency, Pi.single_apply, hl]

theorem transversePhysicalCharacter_injective (i : Fin d) (hR : R < n) :
    Function.Injective (transversePhysicalCharacter (n := n) (R := R) i) := by
  intro r s hrs
  have he : transversePhysicalFrequency (n := n) i r = transversePhysicalFrequency i s :=
    torusFourierCharacter_injective hrs
  have hr : r.val + 1 < n := by have := r.isLt; omega
  have hs : s.val + 1 < n := by have := s.isLt; omega
  have hz : ((r.val + 1 : ℕ) : ZMod n) = ((s.val + 1 : ℕ) : ZMod n) := by
    simpa [transversePhysicalFrequency, Pi.single_apply] using congrFun he i
  have hv := congrArg ZMod.val hz
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] at hv
  apply Fin.ext
  omega

noncomputable def physicalCharacterNormalization (d n : ℕ) : ℝ :=
  Real.sqrt (((n : ℝ)^d)⁻¹)

theorem physicalCharacterNormalization_sq :
    physicalCharacterNormalization d n ^ 2 = ((n : ℝ)^d)⁻¹ := by
  unfold physicalCharacterNormalization
  exact Real.sq_sqrt (by positivity)

theorem physicalCharacterNormalization_mass :
    physicalCharacterNormalization d n ^ 2 * (n : ℝ)^d = 1 := by
  rw [physicalCharacterNormalization_sq]
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  exact inv_mul_cancel₀ (ne_of_gt (pow_pos hn d))

def physicalCharacterQuadrature (b : Bool) : ℂ := if b then Complex.I else 1

theorem physicalCharacterQuadrature_norm (b : Bool) : ‖physicalCharacterQuadrature b‖ ^ 2 = 1 := by
  cases b <;> norm_num [physicalCharacterQuadrature]

noncomputable def normalizedTransversePhysicalCharacter (hNc : 2 ≤ Nc) (i j : Fin d)
    (r : Fin R) (b : Bool) : PhysicalGaugeOneCochain d n Nc :=
  physicalCharacterNormalization d n •
    physicalCharacterField hNc j (transversePhysicalCharacter i r) (physicalCharacterQuadrature b)

theorem normalizedTransversePhysicalCharacters_orthonormal (hNc : 2 ≤ Nc)
    (i j : Fin d) (hR : R < n) :
    Orthonormal ℝ (fun p : Fin R × Bool => normalizedTransversePhysicalCharacter
      (n := n) hNc i j p.1 p.2) := by
  classical
  apply orthonormal_iff_ite.mpr
  rintro ⟨r,b⟩ ⟨s,c⟩
  simp only [normalizedTransversePhysicalCharacter, real_inner_smul_left,
    real_inner_smul_right, physicalCharacter_real_inner]
  by_cases hrs : r = s
  · subst s
    cases b <;> cases c <;> simp [physicalCharacterQuadrature] <;>
      nlinarith [physicalCharacterNormalization_mass (d := d) (n := n)]
  · have hchi : transversePhysicalCharacter (n := n) i r ≠ transversePhysicalCharacter i s :=
      fun h => hrs (transversePhysicalCharacter_injective i hR h)
    have hp : (r,b) ≠ (s,c) := fun h => hrs (Prod.mk.inj h).1
    simp [hchi, hp]

theorem normalizedTransversePhysicalCharacter_div_zero (hNc : 2 ≤ Nc)
    (rho : SUNAdjointModel Nc) (i j : Fin d) (hij : i ≠ j) (r : Fin R) (b : Bool) :
    gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground d n Nc)
      (normalizedTransversePhysicalCharacter hNc i j r b) = 0 := by
  rw [normalizedTransversePhysicalCharacter, map_smul]
  have hj : transversePhysicalCharacter (n := n) i r (Pi.single j (1 : ZMod n)) = 1 := by
    rw [transversePhysicalCharacter_step]
    simp [Ne.symm hij]
  rw [physicalCharacter_div_zero hNc rho j _ _ hj, smul_zero]

theorem normalizedTransversePhysicalCharacters_span_finrank (hNc : 2 ≤ Nc)
    (i j : Fin d) (hR : R < n) :
    finrank ℝ (Submodule.span ℝ (Set.range (fun p : Fin R × Bool =>
      normalizedTransversePhysicalCharacter (n := n) hNc i j p.1 p.2))) = 2 * R := by
  rw [finrank_span_eq_card
    (normalizedTransversePhysicalCharacters_orthonormal hNc i j hR).linearIndependent]
  simp [mul_comm]

noncomputable def physicalDirectionalWeightAverage (w : PhysicalGradientIndex d n → ℝ)
    (i j : Fin d) : ℝ := ((n : ℝ)^d)⁻¹ * ∑ x : FinBox d n, w (i,(x,j))

theorem physical_quadratic_smul (T : PhysicalGaugeOneCochain d n Nc →L[ℝ]
    PhysicalGaugeOneCochain d n Nc) (a : ℝ) (v : PhysicalGaugeOneCochain d n Nc) :
    inner ℝ (a • v) (T (a • v)) = a^2 * inner ℝ v (T v) := by
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

theorem transversePhysicalCharacter_multiplier (i l : Fin d) (r : Fin R) :
    ‖transversePhysicalCharacter (n := n) i r (Pi.single l (1 : ZMod n)) - 1‖ ^ 2 =
      if l = i then ‖ZMod.stdAddChar ((r.val + 1 : ℕ) : ZMod n) - 1‖ ^ 2 else 0 := by
  rw [transversePhysicalCharacter_step]
  split_ifs <;> simp

theorem normalizedTransversePhysicalCharacter_weighted_energy (hNc : 2 ≤ Nc)
    (i j : Fin d) (r : Fin R) (b : Bool) (w : PhysicalGradientIndex d n → ℝ) :
    inner ℝ (normalizedTransversePhysicalCharacter hNc i j r b)
      (componentwiseWeightedRepairCLM w (normalizedTransversePhysicalCharacter hNc i j r b)) =
      ‖ZMod.stdAddChar ((r.val + 1 : ℕ) : ZMod n) - 1‖ ^ 2 * physicalDirectionalWeightAverage w i j := by
  classical
  rw [normalizedTransversePhysicalCharacter, physical_quadratic_smul,
    physicalCharacter_weightedRepair_energy]
  simp_rw [physicalCharacterQuadrature_norm, one_mul, transversePhysicalCharacter_multiplier]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [physicalCharacterNormalization_sq, physicalDirectionalWeightAverage]
  ring

theorem normalizedTransversePhysicalCharacter_hodge_energy (hNc : 2 ≤ Nc)
    (rho : SUNAdjointModel Nc) (i j : Fin d) (r : Fin R) (b : Bool) :
    inner ℝ (normalizedTransversePhysicalCharacter hNc i j r b)
      (flatGaugeHodgeK0CLM d n Nc rho (normalizedTransversePhysicalCharacter hNc i j r b)) =
      ‖ZMod.stdAddChar ((r.val + 1 : ℕ) : ZMod n) - 1‖ ^ 2 := by
  classical
  rw [normalizedTransversePhysicalCharacter, physical_quadratic_smul, physicalCharacter_hodge_energy]
  simp_rw [physicalCharacterQuadrature_norm, one_mul, transversePhysicalCharacter_multiplier]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc
    _ = (physicalCharacterNormalization d n ^ 2 * (n : ℝ)^d) *
        ‖ZMod.stdAddChar ((r.val + 1 : ℕ) : ZMod n) - 1‖ ^ 2 := by ring
    _ = _ := by rw [physicalCharacterNormalization_mass, one_mul]

theorem normalizedTransversePhysicalCharacters_energy_sum (hNc : 2 ≤ Nc)
    (rho : SUNAdjointModel Nc) (i j : Fin d) (w : PhysicalGradientIndex d n → ℝ) :
    (∑ p : Fin R × Bool, (inner ℝ (normalizedTransversePhysicalCharacter hNc i j p.1 p.2)
        (flatGaugeHodgeK0CLM d n Nc rho (normalizedTransversePhysicalCharacter hNc i j p.1 p.2)) +
      inner ℝ (normalizedTransversePhysicalCharacter hNc i j p.1 p.2)
        (componentwiseWeightedRepairCLM w (normalizedTransversePhysicalCharacter hNc i j p.1 p.2)))) =
      2 * (1 + physicalDirectionalWeightAverage w i j) *
        ∑ r : Fin R, ‖ZMod.stdAddChar ((r.val + 1 : ℕ) : ZMod n) - 1‖ ^ 2 := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [normalizedTransversePhysicalCharacter_hodge_energy,
    normalizedTransversePhysicalCharacter_weighted_energy]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring
end Strip
end YangMills.RG
