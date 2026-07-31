import YangMills.SU2ThetaPrism.Cell

/-!
# The concrete theta witness
-/

noncomputable section

open Complex

namespace YangMills.SU2ThetaPrism

/-- `F(U,V) = chi(U)chi(V) - (1/2)chi(UV⁻¹)`. -/
def witness (U V : SU2) : ℂ :=
  chi U * chi V - (1 / 2 : ℂ) * chi (U * V⁻¹)

theorem witness_simultaneous_conj (h U V : SU2) :
    witness (h * U * h⁻¹) (h * V * h⁻¹) = witness U V := by
  simp only [witness, chi_conj]
  have hprod :
      (h * U * h⁻¹) * (h * V * h⁻¹)⁻¹ = h * (U * V⁻¹) * h⁻¹ := by
    simp [mul_assoc]
  rw [hprod, chi_conj]

/-- Concrete anti-vacuity witness: at `(1,1)`, `F=3`. -/
theorem witness_one_one : witness (1 : SU2) (1 : SU2) = 3 := by
  norm_num [witness, chi_one]

theorem witness_ne_zero : witness ≠ (0 : SU2 → SU2 → ℂ) := by
  intro h
  have hv := congr_fun (congr_fun h (1 : SU2)) (1 : SU2)
  rw [witness_one_one] at hv
  norm_num at hv

/-- The scalar matrix `-I₂` as an explicit SU(2) element. -/
def negIdentitySU2 : SU2 := by
  refine ⟨(-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ), ?_⟩
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    simp
  · rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    norm_num

@[simp] theorem chi_negIdentity : chi negIdentitySU2 = -2 := by
  simp [negIdentitySU2, chi, Matrix.trace_one]

/-- Left multiplication by the central element `-I₂` negates the fundamental
character. -/
@[simp] theorem chi_negIdentity_mul (g : SU2) :
    chi (negIdentitySU2 * g) = -chi g := by
  change Matrix.trace (((-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * g.val) =
    -Matrix.trace g.val
  simp [Matrix.trace, Matrix.mul_apply]

/-- Concrete anti-singleton witness `I₂ ≠ -I₂`. -/
theorem one_ne_negIdentity : (1 : SU2) ≠ negIdentitySU2 := by
  intro h
  have hc := congrArg chi h
  norm_num at hc

theorem su2_nontrivial : Nontrivial SU2 :=
  ⟨⟨1, negIdentitySU2, one_ne_negIdentity⟩⟩

theorem su2_not_subsingleton : ¬ Subsingleton SU2 :=
  not_subsingleton_iff_nontrivial.mpr su2_nontrivial

end YangMills.SU2ThetaPrism
