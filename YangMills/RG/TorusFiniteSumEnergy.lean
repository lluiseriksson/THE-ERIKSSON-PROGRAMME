import YangMills.RG.TorusFourierBandDimension

/-!
Explicit counting-measure energies, not the ambient Pi norm.
This proves the finite-sum shift identities and the exact energy of an
individual torus character. It does not yet prove Parseval for a band or
identify this stencil with the repository's physical cochain operator.
-/

namespace YangMills.RG

open scoped BigOperators

section FiniteGroup

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def countingL2Mass (f : G → ℂ) : ℝ := ∑ x, ‖f x‖ ^ 2

noncomputable def forwardShiftEnergy (f : G → ℂ) (a : G) : ℝ :=
  ∑ x, ‖f (x + a) - f x‖ ^ 2

noncomputable def backwardShiftEnergy (f : G → ℂ) (a : G) : ℝ :=
  ∑ x, ‖f x - f (x - a)‖ ^ 2

theorem backwardShiftEnergy_eq_forward (f : G → ℂ) (a : G) :
    backwardShiftEnergy f a = forwardShiftEnergy f a := by
  classical
  have h := (Equiv.addRight (-a)).sum_comp (fun x => ‖f (x + a) - f x‖ ^ 2)
  simpa [backwardShiftEnergy, forwardShiftEnergy, sub_eq_add_neg, add_assoc] using h

theorem character_forward_difference (chi : AddChar G ℂ) (a x : G) :
    chi (x + a) - chi x = (chi a - 1) * chi x := by
  rw [AddChar.map_add_eq_mul]
  ring

theorem character_forwardShiftEnergy (chi : AddChar G ℂ) (a : G) :
    forwardShiftEnergy chi a = ‖chi a - 1‖ ^ 2 * countingL2Mass chi := by
  classical
  simp only [forwardShiftEnergy, character_forward_difference, norm_mul, mul_pow,
    countingL2Mass, Finset.mul_sum]

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The explicit scalar stencil obtained from one occupied bond direction:
transverse forward differences and the longitudinal backward difference.
The identification with PhysicalGaugeCochains is a separate obligation. -/
noncomputable def oneComponentStencilEnergy (f : G → ℂ) (a : I → G) (i : I) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, forwardShiftEnergy f (a j)) + backwardShiftEnergy f (a i)

theorem oneComponentStencilEnergy_eq (f : G → ℂ) (a : I → G) (i : I) :
    oneComponentStencilEnergy f a i = ∑ j, forwardShiftEnergy f (a j) := by
  classical
  rw [oneComponentStencilEnergy, backwardShiftEnergy_eq_forward]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

theorem character_oneComponentStencilEnergy (chi : AddChar G ℂ) (a : I → G) (i : I) :
    oneComponentStencilEnergy chi a i =
      (∑ j, ‖chi (a j) - 1‖ ^ 2) * countingL2Mass chi := by
  rw [oneComponentStencilEnergy_eq]
  simp_rw [character_forwardShiftEnergy]
  exact (Finset.sum_mul _ _ _).symm

end FiniteGroup

variable {d n : ℕ} [NeZero n]

/-- The unit-step finite-torus stencil has an exact character multiplier.
Its L2 mass is an actual finite sum, with no norm hypothesis. -/
theorem torusCharacter_oneComponentStencilEnergy (k : Fin d → ZMod n) (i : Fin d) :
    oneComponentStencilEnergy (torusFourierCharacter k)
      (fun j => Pi.single j (1 : ZMod n)) i =
      (∑ j : Fin d, ‖torusFourierCharacter k (Pi.single j (1 : ZMod n)) - 1‖ ^ 2) *
        countingL2Mass (torusFourierCharacter k) := by
  exact character_oneComponentStencilEnergy _ _ _

end YangMills.RG
