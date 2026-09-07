import YangMills.RG.BalabanCMP99SourceCenteredAliasReflection
import YangMills.RG.BalabanCMP99FlatMultidimensionalDFT

/-!
PRE-VALIDATION: source present; .olean not materialized and compiler result
not verified. Reuse the sealed literal scalar residue equivalence.
This finite character sum selects congruence only. The remaining continuous
integral, physical phase dictionary and point-source equation are NOT proved.
-/

namespace YangMills.RG
noncomputable section

def neumannCenteredAliasVectorResidueEquiv (d N : ℕ) [NeZero N] :
    {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N} ≃
      CMP99FlatZModBox d N :=
  (cmp89Eq245CenteredAliasVectorPiEquiv d N).trans
    (Equiv.piCongrRight fun _ => cmp99SourceCenteredAliasResidueEquiv N)

theorem neumannCenteredAliasVectorResidueEquiv_apply
    (d N : ℕ) [NeZero N]
    (m : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N}) :
    neumannCenteredAliasVectorResidueEquiv d N m =
      (fun i => (m.1 i : ZMod N)) := by
  funext i
  change cmp99SourceCenteredAliasResidueEquiv N
    ((cmp89Eq245CenteredAliasVectorPiEquiv d N m) i) = (m.1 i : ZMod N)
  rw [cmp99SourceCenteredAliasResidueEquiv_apply]
  rfl

theorem neumannCenteredAlias_character_sum
    (d N : ℕ) [NeZero N] (u : CMP99FlatZModBox d N) :
    (∑ m : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N},
      cmp99FlatZModFourierCharacter (fun i => (m.1 i : ZMod N)) u) =
      if u = 0 then (N : ℂ)^d else 0 := by
  calc
    _ = ∑ k : CMP99FlatZModBox d N, cmp99FlatZModFourierCharacter k u := by
      simpa only [neumannCenteredAliasVectorResidueEquiv_apply] using
        (neumannCenteredAliasVectorResidueEquiv d N).sum_comp
          (fun k => cmp99FlatZModFourierCharacter k u)
    _ = _ := sum_cmp99FlatZModFourierCharacter u

theorem neumannIntegerCharacter_product_phase
    (N : ℕ) [NeZero N] (m u : ℤ) :
    ZMod.stdAddChar ((m : ZMod N) * (u : ZMod N)) =
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ) / (N : ℂ)) := by
  rw [← Int.cast_mul, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

end
end YangMills.RG

#print axioms YangMills.RG.neumannCenteredAliasVectorResidueEquiv_apply
#print axioms YangMills.RG.neumannCenteredAlias_character_sum
#print axioms YangMills.RG.neumannIntegerCharacter_product_phase
