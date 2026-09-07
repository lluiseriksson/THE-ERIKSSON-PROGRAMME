import YangMills.RG.BalabanCMP99SourceAliasReflectionInvolutive
import YangMills.RG.BalabanCMP99SourceAliasReflectionStabilizedSolution

/-!
# PRE-VALIDATION: one-coordinate reflection of the actual alias carrier

Source present; .olean not materialized; result not compiler-verified.
This is R1 only. It constructs a permutation of the printed half-open
carrier, not literal integer negation. N is the alias count; the physical
consumer must instantiate N=L^j. No precision or Green covariance is assumed.
The current common-translation diagnostic does NOT include this file.
-/

namespace YangMills.RG
noncomputable section

def neumannAliasPiCoordinateReflection (d N : ℕ) [NeZero N] (mu : Fin d) :
    Equiv.Perm ((nu : Fin d) →
      {x : ℤ // x ∈ cmp89Eq245CenteredAliasIntegers N}) :=
  Equiv.piCongrRight fun nu =>
    if nu = mu then cmp99SourceCenteredAliasReflection N else Equiv.refl _

theorem neumannAliasPiCoordinateReflection_self
    (d N : ℕ) [NeZero N] (mu : Fin d)
    (m : (nu : Fin d) → {x : ℤ // x ∈ cmp89Eq245CenteredAliasIntegers N}) :
    neumannAliasPiCoordinateReflection d N mu m mu =
      cmp99SourceCenteredAliasReflection N (m mu) := by
  simp [neumannAliasPiCoordinateReflection]

theorem neumannAliasPiCoordinateReflection_other
    (d N : ℕ) [NeZero N] (mu nu : Fin d) (hnu : nu ≠ mu)
    (m : (rho : Fin d) → {x : ℤ // x ∈ cmp89Eq245CenteredAliasIntegers N}) :
    neumannAliasPiCoordinateReflection d N mu m nu = m nu := by
  simp [neumannAliasPiCoordinateReflection, hnu]

def neumannAliasCoordinateReflection (d N : ℕ) [NeZero N] (mu : Fin d) :
    Equiv.Perm {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N} :=
  (cmp89Eq245CenteredAliasVectorPiEquiv d N).trans
    ((neumannAliasPiCoordinateReflection d N mu).trans
      (cmp89Eq245CenteredAliasVectorPiEquiv d N).symm)

theorem neumannAliasCoordinateReflection_other
    (d N : ℕ) [NeZero N] (mu nu : Fin d) (hnu : nu ≠ mu)
    (m : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N}) :
    (neumannAliasCoordinateReflection d N mu m).1 nu = m.1 nu := by
  simp [neumannAliasCoordinateReflection, cmp89Eq245CenteredAliasVectorPiEquiv,
    neumannAliasPiCoordinateReflection, hnu]

theorem neumannAliasCoordinateReflection_residue
    (d N : ℕ) [NeZero N] (mu : Fin d)
    (m : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N}) :
    (((neumannAliasCoordinateReflection d N mu m).1 mu : ℤ) : ZMod N) =
      -(m.1 mu : ZMod N) := by
  simpa [neumannAliasCoordinateReflection, cmp89Eq245CenteredAliasVectorPiEquiv,
    neumannAliasPiCoordinateReflection] using
    cmp99SourceCenteredAliasReflection_cast_eq_neg N
      ((cmp89Eq245CenteredAliasVectorPiEquiv d N m) mu)

theorem neumannAliasCoordinateReflection_involutive
    (d N : ℕ) [NeZero N] (mu : Fin d)
    (m : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N}) :
    neumannAliasCoordinateReflection d N mu
      (neumannAliasCoordinateReflection d N mu m) = m := by
  apply (cmp89Eq245CenteredAliasVectorPiEquiv d N).injective
  funext nu
  change neumannAliasPiCoordinateReflection d N mu
      (neumannAliasPiCoordinateReflection d N mu
        (cmp89Eq245CenteredAliasVectorPiEquiv d N m)) nu =
    (cmp89Eq245CenteredAliasVectorPiEquiv d N m) nu
  by_cases hnu : nu = mu
  · subst nu
    rw [neumannAliasPiCoordinateReflection_self,
      neumannAliasPiCoordinateReflection_self]
    exact cmp99SourceCenteredAliasReflection_apply_apply N _
  · rw [neumannAliasPiCoordinateReflection_other d N mu nu hnu,
      neumannAliasPiCoordinateReflection_other d N mu nu hnu]

theorem neumannAliasCoordinateReflection_sum
    {A : Type*} [AddCommMonoid A] (d N : ℕ) [NeZero N] (mu : Fin d)
    (f : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N} → A) :
    ∑ m, f (neumannAliasCoordinateReflection d N mu m) = ∑ m, f m := by
  exact Equiv.sum_comp (neumannAliasCoordinateReflection d N mu) f

/-- The physical specialization fixes the alias count to L^j, including j=0. -/
def neumannPhysicalAliasCoordinateReflection
    (d L j : ℕ) [NeZero L] (mu : Fin d) :
    Equiv.Perm (CMP89Eq246AliasIndex d L j) := by
  letI : NeZero (L ^ j) := ⟨pow_ne_zero j (NeZero.ne L)⟩
  exact neumannAliasCoordinateReflection d (L ^ j) mu

theorem neumannPhysicalAliasCoordinateReflection_central
    (d L j : ℕ) [NeZero L] (mu : Fin d) :
    neumannPhysicalAliasCoordinateReflection d L j mu
        (cmp89Eq249CentralAliasIndex d L j) =
      cmp89Eq249CentralAliasIndex d L j := by
  letI : NeZero (L ^ j) := ⟨pow_ne_zero j (NeZero.ne L)⟩
  change neumannAliasCoordinateReflection d (L ^ j) mu
      (cmp89Eq249CentralAliasIndex d L j) =
    cmp89Eq249CentralAliasIndex d L j
  apply (cmp89Eq245CenteredAliasVectorPiEquiv d (L ^ j)).injective
  funext nu
  change neumannAliasPiCoordinateReflection d (L ^ j) mu
      (cmp89Eq245CenteredAliasVectorPiEquiv d (L ^ j)
        (cmp89Eq249CentralAliasIndex d L j)) nu =
    (cmp89Eq245CenteredAliasVectorPiEquiv d (L ^ j)
      (cmp89Eq249CentralAliasIndex d L j)) nu
  by_cases hnu : nu = mu
  · subst nu
    rw [neumannAliasPiCoordinateReflection_self]
    change cmp99SourceCenteredAliasReflection (L ^ j)
        ⟨0, _⟩ = ⟨0, _⟩
    exact cmp99SourceCenteredAliasReflection_zero
  · exact neumannAliasPiCoordinateReflection_other d (L ^ j) mu nu hnu _

#print axioms neumannAliasPiCoordinateReflection_self
#print axioms neumannAliasPiCoordinateReflection_other
#print axioms neumannAliasCoordinateReflection_other
#print axioms neumannAliasCoordinateReflection_residue
#print axioms neumannAliasCoordinateReflection_involutive
#print axioms neumannAliasCoordinateReflection_sum
#print axioms neumannPhysicalAliasCoordinateReflection_central

end
end YangMills.RG
