import YangMills.RG.NeumannCoordinateMomentumCarry
import YangMills.RG.NeumannEntireAverageHalfCellPhase
import YangMills.RG.NeumannCoordinateProduct

/-!
# actual one-coordinate averaging phases

Cold compiler/audit verified at source 84ceb5f2 (2026-09-07).
Evidence and scope: VERIFICATION-LEDGER Addendum 1197; no terminal claim.
R2b uses the finite average itself, with the one-coordinate residue carry.
The phases are entire exponentials, not complex conjugations. No positivity
or nonvanishing of the averaging factors is assumed. N=1 and j=0 are kept.
-/

namespace YangMills.RG
noncomputable section

def neumannCoordinateHalfCellPhase (d N : ℕ) (mu : Fin d)
    (z : Fin d → ℂ) : ℂ :=
  Complex.exp (Complex.I * ((N : ℂ)⁻¹ * z mu) * ((N - 1 : ℕ) : ℂ))

theorem neumannCoordinateHalfCellPhase_ne_zero
    (d N : ℕ) (mu : Fin d) (z : Fin d → ℂ) :
    neumannCoordinateHalfCellPhase d N mu z ≠ 0 :=
  Complex.exp_ne_zero _

theorem neumannCoordinateHalfCellPhase_neg
    (d N : ℕ) (mu : Fin d) (z : Fin d → ℂ) :
    neumannCoordinateHalfCellPhase d N mu (-z) =
      (neumannCoordinateHalfCellPhase d N mu z)⁻¹ := by
  unfold neumannCoordinateHalfCellPhase
  simp only [Pi.neg_apply]
  rw [show Complex.I * ((N : ℂ)⁻¹ * -z mu) * ((N - 1 : ℕ) : ℂ) =
      -(Complex.I * ((N : ℂ)⁻¹ * z mu) * ((N - 1 : ℕ) : ℂ)) by ring]
  exact Complex.exp_neg _

theorem neumannEntireAverageAmplitude_coordinateReflection
    (d N : ℕ) (mu : Fin d) (z : Fin d → ℂ) :
    cmp89Eq245EntireAverageAmplitude d N
      (neumannMomentumCoordinateReflection d mu z) =
    neumannCoordinateHalfCellPhase d N mu z *
      cmp89Eq245EntireAverageAmplitude d N z := by
  let f := fun nu : Fin d => cmp89Eq245EntireAverageFactor N (z nu)
  let g := fun nu : Fin d => cmp89Eq245EntireAverageFactor N
    (neumannMomentumCoordinateReflection d mu z nu)
  have he : ∀ nu, nu ≠ mu → g nu = f nu := by
    intro nu hne
    simp [f, g, neumannMomentumCoordinateReflection, hne]
  have hm : g mu = neumannCoordinateHalfCellPhase d N mu z * f mu := by
    simpa [f, g, neumannMomentumCoordinateReflection,
      neumannCoordinateHalfCellPhase] using
      neumannEntireAverageFactor_halfCellPhase N (z mu)
  change (∏ nu, g nu) = neumannCoordinateHalfCellPhase d N mu z * ∏ nu, f nu
  exact NeumannCoordinateProductRepro.one_factor mu f g _ he hm

theorem neumannEntireAliasAverageColumn_coordinateReflection
    (d L j : ℕ) [NeZero L] (mu : Fin d) (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246EntireAliasAverageColumn d L j
      (neumannMomentumCoordinateReflection d mu z)
      (neumannPhysicalAliasCoordinateReflection d L j mu m) =
    neumannCoordinateHalfCellPhase d (L ^ j) mu
        (cmp89Eq248EntireAliasMomentum z m.1) *
      cmp89Eq246EntireAliasAverageColumn d L j z m := by
  obtain ⟨w, _, hw⟩ :=
    neumannPhysicalAliasCoordinateReflection_momentum d L j mu z m
  unfold cmp89Eq246EntireAliasAverageColumn
  rw [hw, cmp89Eq245EntireAverageAmplitude_add_int_aliasPeriods
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)]
  exact neumannEntireAverageAmplitude_coordinateReflection _ _ _ _

theorem neumannEntireAliasAverageRow_coordinateReflection
    (d L j : ℕ) [NeZero L] (mu : Fin d) (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246EntireAliasAverageRow d L j
      (neumannMomentumCoordinateReflection d mu z)
      (neumannPhysicalAliasCoordinateReflection d L j mu m) =
    (neumannCoordinateHalfCellPhase d (L ^ j) mu
        (cmp89Eq248EntireAliasMomentum z m.1))⁻¹ *
      cmp89Eq246EntireAliasAverageRow d L j z m := by
  obtain ⟨w, _, hw⟩ :=
    neumannPhysicalAliasCoordinateReflection_momentum d L j mu z m
  have hneg :
      -cmp89Eq248EntireAliasMomentum (neumannMomentumCoordinateReflection d mu z)
          (neumannPhysicalAliasCoordinateReflection d L j mu m).1 =
      fun nu =>
        neumannMomentumCoordinateReflection d mu
            (-cmp89Eq248EntireAliasMomentum z m.1) nu +
        ((-w nu : ℤ) : ℂ) * (((2 * Real.pi * ((L ^ j : ℕ) : ℝ) : ℝ) : ℂ)) := by
    funext nu
    simp only [Pi.neg_apply]
    rw [congrFun hw nu]
    by_cases hnu : nu = mu <;>
      simp [neumannMomentumCoordinateReflection, hnu] <;> ring
  unfold cmp89Eq246EntireAliasAverageRow
  rw [hneg, cmp89Eq245EntireAverageAmplitude_add_int_aliasPeriods
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)]
  rw [neumannEntireAverageAmplitude_coordinateReflection,
    neumannCoordinateHalfCellPhase_neg]

/-- Literal entrywise conjugacy, derived from the three physical coefficient laws. -/
theorem neumannEntireAliasPrecisionMatrix_coordinateReflection
    (d L j : ℕ) [NeZero L] (mu : Fin d) (mass a : ℝ) (z : Fin d → ℂ)
    (m n : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246EntireAliasPrecisionMatrix d L j mass a
      (neumannMomentumCoordinateReflection d mu z)
      (neumannPhysicalAliasCoordinateReflection d L j mu m)
      (neumannPhysicalAliasCoordinateReflection d L j mu n) =
    neumannCoordinateHalfCellPhase d (L ^ j) mu
        (cmp89Eq248EntireAliasMomentum z m.1) *
      cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z m n *
      (neumannCoordinateHalfCellPhase d (L ^ j) mu
        (cmp89Eq248EntireAliasMomentum z n.1))⁻¹ := by
  classical
  unfold cmp89Eq246EntireAliasPrecisionMatrix
  rw [neumannEntireAliasFineSymbol_coordinateReflection,
    neumannEntireAliasAverageColumn_coordinateReflection,
    neumannEntireAliasAverageRow_coordinateReflection]
  by_cases h : m = n
  · subst n
    simp only [if_pos rfl]
    have hD := neumannCoordinateHalfCellPhase_ne_zero d (L ^ j) mu
      (cmp89Eq248EntireAliasMomentum z m.1)
    field_simp [hD] <;> ring
  · have hr :
        neumannPhysicalAliasCoordinateReflection d L j mu m ≠
        neumannPhysicalAliasCoordinateReflection d L j mu n :=
      (neumannPhysicalAliasCoordinateReflection d L j mu).injective.ne h
    simp only [if_neg h, if_neg hr]
    ring


end
end YangMills.RG
