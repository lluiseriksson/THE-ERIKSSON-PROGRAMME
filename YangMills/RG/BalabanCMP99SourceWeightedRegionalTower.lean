/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceWeightedRegionalAdjoint

/-!
# The source-weighted multiscale regional average

CMP99 (3.18)--(3.19), printed p. 393, composes the one-step regional
averages in the order `Q_{j-1} ... Q_0`.  Its lattice scalar product carries
the spacing weight.  This file composes the literal one-step average with
coefficient `M^{-d}` and the corresponding weighted adjoint (unit synthesis).

The reverse synthesis is stored explicitly; it is not the adjoint in the
unweighted counting Hilbert structure.  At every depth the exact identities

`Q'_j (Q'_j)^dagger = I`

and equality of the source spacing norms are preserved.  Hence every
one-scale factor `c_k` and their finite product `C_j` are exactly one.
-/

namespace YangMills.RG

noncomputable section

/-- A bundled real Hilbert space used for the terminal carrier of a varying
regional tower. -/
structure CMP99SourceWeightedTowerHilbertSpace where
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [innerProductSpace : InnerProductSpace ℝ carrier]
  [completeSpace : CompleteSpace carrier]

attribute [instance]
  CMP99SourceWeightedTowerHilbertSpace.normedAddCommGroup
  CMP99SourceWeightedTowerHilbertSpace.innerProductSpace
  CMP99SourceWeightedTowerHilbertSpace.completeSpace

/-- A source-normalized regional tower.  `weightedAdjoint` is the adjoint for
the spacing-weighted pairings, not Lean's counting-space `adjoint`. -/
structure CMP99SourceWeightedRegionalTower
    {d N : ℕ} {g : Type} [NeZero N]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N) (spacing : ℝ) where
  depth : ℕ
  TerminalSpace : CMP99SourceWeightedTowerHilbertSpace
  terminalSpacing : ℝ
  Qprime : ActiveGaugeZeroCochain Omega g →L[ℝ] TerminalSpace.carrier
  weightedAdjoint : TerminalSpace.carrier →L[ℝ]
    ActiveGaugeZeroCochain Omega g
  Qprime_comp_weightedAdjoint :
    Qprime.comp weightedAdjoint =
      ContinuousLinearMap.id ℝ TerminalSpace.carrier
  weightedAdjoint_spacingNorm : ∀ eta,
    cmp99SourceSpacingNorm d spacing (weightedAdjoint eta) =
      cmp99SourceSpacingNorm d terminalSpacing eta

/-- The empty composition. -/
noncomputable def CMP99SourceWeightedRegionalTower.stop
    {d N : ℕ} {g : Type} [NeZero N]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N) (spacing : ℝ) :
    CMP99SourceWeightedRegionalTower (g := g) Omega spacing where
  depth := 0
  TerminalSpace :=
    { carrier := ActiveGaugeZeroCochain Omega g }
  terminalSpacing := spacing
  Qprime := ContinuousLinearMap.id ℝ _
  weightedAdjoint := ContinuousLinearMap.id ℝ _
  Qprime_comp_weightedAdjoint := by ext eta; rfl
  weightedAdjoint_spacingNorm := by intro eta; rfl

/-- Prepend one literal source average.  The total average is
`Q_tail.comp Q_head`, while the weighted adjoint is the reverse composition
`S_head.comp S_tail`. -/
noncomputable def CMP99SourceWeightedRegionalTower.step
    {d M N' : ℕ} {g : Type} [NeZero M] [NeZero N']
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (spacing : ℝ)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (tail : CMP99SourceWeightedRegionalTower (g := g)
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      ((M : ℝ) * spacing)) :
    CMP99SourceWeightedRegionalTower (g := g) Omega spacing where
  depth := tail.depth + 1
  TerminalSpace := tail.TerminalSpace
  terminalSpacing := tail.terminalSpacing
  Qprime := tail.Qprime.comp
    (cmp99SourceTransportedBlockAverageCLM Omega transport)
  weightedAdjoint :=
    (cmp99SourceTransportedBlockWeightedAdjointCLM
      Omega hOmega transport).comp tail.weightedAdjoint
  Qprime_comp_weightedAdjoint := by
    apply ContinuousLinearMap.ext
    intro eta
    change tail.Qprime
      (cmp99SourceTransportedBlockAverageCLM Omega transport
        (cmp99SourceTransportedBlockWeightedAdjointCLM
          Omega hOmega transport (tail.weightedAdjoint eta))) = eta
    have hhead := congrArg
      (fun A : ActiveGaugeZeroCochain
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g →L[ℝ]
          ActiveGaugeZeroCochain
            (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g =>
        A (tail.weightedAdjoint eta))
      (cmp99SourceTransportedBlockAverage_comp_weightedAdjoint
        Omega hOmega transport)
    change cmp99SourceTransportedBlockAverageCLM Omega transport
        (cmp99SourceTransportedBlockWeightedAdjointCLM
          Omega hOmega transport (tail.weightedAdjoint eta)) =
      tail.weightedAdjoint eta at hhead
    rw [hhead]
    have htail := congrArg
      (fun A : tail.TerminalSpace.carrier →L[ℝ]
          tail.TerminalSpace.carrier => A eta)
      tail.Qprime_comp_weightedAdjoint
    exact htail
  weightedAdjoint_spacingNorm := by
    intro eta
    change cmp99SourceSpacingNorm d spacing
        (cmp99SourceTransportedBlockWeightedAdjointCLM
          Omega hOmega transport (tail.weightedAdjoint eta)) =
      cmp99SourceSpacingNorm d tail.terminalSpacing eta
    rw [cmp99SourceTransportedBlockWeightedAdjoint_spacingNorm]
    exact tail.weightedAdjoint_spacingNorm eta

@[simp] theorem CMP99SourceWeightedRegionalTower.depth_stop
    {d N : ℕ} {g : Type} [NeZero N]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N) (spacing : ℝ) :
    (CMP99SourceWeightedRegionalTower.stop (g := g) Omega spacing :
      CMP99SourceWeightedRegionalTower (g := g) Omega spacing).depth = 0 := rfl

theorem CMP99SourceWeightedRegionalTower.depth_step
    {d M N' : ℕ} {g : Type} [NeZero M] [NeZero N']
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (spacing : ℝ)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (tail : CMP99SourceWeightedRegionalTower (g := g)
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      ((M : ℝ) * spacing)) :
    (CMP99SourceWeightedRegionalTower.step (g := g)
      Omega hOmega spacing transport tail).depth = tail.depth + 1 := rfl

/-- Literal printed order: adding the fine scale on the right gives
`Q_tail ... Q_head`. -/
theorem CMP99SourceWeightedRegionalTower.Qprime_step
    {d M N' : ℕ} {g : Type} [NeZero M] [NeZero N']
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (spacing : ℝ)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (tail : CMP99SourceWeightedRegionalTower (g := g)
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      ((M : ℝ) * spacing)) :
    (CMP99SourceWeightedRegionalTower.step (g := g)
      Omega hOmega spacing transport tail).Qprime =
      tail.Qprime.comp
        (cmp99SourceTransportedBlockAverageCLM Omega transport) := rfl

/-- Reverse order for the source Hilbert adjoint. -/
theorem CMP99SourceWeightedRegionalTower.weightedAdjoint_step
    {d M N' : ℕ} {g : Type} [NeZero M] [NeZero N']
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (spacing : ℝ)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (tail : CMP99SourceWeightedRegionalTower (g := g)
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      ((M : ℝ) * spacing)) :
    (CMP99SourceWeightedRegionalTower.step (g := g)
      Omega hOmega spacing transport tail).weightedAdjoint =
      (cmp99SourceTransportedBlockWeightedAdjointCLM
        Omega hOmega transport).comp tail.weightedAdjoint := rfl

/-- Every scale normalization is exactly one in the printed weighted Hilbert
convention. -/
def cmp99SourceScaleNormalization (_k : ℕ) : ℝ := 1

/-- The exact finite product `C_j` from the source-normalized scales. -/
def cmp99SourceTowerNormalization (j : ℕ) : ℝ :=
  ∏ k : Fin j, cmp99SourceScaleNormalization k

@[simp] theorem cmp99SourceTowerNormalization_eq_one (j : ℕ) :
    cmp99SourceTowerNormalization j = 1 := by
  simp [cmp99SourceTowerNormalization, cmp99SourceScaleNormalization]

theorem cmp99SourceTowerNormalization_pos (j : ℕ) :
    0 < cmp99SourceTowerNormalization j := by simp

/-- Source-specific terminal normalization in the requested product form. -/
theorem CMP99SourceWeightedRegionalTower.Qprime_comp_weightedAdjoint_eq_Cj
    {d N : ℕ} {g : Type} [NeZero N]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [FiniteDimensional ℝ g]
    {Omega : ActiveGaugeRegion d N} {spacing : ℝ}
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing) :
    T.Qprime.comp T.weightedAdjoint =
      cmp99SourceTowerNormalization T.depth •
        ContinuousLinearMap.id ℝ T.TerminalSpace.carrier := by
  rw [cmp99SourceTowerNormalization_eq_one, one_smul]
  exact T.Qprime_comp_weightedAdjoint

/-- Exact terminal source-norm equality, equivalently the requested
`sqrt C_j` law since `C_j = 1`. -/
theorem CMP99SourceWeightedRegionalTower.weightedAdjoint_norm_eq_sqrt_Cj
    {d N : ℕ} {g : Type} [NeZero N]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [FiniteDimensional ℝ g]
    {Omega : ActiveGaugeRegion d N} {spacing : ℝ}
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (eta : T.TerminalSpace.carrier) :
    cmp99SourceSpacingNorm d spacing (T.weightedAdjoint eta) =
      Real.sqrt (cmp99SourceTowerNormalization T.depth) *
        cmp99SourceSpacingNorm d T.terminalSpacing eta := by
  rw [cmp99SourceTowerNormalization_eq_one, Real.sqrt_one, one_mul]
  exact T.weightedAdjoint_spacingNorm eta

end

end YangMills.RG
