import YangMills.RG.BalabanCMP99SourceEq395PhysicalDistanceDecay

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe u v w

noncomputable def testKernelReindex
    {ι : Type u} {κ : Type v} {ι' : Type*} {κ' : Type*} {g : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    [Fintype ι'] [DecidableEq ι'] [Fintype κ']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (sourceEquiv : ι ≃ ι') (targetEquiv : κ ≃ κ')
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g) :
    FinitePiLpField ι' g →L[ℝ] FinitePiLpField κ' g :=
  let sourceMap :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g sourceEquiv).toContinuousLinearEquiv
  let targetMap :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g targetEquiv).toContinuousLinearEquiv
  targetMap.toContinuousLinearMap.comp
    (T.comp sourceMap.symm.toContinuousLinearMap)

theorem testKernelReindex_exponential
    {ι : Type u} {κ : Type v} {ι' : Type*} {κ' : Type*} {g : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (sourceEquiv : ι ≃ ι') (targetEquiv : κ ≃ κ')
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (dist : κ → ι → ℕ) {A rate : ℝ}
    (hT : FinitePiLpTypedExponentialKernelBound T dist A rate) :
    FinitePiLpTypedExponentialKernelBound
      (testKernelReindex sourceEquiv targetEquiv T)
      (fun target source =>
        dist (targetEquiv.symm target) (sourceEquiv.symm source)) A rate := by
  refine ⟨hT.1, hT.2.1, ?_⟩
  intro source target v
  let sourceMap :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g sourceEquiv).toContinuousLinearEquiv
  let targetMap :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g targetEquiv).toContinuousLinearEquiv
  have hsingle : sourceMap.symm (singleFinitePiLp source v) =
      singleFinitePiLp (sourceEquiv.symm source) v := by
    rw [singleFinitePiLp_eq_toLp_single,
      singleFinitePiLp_eq_toLp_single]
    simpa only [sourceMap,
      LinearIsometryEquiv.piLpCongrLeft_symm] using
      (LinearIsometryEquiv.piLpCongrLeft_single
        (p := (2 : ENNReal)) (𝕜 := ℝ) sourceEquiv.symm source v)
  have heval (f : FinitePiLpField κ g) :
      targetMap f target = f (targetEquiv.symm target) := by
    rfl
  change ‖targetMap (T (sourceMap.symm (singleFinitePiLp source v))) target‖ ≤ _
  rw [hsingle, heval]
  exact hT.2.2 (sourceEquiv.symm source) (targetEquiv.symm target) v

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

noncomputable def testTerminalEquiv
    (Omega : ActiveGaugeRegion 4 (2 * Q)) (depth : ℕ) :
    (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (depth + 1)
      |>.terminalSite) ≃ ActiveGaugeRegion.Site Omega :=
  Equiv.cast (cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (M := M) Omega (depth + 1))

set_option maxHeartbeats 4000000 in
noncomputable def testOnOmegaReindex
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  testKernelReindex (testTerminalEquiv (M := M) Omega depth)
    (testTerminalEquiv (M := M) Omega depth)
    (cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing background
      budget fineSmall hsmall)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem testOnOmegaReindex_bound
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpTypedExponentialKernelBound
      (testOnOmegaReindex Omega hM depth hspacing background budget fineSmall
        hsmall)
      (fun target source : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1)
      (cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 4) := by
  have hG := cmp99Eq395GeneratedPhysicalMiddle_physicalDist_exponentialKernelBound
    Omega hM depth hspacing background budget fineSmall hsmall
  have htransport := testKernelReindex_exponential
    (testTerminalEquiv (M := M) Omega depth)
    (testTerminalEquiv (M := M) Omega depth)
    (cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing background
      budget fineSmall hsmall)
    (cmp99SourceIteratedLiftPhysicalTerminalDist
      (M := M) Omega (depth + 1)) hG
  let hsite := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (M := M) Omega (depth + 1)
  have hcast (x : ActiveGaugeRegion.Site Omega) :
      hsite ▸ ((testTerminalEquiv (M := M) Omega depth).symm x) = x := by
    exact cast_cancel_of_opposite_equalities hsite hsite.symm x
  have hdist :
      (fun target source : ActiveGaugeRegion.Site Omega =>
        cmp99SourceIteratedLiftPhysicalTerminalDist
          (M := M) Omega (depth + 1)
          ((testTerminalEquiv (M := M) Omega depth).symm target)
          ((testTerminalEquiv (M := M) Omega depth).symm source)) =
      (fun target source : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1) := by
    funext target source
    unfold cmp99SourceIteratedLiftPhysicalTerminalDist
    dsimp only
    rw [hcast target, hcast source]
  change FinitePiLpTypedExponentialKernelBound
    (testKernelReindex (testTerminalEquiv (M := M) Omega depth)
      (testTerminalEquiv (M := M) Omega depth)
      (cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing background
        budget fineSmall hsmall))
    (fun target source : ActiveGaugeRegion.Site Omega =>
      finBoxDist target.1 source.1)
    (cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
    (cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 4)
  rw [← hdist]
  exact htransport

end
end YangMills.RG
