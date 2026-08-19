import YangMills.RG.BalabanCMP99SourceRetainedGeneratedTerminalBridge
/-!
elaboration target for Step 8b.24/P0.

It constructs the two canonical fine-to-coarse prefix truncations and the proposed family bridge from every retained physical prefix to those truncations.

SEALED SOURCE-SPECIFIC BRICK: compiler-verified in a fresh Colab checkout.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.L2Operator

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Retain the first `r` fine-to-coarse regional steps and stop at that
prefix.  The original fine region remains the head of the result. -/
def CMP99SourceActiveRegionChain.take
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (r : ℕ) (hr : r ≤ depth) :
    CMP99SourceActiveRegionChain d M N Omega r := by
  induction regions generalizing r with
  | stop Omega =>
      have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
      subst r
      exact .stop Omega
  | @step N' depth _ Omega hOmega tail ih =>
      cases r with
      | zero => exact .stop Omega
      | succ r =>
          exact .step Omega hOmega
            (ih r (Nat.le_of_succ_le_succ hr))

/-- Fin-indexed wrapper: an out-of-range truncation proof never reaches a
public prefix theorem. -/
def CMP99SourceActiveRegionChain.takeFin
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (r : Fin (depth + 1)) :
    CMP99SourceActiveRegionChain d M N Omega r.val :=
  regions.take r.val (Nat.lt_succ_iff.mp r.isLt)

@[simp]
theorem CMP99SourceActiveRegionChain.take_zero
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    regions.take 0 (Nat.zero_le depth) =
      CMP99SourceActiveRegionChain.stop Omega := by
  cases regions <;> rfl

@[simp]
theorem CMP99SourceActiveRegionChain.take_step_succ
    {N' depth r : ℕ} [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (tail : CMP99SourceActiveRegionChain d M N'
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) depth)
    (hr : r + 1 ≤ depth + 1) :
    (CMP99SourceActiveRegionChain.step Omega hOmega tail).take
        (r + 1) hr =
      CMP99SourceActiveRegionChain.step Omega hOmega
        (tail.take r (Nat.le_of_succ_le_succ hr)) := by
  rfl

/-- Retain the first `r` scalar small-field steps.  The initial radius and
all proof data on retained constructors are copied from the physical chain;
the unused tail is replaced by `stop`. -/
def CMP99SourceUbarRadiusChain.take
    {depth : ℕ} {epsilon : ℝ}
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (r : ℕ) (hr : r ≤ depth) :
    CMP99SourceUbarRadiusChain d M Nc r epsilon := by
  induction chain generalizing r with
  | stop epsilon epsilon_nonneg =>
      have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
      subst r
      exact .stop epsilon epsilon_nonneg
  | @step depth epsilon epsilon_nonneg noWinding logSmall tail ih =>
      cases r with
      | zero => exact .stop epsilon epsilon_nonneg
      | succ r =>
          exact .step epsilon epsilon_nonneg noWinding logSmall
            (ih r (Nat.le_of_succ_le_succ hr))

/-- Fin-indexed radius-chain prefix matching `ActiveRegionChain.takeFin`. -/
def CMP99SourceUbarRadiusChain.takeFin
    {depth : ℕ} {epsilon : ℝ}
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (r : Fin (depth + 1)) :
    CMP99SourceUbarRadiusChain d M Nc r.val epsilon :=
  chain.take r.val (Nat.lt_succ_iff.mp r.isLt)

@[simp]
theorem CMP99SourceUbarRadiusChain.take_zero
    {depth : ℕ} {epsilon : ℝ}
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon) :
    chain.take 0 (Nat.zero_le depth) =
      CMP99SourceUbarRadiusChain.stop epsilon chain.epsilon_nonneg := by
  cases chain <;> rfl

@[simp]
theorem CMP99SourceUbarRadiusChain.take_step_succ
    {depth r : ℕ} {epsilon : ℝ} (epsilon_nonneg : 0 ≤ epsilon)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilon <
      cmp99UbarNoWindingThreshold Nc)
    (logSmall :
      cmp99UbarLogRadius
          (cmp99SourceUbarFineNoWindingBudget
            (d := d) (M := M) (Nc := Nc) epsilon noWinding) < 1)
    (tail : CMP99SourceUbarRadiusChain d M Nc depth
      (cmp99SourceUbarNextFineRadius d M epsilon))
    (hr : r + 1 ≤ depth + 1) :
    (CMP99SourceUbarRadiusChain.step epsilon epsilon_nonneg noWinding logSmall
        tail).take (r + 1) hr =
      CMP99SourceUbarRadiusChain.step epsilon epsilon_nonneg noWinding logSmall
        (tail.take r (Nat.le_of_succ_le_succ hr)) := by
  rfl

/-- Transport of a generated retained-prefix identification across equality
of the active-region index.  Both truncations are constructed internally;
the caller supplies only the already-proved prefix equality. -/
theorem cmp99SourceRetainedWeightedPrefix_transport
    {Omega₁ Omega₂ : ActiveGaugeRegion d N} (h : Omega₁ = Omega₂)
    {rho : SUNAdjointModel Nc} {spacing epsilon : ℝ} {depth : ℕ}
    {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega₂ M spacing background depth)
    (regions : CMP99SourceActiveRegionChain d M N Omega₂ depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (r : Fin (depth + 1))
    (hprefix : T.towerAt r =
      (regions.takeFin r).weightedQprimeTower hd hM rho spacing epsilon
        background (chain.takeFin r) fineSmall) :
    ((h.symm ▸ T).towerAt r) =
      ((h.symm ▸ regions).takeFin r).weightedQprimeTower hd hM rho
        spacing epsilon background (chain.takeFin r) fineSmall := by
  cases h
  exact hprefix

/-- Every retained physical prefix is the literal weighted `Q'` tower on
the canonical truncation of the same source chains.  This is the family
version of the already sealed terminal-prefix theorem. -/
theorem cmp99SourceGeneratedRetainedPhysicalTower_towerAt_eq_take
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d N) :
    ∀ (depth : ℕ) (spacing epsilon : ℝ)
      (background : GaugeConfig d
        (cmp99RegionalLatticeSize M N depth) (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d
        (cmp99RegionalLatticeSize M N depth),
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (r : Fin (depth + 1)),
      (cmp99SourceGeneratedRetainedPhysicalTower hd hM rho Omega depth
        spacing epsilon background chain fineSmall).towerAt r =
        ((cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth).takeFin r
          |>.weightedQprimeTower hd hM rho spacing epsilon background
            (chain.takeFin r) fineSmall) := by
  intro depth
  induction depth with
  | zero =>
      intro spacing epsilon background chain fineSmall r
      have hr : r = 0 := Fin.eq_zero r
      subst r
      rfl
  | succ depth ih =>
      intro spacing epsilon background chain fineSmall r
      let Scale : CMP99SourceNormalizedRegionalScale
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
          background :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
          background
          (cmp99IteratedLiftActiveRegion_blockSaturated Omega depth)
          epsilon chain.epsilon_nonneg chain.head_noWinding fineSmall
      have nextSmall : ∀ e : ConcreteEdge d
          (cmp99RegionalLatticeSize M N depth),
          ‖(Scale.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [Scale, CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM
            (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
            background (cmp99SourceBlockAverageWeight M d) epsilon
            chain.epsilon_nonneg chain.head_noWinding chain.head_logSmall
            fineSmall e
      let Tail := cmp99SourceGeneratedRetainedPhysicalTower hd hM rho Omega
        depth ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall
      have hregion :
          cmp99ActiveCoarseRegion
              (M := M) (N' := cmp99RegionalLatticeSize M N depth)
              (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =
            cmp99IteratedLiftActiveRegion (M := M) Omega depth :=
        cmp99ActiveCoarseRegion_iteratedLift_succ_eq (M := M) Omega depth
      let Tail' : CMP99SourceRetainedPhysicalTower rho
          (cmp99ActiveCoarseRegion
            (M := M) (N' := cmp99RegionalLatticeSize M N depth)
            (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
          M ((M : ℝ) * spacing)
          Scale.toSourceScale.data.nextBackground depth :=
        hregion.symm ▸ Tail
      let regions :=
        cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
      let regions' : CMP99SourceActiveRegionChain d M
          (cmp99RegionalLatticeSize M N depth)
          (cmp99ActiveCoarseRegion
            (M := M) (N' := cmp99RegionalLatticeSize M N depth)
            (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
          depth := hregion.symm ▸ regions
      let regionsRec : CMP99SourceActiveRegionChain d M
          (cmp99RegionalLatticeSize M N depth)
          (cmp99ActiveCoarseRegion
            (M := M) (N' := cmp99RegionalLatticeSize M N depth)
            (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
          depth := by
        rw [hregion]
        exact regions
      have hregions : regions' = regionsRec := by
        simpa [regions', regionsRec] using
          regions.transport_eq_mpr hregion
      refine Fin.cases ?_ (fun s => ?_) r
      · rfl
      · have htail := ih ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          Scale.toSourceScale.data.nextBackground chain.tail nextSmall s
        have htail' :
            Tail'.towerAt s =
              (regions'.takeFin s).weightedQprimeTower hd hM rho
                ((M : ℝ) * spacing)
                (cmp99SourceUbarNextFineRadius d M epsilon)
                Scale.toSourceScale.data.nextBackground
                (chain.tail.takeFin s) nextSmall := by
          simpa [Tail', regions'] using
            cmp99SourceRetainedWeightedPrefix_transport hregion
              Tail regions hd hM chain.tail nextSmall s htail
        have htailRec :
            Tail'.towerAt s =
              (regionsRec.takeFin s).weightedQprimeTower hd hM rho
                ((M : ℝ) * spacing)
                (cmp99SourceUbarNextFineRadius d M epsilon)
                Scale.toSourceScale.data.nextBackground
                (chain.tail.takeFin s) nextSmall := by
          rw [← hregions]
          exact htail'
        change
          CMP99SourceWeightedRegionalTower.step
              (g := SUNLieCoord Nc)
              (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
              (cmp99IteratedLiftActiveRegion_blockSaturated Omega depth)
              spacing (cmp99SourceWeightedPhysicalTransport rho background)
              (Tail'.towerAt s) =
            CMP99SourceWeightedRegionalTower.step
              (g := SUNLieCoord Nc)
              (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
              (cmp99IteratedLiftActiveRegion_blockSaturated Omega depth)
              spacing (cmp99SourceWeightedPhysicalTransport rho background)
              ((regionsRec.takeFin s).weightedQprimeTower hd hM rho
                ((M : ℝ) * spacing)
                (cmp99SourceUbarNextFineRadius d M epsilon)
                Scale.toSourceScale.data.nextBackground
                (chain.tail.takeFin s) nextSmall)
        exact congrArg
          (CMP99SourceWeightedRegionalTower.step
            (g := SUNLieCoord Nc)
            (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
            (cmp99IteratedLiftActiveRegion_blockSaturated Omega depth)
            spacing (cmp99SourceWeightedPhysicalTransport rho background))
          htailRec

end

end YangMills.RG
