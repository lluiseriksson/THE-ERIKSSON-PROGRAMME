import YangMills.RG.BalabanCMP99SourceTransportedAverageExactReadCarrier
import YangMills.RG.BalabanCMP99SourceGeneratedScaledGradient

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# Exact fine read carrier of a retained physical tower

The complete source `nextBackground` is global, but a retained regional tower
does not need equality of that complete configuration.  At every successor it
needs only:

* the fine bonds read by the current transported average; and
* enough fine bonds to determine the selected coarse bonds read by the tail.

This module pulls the latter family back through the literal Ubar contours and
recurses along the proof-carrying active-region chain.  It therefore records
the exact finite carrier needed for locality of the retained prefix without
claiming locality of the global `nextBackground`.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Fine positive bonds sufficient to determine every one-step transported
average in a typed retained region chain.  In the successor case the tail
carrier is pulled back through the exact selected-family Ubar carrier. -/
noncomputable def CMP99SourceActiveRegionChain.retainedFineReadBonds
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    Finset (PhysicalBond d N) := by
  induction regions with
  | stop Omega => exact ∅
  | @step N' depth _ Omega hOmega tail ih =>
      exact cmp99SourceTransportedAverageFineReadBonds (Nc := Nc) Omega ∪
        cmp99SourceUbarFineReadBondsOfCoarseBonds (Nc := Nc) ih

omit [NeZero d] [NeZero N] in
@[simp] theorem CMP99SourceActiveRegionChain.retainedFineReadBonds_stop
    (Omega : ActiveGaugeRegion d N) :
    (CMP99SourceActiveRegionChain.stop (M := M) Omega).
        retainedFineReadBonds (Nc := Nc) = ∅ :=
  rfl

omit [NeZero N] in
theorem CMP99SourceActiveRegionChain.retainedFineReadBonds_step
    {N' depth : ℕ} [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (tail : CMP99SourceActiveRegionChain d M N'
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) depth) :
    (CMP99SourceActiveRegionChain.step Omega hOmega tail).
        retainedFineReadBonds (Nc := Nc) =
      cmp99SourceTransportedAverageFineReadBonds (Nc := Nc) Omega ∪
        cmp99SourceUbarFineReadBondsOfCoarseBonds (Nc := Nc)
          (tail.retainedFineReadBonds (Nc := Nc)) :=
  rfl

/-- Agreement on the recursive carrier supplies every bond read by the head
transported average. -/
omit [NeZero N] in
theorem eqOn_averageReadBonds_of_eqOn_retainedFineReadBonds
    {N' depth : ℕ} [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (tail : CMP99SourceActiveRegionChain d M N'
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) depth)
    (U V : PhysicalGaugeBackground d (M * N') Nc)
    (hUV : ∀ q ∈ (CMP99SourceActiveRegionChain.step Omega hOmega tail).
        retainedFineReadBonds (Nc := Nc),
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q)) :
    ∀ q ∈ cmp99SourceTransportedAverageFineReadBonds (Nc := Nc) Omega,
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q) := by
  intro q hq
  exact hUV q (by
    rw [CMP99SourceActiveRegionChain.retainedFineReadBonds_step]
    exact Finset.mem_union_left _ hq)

/-- Agreement on the recursive carrier also supplies precisely the Ubar
pullback required to determine every coarse bond read by the tail. -/
omit [NeZero N] in
theorem eqOn_tailUbarReadBonds_of_eqOn_retainedFineReadBonds
    {N' depth : ℕ} [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (tail : CMP99SourceActiveRegionChain d M N'
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) depth)
    (U V : PhysicalGaugeBackground d (M * N') Nc)
    (hUV : ∀ q ∈ (CMP99SourceActiveRegionChain.step Omega hOmega tail).
        retainedFineReadBonds (Nc := Nc),
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q)) :
    ∀ q ∈ cmp99SourceUbarFineReadBondsOfCoarseBonds (Nc := Nc)
        (tail.retainedFineReadBonds (Nc := Nc)),
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q) := by
  intro q hq
  exact hUV q (by
    rw [CMP99SourceActiveRegionChain.retainedFineReadBonds_step]
    exact Finset.mem_union_right _ hq)

/-- The current literal one-step average is local on the recursively generated
carrier.  No transport family or operator equality is accepted as input. -/
omit [NeZero N] in
theorem cmp99SourceTransportedBlockAverageCLM_eq_of_eqOn_retainedFineReadBonds
    {N' depth : ℕ} [NeZero N']
    (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (tail : CMP99SourceActiveRegionChain d M N'
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) depth)
    (U V : PhysicalGaugeBackground d (M * N') Nc)
    (hUV : ∀ q ∈ (CMP99SourceActiveRegionChain.step Omega hOmega tail).
        retainedFineReadBonds (Nc := Nc),
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q)) :
    cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho U) =
      cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho V) :=
  cmp99SourceTransportedBlockAverageCLM_eq_of_eqOn_readBonds rho Omega U V
    (eqOn_averageReadBonds_of_eqOn_retainedFineReadBonds
      Omega hOmega tail U V hUV)

/-- Every raw Ubar value needed by the tail is fixed by the recursively
generated fine carrier.  This deliberately stops short of equality of the
complete global next background. -/
omit [NeZero N] in
theorem cmp99SourcePhysicalUbar_eq_of_eqOn_retainedTailReadBonds
    {N' depth : ℕ} [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (tail : CMP99SourceActiveRegionChain d M N'
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) depth)
    (U V : PhysicalGaugeBackground d (M * N') Nc)
    (hUV : ∀ q ∈ (CMP99SourceActiveRegionChain.step Omega hOmega tail).
        retainedFineReadBonds (Nc := Nc),
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q))
    (b : PhysicalBond d N')
    (hb : b ∈ tail.retainedFineReadBonds (Nc := Nc)) :
    Ubar (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        U (cmp99SourceBaseCoarseBackground U) (positiveEdgeOfPhysicalBond b)
        (cmp99SourceUbarGamma1 (G := SUN Nc) b)
        (cmp99SourceUbarGamma2 (G := SUN Nc) b)
        (cmp99SourceUbarGamma3 (G := SUN Nc) b) =
      Ubar (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        V (cmp99SourceBaseCoarseBackground V) (positiveEdgeOfPhysicalBond b)
        (cmp99SourceUbarGamma1 (G := SUN Nc) b)
        (cmp99SourceUbarGamma2 (G := SUN Nc) b)
        (cmp99SourceUbarGamma3 (G := SUN Nc) b) :=
  cmp99SourcePhysicalUbar_eq_of_eqOn_selectedReadBonds U V
    (tail.retainedFineReadBonds (Nc := Nc))
    (eqOn_tailUbarReadBonds_of_eqOn_retainedFineReadBonds
      Omega hOmega tail U V hUV) b hb

end

end YangMills.RG
