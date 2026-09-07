import YangMills.RG.BalabanCMP99SourceUbarExactReadCarrier
import YangMills.RG.BalabanCMP99SourceWeightedPhysicalTower

/-!


# Exact read carrier of one retained transported average

The one-step regional average targets exactly the coarse sites whose complete
fine blocks lie in the active region.  At each such site it reads the literal
block-contained contour from the canonical block basepoint to every fine site
of that block.  This module forms that finite carrier and derives equality of
the physical transport and of the full continuous-linear average from
positive-bond agreement there.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Exact fine positive-bond read carrier of the physical transported average
on one active region. -/
def cmp99SourceTransportedAverageFineReadBonds
    (Omega : ActiveGaugeRegion d (M * N')) :
    Finset (PhysicalBond d (M * N')) :=
  (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites.biUnion fun y =>
    (blockOf M N' y).biUnion fun x =>
      cmp99PhysicalBondsOfEdgeList
        (cmp99BlockContainedContourSystem (G := SUN Nc) y x).edges

theorem physicalBondOfEdge_mem_cmp99SourceTransportedAverageFineReadBonds
    (Omega : ActiveGaugeRegion d (M * N'))
    (y : FinBox d N')
    (hy : y ∈ (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites)
    (x : FinBox d (M * N')) (hx : x ∈ blockOf M N' y)
    (e : ConcreteEdge d (M * N'))
    (he : e ∈ (cmp99BlockContainedContourSystem (G := SUN Nc) y x).edges) :
    physicalBondOfEdge e ∈
      cmp99SourceTransportedAverageFineReadBonds (Nc := Nc) Omega := by
  apply Finset.mem_biUnion.mpr
  refine ⟨y, hy, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨x, hx,
    physicalBondOfEdge_mem_cmp99PhysicalBondsOfEdgeList _ _ he⟩

/-- Equality of the literal contour holonomy on every entry actually used by
the regional average. -/
theorem cmp99BlockContainedContourHolonomy_eq_of_eqOn_averageReadBonds
    (Omega : ActiveGaugeRegion d (M * N'))
    (U V : PhysicalGaugeBackground d (M * N') Nc)
    (hUV : ∀ q ∈ cmp99SourceTransportedAverageFineReadBonds
        (Nc := Nc) Omega,
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q))
    (y : FinBox d N')
    (hy : y ∈ (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites)
    (x : FinBox d (M * N')) (hx : x ∈ blockOf M N' y) :
    (cmp99BlockContainedContourSystem (G := SUN Nc) y x).holonomy U =
      (cmp99BlockContainedContourSystem (G := SUN Nc) y x).holonomy V := by
  apply wilsonLine_congr
  intro e he
  apply gaugeConfig_apply_eq_of_positivePhysicalBond_eq U V e
  exact hUV _
    (physicalBondOfEdge_mem_cmp99SourceTransportedAverageFineReadBonds
      Omega y hy x hx e he)

/-- The physical adjoint transport families agree on every `(y,x)` consumed
by the one-step regional average. -/
theorem cmp99SourceWeightedPhysicalTransport_apply_eq_of_eqOn_readBonds
    (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d (M * N'))
    (U V : PhysicalGaugeBackground d (M * N') Nc)
    (hUV : ∀ q ∈ cmp99SourceTransportedAverageFineReadBonds
        (Nc := Nc) Omega,
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q))
    (y : FinBox d N')
    (hy : y ∈ (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites)
    (x : FinBox d (M * N')) (hx : x ∈ blockOf M N' y) :
    cmp99SourceWeightedPhysicalTransport rho U y x =
      cmp99SourceWeightedPhysicalTransport rho V y x := by
  unfold cmp99SourceWeightedPhysicalTransport cmp99AdjointBlockTransport
    cmp99ContourHolonomy
  rw [cmp99BlockContainedContourHolonomy_eq_of_eqOn_averageReadBonds
    Omega U V hUV y hy x hx]

/-- One-step operator locality, with no supplied transport or operator
equality: the exact path carrier generates the conclusion. -/
theorem cmp99SourceTransportedBlockAverageCLM_eq_of_eqOn_readBonds
    (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d (M * N'))
    (U V : PhysicalGaugeBackground d (M * N') Nc)
    (hUV : ∀ q ∈ cmp99SourceTransportedAverageFineReadBonds
        (Nc := Nc) Omega,
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q)) :
    cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho U) =
      cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho V) := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro y
  unfold cmp99SourceTransportedBlockAverageCLM
  rw [cmp99TransportedBlockAverageCLM_apply,
    cmp99TransportedBlockAverageCLM_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro x _hx
  rw [cmp99SourceWeightedPhysicalTransport_apply_eq_of_eqOn_readBonds
    rho Omega U V hUV y.1 y.2 x.1 x.2]

end

end YangMills.RG
