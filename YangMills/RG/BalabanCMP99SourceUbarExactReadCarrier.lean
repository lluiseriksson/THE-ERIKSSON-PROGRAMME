import YangMills.RG.BalabanCMP99SourceUbarContours
import YangMills.RG.BalabanCMP99PhysicalUbarGaugeConfig

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# Exact fine-bond read carrier of the literal CMP99 Ubar block

For one positive coarse bond the source formula reads the three literal
contours for every fine site of its source block and the straight fine path
which generates the coarse base background.  This module constructs precisely
that finite carrier and derives locality of the represented Ubar value from
agreement of positive fine-bond coordinates there.

The construction is indexed by a selected finite set of coarse bonds.  It does
not claim that the existing complete `nextBackground`, which constructs every
coarse bond, is regional.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]

/-- Positive physical coordinates read by a finite oriented edge list. -/
def cmp99PhysicalBondsOfEdgeList
    (es : List (ConcreteEdge d (L * N'))) :
    Finset (PhysicalBond d (L * N')) :=
  es.toFinset.image physicalBondOfEdge

theorem physicalBondOfEdge_mem_cmp99PhysicalBondsOfEdgeList
    (es : List (ConcreteEdge d (L * N'))) (e : ConcreteEdge d (L * N'))
    (he : e ∈ es) :
    physicalBondOfEdge e ∈ cmp99PhysicalBondsOfEdgeList es := by
  apply Finset.mem_image.mpr
  exact ⟨e, by simpa using he, rfl⟩

/-- The three literal fine contours entering the Ubar deviation at `x`. -/
def cmp99SourceUbarFineContourEdgeList
    (b : PhysicalBond d N') (x : FinBox d (L * N')) :
    List (ConcreteEdge d (L * N')) :=
  cmp99SourceUbarGamma1 (G := SUN Nc) b x ++
    cmp99SourceUbarGamma2 (G := SUN Nc) b x ++
      cmp99SourceUbarGamma3 (G := SUN Nc) b x

/-- The straight fine path which generates the base coarse value on `b`. -/
def cmp99SourceUbarBaseEdgeList
    (b : PhysicalBond d N') : List (ConcreteEdge d (L * N')) :=
  (cmp99SourceParallelTransportPath (G := SUN Nc)
    (blockBasepoint L N' b.1) b.2).edges

/-- Exact fine positive-bond read carrier of one literal source Ubar block. -/
def cmp99SourceUbarFineReadBonds
    (b : PhysicalBond d N') : Finset (PhysicalBond d (L * N')) :=
  cmp99PhysicalBondsOfEdgeList
      (cmp99SourceUbarBaseEdgeList (Nc := Nc) b) ∪
    (blockOf L N' b.1).biUnion fun x =>
      cmp99PhysicalBondsOfEdgeList
        (cmp99SourceUbarFineContourEdgeList (Nc := Nc) b x)

/-- Exact fine read carrier of a selected finite family of coarse bonds. -/
def cmp99SourceUbarFineReadBondsOfCoarseBonds
    (coarseBonds : Finset (PhysicalBond d N')) :
    Finset (PhysicalBond d (L * N')) :=
  coarseBonds.biUnion (cmp99SourceUbarFineReadBonds (Nc := Nc))

theorem physicalBondOfEdge_mem_cmp99SourceUbarFineReadBonds_of_base
    (b : PhysicalBond d N') (e : ConcreteEdge d (L * N'))
    (he : e ∈ cmp99SourceUbarBaseEdgeList (Nc := Nc) b) :
    physicalBondOfEdge e ∈ cmp99SourceUbarFineReadBonds (Nc := Nc) b := by
  exact Finset.mem_union_left _
    (physicalBondOfEdge_mem_cmp99PhysicalBondsOfEdgeList _ _ he)

theorem physicalBondOfEdge_mem_cmp99SourceUbarFineReadBonds_of_gamma1
    (b : PhysicalBond d N') (x : FinBox d (L * N'))
    (hx : x ∈ blockOf L N' b.1) (e : ConcreteEdge d (L * N'))
    (he : e ∈ cmp99SourceUbarGamma1 (G := SUN Nc) b x) :
    physicalBondOfEdge e ∈ cmp99SourceUbarFineReadBonds (Nc := Nc) b := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hx, physicalBondOfEdge_mem_cmp99PhysicalBondsOfEdgeList _ _ ?_⟩
  simp [cmp99SourceUbarFineContourEdgeList, he]

theorem physicalBondOfEdge_mem_cmp99SourceUbarFineReadBonds_of_gamma2
    (b : PhysicalBond d N') (x : FinBox d (L * N'))
    (hx : x ∈ blockOf L N' b.1) (e : ConcreteEdge d (L * N'))
    (he : e ∈ cmp99SourceUbarGamma2 (G := SUN Nc) b x) :
    physicalBondOfEdge e ∈ cmp99SourceUbarFineReadBonds (Nc := Nc) b := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hx, physicalBondOfEdge_mem_cmp99PhysicalBondsOfEdgeList _ _ ?_⟩
  simp [cmp99SourceUbarFineContourEdgeList, he]

theorem physicalBondOfEdge_mem_cmp99SourceUbarFineReadBonds_of_gamma3
    (b : PhysicalBond d N') (x : FinBox d (L * N'))
    (hx : x ∈ blockOf L N' b.1) (e : ConcreteEdge d (L * N'))
    (he : e ∈ cmp99SourceUbarGamma3 (G := SUN Nc) b x) :
    physicalBondOfEdge e ∈ cmp99SourceUbarFineReadBonds (Nc := Nc) b := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hx, physicalBondOfEdge_mem_cmp99PhysicalBondsOfEdgeList _ _ ?_⟩
  simp [cmp99SourceUbarFineContourEdgeList, he]

/-- Gauge configurations are determined on every oriented edge by agreement
on the corresponding positive physical coordinate. -/
theorem gaugeConfig_apply_eq_of_positivePhysicalBond_eq
    (U V : PhysicalGaugeBackground d (L * N') Nc)
    (e : ConcreteEdge d (L * N'))
    (h : U (positiveEdgeOfPhysicalBond (physicalBondOfEdge e)) =
      V (positiveEdgeOfPhysicalBond (physicalBondOfEdge e))) :
    U e = V e := by
  cases e with
  | mk x mu sign =>
      cases sign
      · have hU := U.map_reverse (ConcreteEdge.mk x mu true)
        have hV := V.map_reverse (ConcreteEdge.mk x mu true)
        change U (ConcreteEdge.mk x mu false) =
          (U (ConcreteEdge.mk x mu true))⁻¹ at hU
        change V (ConcreteEdge.mk x mu false) =
          (V (ConcreteEdge.mk x mu true))⁻¹ at hV
        change U (ConcreteEdge.mk x mu true) =
          V (ConcreteEdge.mk x mu true) at h
        rw [hU, hV, h]
      · exact h

/-- The coarse base value on one selected bond reads only its straight fine
path, already included in the exact Ubar carrier. -/
theorem cmp99SourceBaseCoarseBackground_apply_pos_eq_of_eqOn_readBonds
    (U V : PhysicalGaugeBackground d (L * N') Nc)
    (b : PhysicalBond d N')
    (hUV : ∀ q ∈ cmp99SourceUbarFineReadBonds (Nc := Nc) b,
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q)) :
    cmp99SourceBaseCoarseBackground U (positiveEdgeOfPhysicalBond b) =
      cmp99SourceBaseCoarseBackground V (positiveEdgeOfPhysicalBond b) := by
  rw [cmp99SourceBaseCoarseBackground_apply_pos,
    cmp99SourceBaseCoarseBackground_apply_pos]
  apply wilsonLine_congr
  intro e he
  apply gaugeConfig_apply_eq_of_positivePhysicalBond_eq U V e
  exact hUV _
    (physicalBondOfEdge_mem_cmp99SourceUbarFineReadBonds_of_base b e he)

/-- Locality of the literal represented Ubar value on one positive coarse
bond, derived from its internally generated fine read carrier. -/
theorem cmp99SourcePhysicalUbar_eq_of_eqOn_readBonds
    (U V : PhysicalGaugeBackground d (L * N') Nc)
    (b : PhysicalBond d N')
    (hUV : ∀ q ∈ cmp99SourceUbarFineReadBonds (Nc := Nc) b,
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q)) :
    Ubar (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        U (cmp99SourceBaseCoarseBackground U) (positiveEdgeOfPhysicalBond b)
        (cmp99SourceUbarGamma1 (G := SUN Nc) b)
        (cmp99SourceUbarGamma2 (G := SUN Nc) b)
        (cmp99SourceUbarGamma3 (G := SUN Nc) b) =
      Ubar (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        V (cmp99SourceBaseCoarseBackground V) (positiveEdgeOfPhysicalBond b)
        (cmp99SourceUbarGamma1 (G := SUN Nc) b)
        (cmp99SourceUbarGamma2 (G := SUN Nc) b)
        (cmp99SourceUbarGamma3 (G := SUN Nc) b) := by
  apply Ubar_locality
  · exact cmp99SourceBaseCoarseBackground_apply_pos_eq_of_eqOn_readBonds
      U V b hUV
  · intro x hx e he
    apply gaugeConfig_apply_eq_of_positivePhysicalBond_eq U V e
    exact hUV _
      (physicalBondOfEdge_mem_cmp99SourceUbarFineReadBonds_of_gamma1
        b x hx e he)
  · intro x hx e he
    apply gaugeConfig_apply_eq_of_positivePhysicalBond_eq U V e
    exact hUV _
      (physicalBondOfEdge_mem_cmp99SourceUbarFineReadBonds_of_gamma2
        b x hx e he)
  · intro x hx e he
    apply gaugeConfig_apply_eq_of_positivePhysicalBond_eq U V e
    exact hUV _
      (physicalBondOfEdge_mem_cmp99SourceUbarFineReadBonds_of_gamma3
        b x hx e he)

/-- Family form consumed by the future localized Ubar constructor. -/
theorem cmp99SourcePhysicalUbar_eq_of_eqOn_selectedReadBonds
    (U V : PhysicalGaugeBackground d (L * N') Nc)
    (coarseBonds : Finset (PhysicalBond d N'))
    (hUV : ∀ q ∈ cmp99SourceUbarFineReadBondsOfCoarseBonds
        (Nc := Nc) coarseBonds,
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q))
    (b : PhysicalBond d N') (hb : b ∈ coarseBonds) :
    Ubar (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        U (cmp99SourceBaseCoarseBackground U) (positiveEdgeOfPhysicalBond b)
        (cmp99SourceUbarGamma1 (G := SUN Nc) b)
        (cmp99SourceUbarGamma2 (G := SUN Nc) b)
        (cmp99SourceUbarGamma3 (G := SUN Nc) b) =
      Ubar (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        V (cmp99SourceBaseCoarseBackground V) (positiveEdgeOfPhysicalBond b)
        (cmp99SourceUbarGamma1 (G := SUN Nc) b)
        (cmp99SourceUbarGamma2 (G := SUN Nc) b)
        (cmp99SourceUbarGamma3 (G := SUN Nc) b) := by
  apply cmp99SourcePhysicalUbar_eq_of_eqOn_readBonds U V b
  intro q hq
  exact hUV q (Finset.mem_biUnion.mpr ⟨b, hb, hq⟩)

end

end YangMills.RG
