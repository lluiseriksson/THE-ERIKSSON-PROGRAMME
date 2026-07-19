/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalCoarseCovarianceDecay

/-!
# The finite CMP99 regional coarse-covariance telescope

The consecutive covariance defects live between genuinely different regional
Hilbert spaces.  This file keeps those types and constructs the direct physical
restriction between any two nested source regions through the common ambient
coarse lattice.  The restriction laws below are the algebraic input needed to
assemble the consecutive rectangular defects without zero-extending a
covariance and thereby creating a spurious boundary term.
-/

namespace YangMills.RG

noncomputable section

variable {Q M j Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}

/-- Algebraic rectangular telescope on four possibly different Hilbert
spaces.  This small lemma keeps the dependent source proof below free of
bundled-map normalization. -/
theorem continuousLinearMap_rectangular_telescope
    {Ezero Elarge Esmall Eterminal : Type*}
    [NormedAddCommGroup Ezero] [NormedSpace ℝ Ezero]
    [NormedAddCommGroup Elarge] [NormedSpace ℝ Elarge]
    [NormedAddCommGroup Esmall] [NormedSpace ℝ Esmall]
    [NormedAddCommGroup Eterminal] [NormedSpace ℝ Eterminal]
    (Rpre : Ezero →L[ℝ] Elarge) (Rstep : Elarge →L[ℝ] Esmall)
    (Rpost : Esmall →L[ℝ] Eterminal) (Rnext : Ezero →L[ℝ] Esmall)
    (Rcurr : Elarge →L[ℝ] Eterminal) (Cl : Elarge →L[ℝ] Elarge)
    (Cs : Esmall →L[ℝ] Esmall)
    (hprefix : Rstep.comp Rpre = Rnext)
    (hsuffix : Rpost.comp Rstep = Rcurr) :
    Rpost.comp ((Cs.comp Rstep - Rstep.comp Cl).comp Rpre) =
      Rpost.comp (Cs.comp Rnext) - Rcurr.comp (Cl.comp Rpre) := by
  apply ContinuousLinearMap.ext
  intro x
  have hp := DFunLike.congr_fun hprefix x
  have hs := DFunLike.congr_fun hsuffix (Cl (Rpre x))
  simp only [ContinuousLinearMap.comp_apply] at hp hs
  change Rpost (Cs (Rstep (Rpre x)) - Rstep (Cl (Rpre x))) =
    Rpost (Cs (Rnext x)) - Rcurr (Cl (Rpre x))
  rw [map_sub, hp, hs]

/-- Direct restriction between two nested coarse regional carriers.  The map
is written directly on the dependent site subtype; the nesting proof is the
only datum needed to reinterpret a small-region site as a large-region site. -/
noncomputable def cmp99OmegaCoarseDirectRestriction
    (Seq : CMP99SourceOmegaGeometry cell j) (r s : Fin (j + 2))
    (hrs : r ≤ s)
    (g : Type*) [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g] :
    CMP99OmegaRegionalCoarseField (M := M) Seq r g →L[ℝ]
      CMP99OmegaRegionalCoarseField (M := M) Seq s g :=
  LinearMap.toContinuousLinearMap
    { toFun := fun phi => WithLp.toLp 2 fun x =>
        phi ⟨x.1, by
          have hxs : x.1 ∈ Seq.regions s := by
            simpa only [cmp99OmegaActiveCoarseRegion_sites_eq] using x.2
          have hxr : x.1 ∈ Seq.regions r := Seq.nested hrs hxs
          simpa only [cmp99OmegaActiveCoarseRegion_sites_eq] using hxr⟩
      map_add' := fun phi psi => by ext x; rfl
      map_smul' := fun a phi => by ext x; rfl }

/-- Direct restriction to the same regional carrier is the identity. -/
theorem cmp99OmegaCoarseDirectRestriction_self
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (g : Type*) [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g] :
    cmp99OmegaCoarseDirectRestriction (M := M) Seq r r (le_refl r) g =
      ContinuousLinearMap.id ℝ
        (CMP99OmegaRegionalCoarseField (M := M) Seq r g) := by
  apply ContinuousLinearMap.ext
  intro phi
  ext x
  rfl

/-- Direct restrictions compose exactly along nested source regions. -/
theorem cmp99OmegaCoarseDirectRestriction_comp
    (Seq : CMP99SourceOmegaGeometry cell j) (r s t : Fin (j + 2))
    (hrs : r ≤ s) (hst : s ≤ t)
    (g : Type*) [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g] :
    (cmp99OmegaCoarseDirectRestriction (M := M) Seq s t hst g).comp
        (cmp99OmegaCoarseDirectRestriction (M := M) Seq r s hrs g) =
      cmp99OmegaCoarseDirectRestriction (M := M) Seq r t (hrs.trans hst) g := by
  apply ContinuousLinearMap.ext
  intro phi
  ext x
  rfl

set_option maxHeartbeats 1000000 in
/-- The direct restriction at one source step is definitionally the physical
terminal restriction already used in the rectangular resolvent identity. -/
theorem cmp99OmegaCoarseDirectRestriction_transition
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) :
    cmp99OmegaCoarseDirectRestriction (M := M) Seq
        (cmp99OmegaTransitionIndex r) (cmp99OmegaTransitionNextIndex r)
        (by change r.val ≤ r.val + 1; omega)
        (SUNLieCoord Nc) =
      cmp99OmegaSourcePhysicalOneStepTerminalRestriction
        Seq r rho U spacing := by
  apply ContinuousLinearMap.ext
  intro phi
  ext x
  have hxSmall : x.1 ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionNextIndex r))).sites := x.2
  have hxSmallRegion : x.1 ∈
      Seq.regions (cmp99OmegaTransitionNextIndex r) := by
    simpa only [cmp99OmegaActiveCoarseRegion_sites_eq] using hxSmall
  have hxLargeRegion : x.1 ∈
      Seq.regions (cmp99OmegaTransitionIndex r) :=
    Seq.nested (by change r.val ≤ r.val + 1; omega) hxSmallRegion
  have hxLarge : x.1 ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionIndex r))).sites := by
    simpa only [cmp99OmegaActiveCoarseRegion_sites_eq] using hxLargeRegion
  have hxLargeBlock : blockOf M (2 * Q) x.1 ⊆
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r)).sites :=
    (mem_cmp99ActiveCoarseRegion_sites_iff
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r)) x.1).mp hxLarge
  simp [cmp99OmegaCoarseDirectRestriction,
    cmp99OmegaSourcePhysicalOneStepTerminalRestriction,
    cmp99OmegaCoarseTransitionRestriction, restrictZeroCLM,
    extendZeroZeroCLM, hxLargeBlock]

/-- The `k`-th regional coarse covariance, transported from the common
initial carrier to the common terminal carrier. -/
noncomputable def cmp99OmegaEmbeddedCoarseCovariance
    (Seq : CMP99SourceOmegaGeometry cell j) (k : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    CMP99OmegaRegionalCoarseField (M := M) Seq (cmp99OmegaZeroIndex j)
        (SUNLieCoord Nc) →L[ℝ]
      CMP99OmegaRegionalCoarseField (M := M) Seq (cmp99OmegaLastIndex j)
        (SUNLieCoord Nc) :=
  (cmp99OmegaCoarseDirectRestriction (M := M) Seq k
      (cmp99OmegaLastIndex j) (by
        change k.val ≤ j + 1
        omega) (SUNLieCoord Nc)).comp
    ((cmp99OmegaSourcePhysicalOneStepCoarseCovariance
        Seq k rho U hspacing ha).comp
      (cmp99OmegaCoarseDirectRestriction (M := M) Seq
        (cmp99OmegaZeroIndex j) k (by
          change 0 ≤ k.val
          omega) (SUNLieCoord Nc)))

/-- One consecutive rectangular covariance defect, transported to the same
initial and terminal carriers as every other source transition. -/
noncomputable def cmp99OmegaEmbeddedCoarseCovarianceTransition
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    CMP99OmegaRegionalCoarseField (M := M) Seq (cmp99OmegaZeroIndex j)
        (SUNLieCoord Nc) →L[ℝ]
      CMP99OmegaRegionalCoarseField (M := M) Seq (cmp99OmegaLastIndex j)
        (SUNLieCoord Nc) :=
  (cmp99OmegaCoarseDirectRestriction (M := M) Seq
      (cmp99OmegaTransitionNextIndex r) (cmp99OmegaLastIndex j) (by
        change r.val + 1 ≤ j + 1
        omega) (SUNLieCoord Nc)).comp
    ((cmp99OmegaSourcePhysicalOneStepCoarseCovarianceTransition
        Seq r rho U hspacing ha).comp
      (cmp99OmegaCoarseDirectRestriction (M := M) Seq
        (cmp99OmegaZeroIndex j) (cmp99OmegaTransitionIndex r) (by
          change 0 ≤ r.val
          omega) (SUNLieCoord Nc)))

set_option maxHeartbeats 1000000 in
/-- Each embedded consecutive defect is exactly the difference of two
successive common-carrier covariance terms. -/
theorem cmp99OmegaEmbeddedCoarseCovarianceTransition_eq_sub
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    cmp99OmegaEmbeddedCoarseCovarianceTransition Seq r rho U hspacing ha =
      cmp99OmegaEmbeddedCoarseCovariance Seq
          (cmp99OmegaTransitionNextIndex r) rho U hspacing ha -
        cmp99OmegaEmbeddedCoarseCovariance Seq
          (cmp99OmegaTransitionIndex r) rho U hspacing ha := by
  have hprefix :
      (cmp99OmegaSourcePhysicalOneStepTerminalRestriction
          Seq r rho U spacing).comp
        (cmp99OmegaCoarseDirectRestriction (M := M) Seq
          (cmp99OmegaZeroIndex j) (cmp99OmegaTransitionIndex r) (by
            change 0 ≤ r.val
            omega) (SUNLieCoord Nc)) =
      cmp99OmegaCoarseDirectRestriction (M := M) Seq
        (cmp99OmegaZeroIndex j) (cmp99OmegaTransitionNextIndex r) (by
          change 0 ≤ r.val + 1
          omega) (SUNLieCoord Nc) := by
    rw [← cmp99OmegaCoarseDirectRestriction_transition
      (Seq := Seq) (r := r) rho U spacing]
    exact cmp99OmegaCoarseDirectRestriction_comp Seq
      (cmp99OmegaZeroIndex j) (cmp99OmegaTransitionIndex r)
      (cmp99OmegaTransitionNextIndex r)
      (by change 0 ≤ r.val; omega)
      (by change r.val ≤ r.val + 1; omega) (SUNLieCoord Nc)
  have hsuffix :
      (cmp99OmegaCoarseDirectRestriction (M := M) Seq
          (cmp99OmegaTransitionNextIndex r) (cmp99OmegaLastIndex j) (by
            change r.val + 1 ≤ j + 1
            omega) (SUNLieCoord Nc)).comp
        (cmp99OmegaSourcePhysicalOneStepTerminalRestriction
          Seq r rho U spacing) =
      cmp99OmegaCoarseDirectRestriction (M := M) Seq
        (cmp99OmegaTransitionIndex r) (cmp99OmegaLastIndex j) (by
          change r.val ≤ j + 1
          omega) (SUNLieCoord Nc) := by
    rw [← cmp99OmegaCoarseDirectRestriction_transition
      (Seq := Seq) (r := r) rho U spacing]
    exact cmp99OmegaCoarseDirectRestriction_comp Seq
      (cmp99OmegaTransitionIndex r) (cmp99OmegaTransitionNextIndex r)
      (cmp99OmegaLastIndex j)
      (by change r.val ≤ r.val + 1; omega)
      (by change r.val + 1 ≤ j + 1; omega) (SUNLieCoord Nc)
  unfold cmp99OmegaEmbeddedCoarseCovarianceTransition
    cmp99OmegaEmbeddedCoarseCovariance
    cmp99OmegaSourcePhysicalOneStepCoarseCovarianceTransition
  exact continuousLinearMap_rectangular_telescope _ _ _ _ _ _ _
    hprefix hsuffix

/-- Total rectangular covariance mismatch between the first and last source
regions.  Both covariance terms are compared only after the physical direct
restriction has put them in the same terminal carrier. -/
noncomputable def cmp99OmegaTotalCoarseCovarianceTransition
    (Seq : CMP99SourceOmegaGeometry cell j)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    CMP99OmegaRegionalCoarseField (M := M) Seq (cmp99OmegaZeroIndex j)
        (SUNLieCoord Nc) →L[ℝ]
      CMP99OmegaRegionalCoarseField (M := M) Seq (cmp99OmegaLastIndex j)
        (SUNLieCoord Nc) :=
  cmp99OmegaEmbeddedCoarseCovariance Seq (cmp99OmegaLastIndex j)
      rho U hspacing ha -
    cmp99OmegaEmbeddedCoarseCovariance Seq (cmp99OmegaZeroIndex j)
      rho U hspacing ha

/-- Nat-indexed view used only to invoke the standard finite telescoping
identity.  Outside the source range it is zero; every index consumed below is
proved to lie inside the range. -/
noncomputable def cmp99OmegaEmbeddedCoarseCovarianceNat
    (Seq : CMP99SourceOmegaGeometry cell j)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) (k : ℕ) :
    CMP99OmegaRegionalCoarseField (M := M) Seq (cmp99OmegaZeroIndex j)
        (SUNLieCoord Nc) →L[ℝ]
      CMP99OmegaRegionalCoarseField (M := M) Seq (cmp99OmegaLastIndex j)
        (SUNLieCoord Nc) :=
  if hk : k < j + 2 then
    cmp99OmegaEmbeddedCoarseCovariance Seq ⟨k, hk⟩ rho U hspacing ha
  else 0

/-- A consecutive source transition is one successive difference in the
Nat-indexed common-carrier family. -/
theorem cmp99OmegaEmbeddedCoarseCovarianceTransition_eq_nat_sub
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    cmp99OmegaEmbeddedCoarseCovarianceTransition Seq r rho U hspacing ha =
      cmp99OmegaEmbeddedCoarseCovarianceNat Seq rho U hspacing ha (r.val + 1) -
        cmp99OmegaEmbeddedCoarseCovarianceNat Seq rho U hspacing ha r.val := by
  rw [cmp99OmegaEmbeddedCoarseCovarianceTransition_eq_sub]
  have hr : r.val < j + 2 := by omega
  have hrs : r.val + 1 < j + 2 := by omega
  simp only [cmp99OmegaEmbeddedCoarseCovarianceNat, dif_pos hr, dif_pos hrs]
  rfl

/-- The two in-range endpoints of the Nat view are exactly the source
terminal and initial covariance terms. -/
theorem cmp99OmegaEmbeddedCoarseCovarianceNat_endpoints
    (Seq : CMP99SourceOmegaGeometry cell j)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    cmp99OmegaEmbeddedCoarseCovarianceNat Seq rho U hspacing ha (j + 1) -
        cmp99OmegaEmbeddedCoarseCovarianceNat Seq rho U hspacing ha 0 =
      cmp99OmegaTotalCoarseCovarianceTransition Seq rho U hspacing ha := by
  unfold cmp99OmegaEmbeddedCoarseCovarianceNat
    cmp99OmegaTotalCoarseCovarianceTransition
  simp only [dif_pos (show j + 1 < j + 2 by omega),
    dif_pos (show 0 < j + 2 by omega)]
  rfl

set_option maxHeartbeats 800000 in
/-- Exact finite source telescope: the sum of all physical consecutive
rectangular covariance defects is the first-to-last covariance mismatch.
No ambient zero extension and no postulated covariance difference occurs. -/
theorem sum_cmp99OmegaEmbeddedCoarseCovarianceTransition_eq_total
    (Seq : CMP99SourceOmegaGeometry cell j)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    ∑ r : Fin (j + 1),
        cmp99OmegaEmbeddedCoarseCovarianceTransition
          Seq r rho U hspacing ha =
      cmp99OmegaTotalCoarseCovarianceTransition Seq rho U hspacing ha := by
  rw [Finset.sum_fin_eq_sum_range]
  have htele := Finset.sum_range_sub
    (cmp99OmegaEmbeddedCoarseCovarianceNat Seq rho U hspacing ha) (j + 1)
  have hsum :
      ∑ k ∈ Finset.range (j + 1),
          (cmp99OmegaEmbeddedCoarseCovarianceNat Seq rho U hspacing ha (k + 1) -
            cmp99OmegaEmbeddedCoarseCovarianceNat Seq rho U hspacing ha k) =
        cmp99OmegaEmbeddedCoarseCovarianceNat Seq rho U hspacing ha (j + 1) -
          cmp99OmegaEmbeddedCoarseCovarianceNat Seq rho U hspacing ha 0 := htele
  rw [← cmp99OmegaEmbeddedCoarseCovarianceNat_endpoints
    Seq rho U hspacing ha, ← hsum]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < j + 1 := Finset.mem_range.mp hk
  simp only [hklt, dif_pos]
  exact cmp99OmegaEmbeddedCoarseCovarianceTransition_eq_nat_sub
    Seq ⟨k, hklt⟩ rho U hspacing ha



end

end YangMills.RG
