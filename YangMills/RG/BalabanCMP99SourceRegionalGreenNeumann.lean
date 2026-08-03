/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99OneScaleRegionalPoincare
import YangMills.RG.BalabanCMP99PatchedParametrixNeumann
import YangMills.RG.BalabanCMP99SourceEq395HeadDictionary
import YangMills.RG.BalabanCMP99SourceGeneratedLaplacianTransitionSupport

/-!
# CMP99 Theorem 3.7: regional Green Neumann reconstruction

CMP99 equations (3.87)--(3.90) start from one ambient precision `Delta'`,
compress it to the square regions, construct the local Dirichlet inverses,
and patch them with a square partition satisfying `sum_Pi h_Pi^2 = 1`.
The exact commutator identity gives

`Delta' G'_0 = 1 - R'`,

and `norm R' < 1` produces `G' = G'_0 * sum_n (R')^n`.

This file implements that construction on one common ambient fine
zero-cochain carrier.  Every local Green is generated internally from the
same ambient precision and its Dirichlet compression.  The final equality to
the ambient Green follows from inverse uniqueness; it is not an input.

The remaining physical dictionary is separate: the source ambient
`Delta'_a/Q'` still has to be identified with the generated Section-C tower.
In particular, this file does not identify region-specific generated
precisions with one another.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {M Q : ℕ} [NeZero M] [NeZero Q]
variable {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
  [FiniteDimensional ℝ g]

private abbrev CMP99RegionalAmbientZeroField :=
  GaugeZeroCochain 4 (M * (2 * Q)) g

/-- Dirichlet compression of one ambient precision to an arbitrary active
square region. -/
noncomputable def cmp99RegionalDirichletPrecision
    (Omega : ActiveGaugeRegion 4 (M * (2 * Q)))
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g)) :
    ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g :=
  (restrictZeroCLM (𝔤 := g) Omega).comp
    (K.comp (extendZeroZeroCLM (𝔤 := g) Omega))

/-- Coercivity of the single ambient precision descends to every square
compression with no region-dependent premise. -/
theorem isCoerciveCLM_cmp99RegionalDirichletPrecision
    (Omega : ActiveGaugeRegion 4 (M * (2 * Q)))
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g))
    {c : ℝ} (hK : IsCoerciveCLM K c) :
    IsCoerciveCLM (cmp99RegionalDirichletPrecision Omega K) c := by
  intro phi
  let E := extendZeroZeroCLM (𝔤 := g) Omega
  let R := restrictZeroCLM (𝔤 := g) Omega
  have hR : R = E.adjoint :=
    cmp99ActiveRegion_restrictZero_eq_extendZero_adjoint Omega
  have hambient := hK (E phi)
  rw [norm_extendZeroZeroCLM_eq Omega phi] at hambient
  change c * ‖phi‖ ^ 2 ≤ inner ℝ phi (R (K (E phi)))
  rw [hR, ContinuousLinearMap.adjoint_inner_right]
  exact hambient

/-- The local Green is not supplied by the caller: it is the canonical
inverse of the Dirichlet compression of the one ambient precision. -/
noncomputable def cmp99RegionalDirichletGreen
    (Omega : ActiveGaugeRegion 4 (M * (2 * Q)))
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g))
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c) :
    ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g :=
  covarianceOfIsCoerciveCLM
    (cmp99RegionalDirichletPrecision Omega K) hc
    (isCoerciveCLM_cmp99RegionalDirichletPrecision Omega K hK)

/-- The local compressed precision is a left inverse of its generated
Dirichlet Green. -/
theorem cmp99RegionalDirichletPrecision_comp_green
    (Omega : ActiveGaugeRegion 4 (M * (2 * Q)))
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g))
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c) :
    (cmp99RegionalDirichletPrecision Omega K).comp
        (cmp99RegionalDirichletGreen Omega K hc hK) =
      ContinuousLinearMap.id ℝ (ActiveGaugeZeroCochain Omega g) := by
  exact precision_comp_covarianceOfIsCoerciveCLM _ hc _

/-- Zero-extend the generated local Green back to the single ambient carrier.
-/
noncomputable def cmp99RegionalExtendedDirichletGreen
    (Omega : ActiveGaugeRegion 4 (M * (2 * Q)))
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g))
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c) :
    CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) :=
  (extendZeroZeroCLM (𝔤 := g) Omega).comp
    ((cmp99RegionalDirichletGreen Omega K hc hK).comp
      (restrictZeroCLM (𝔤 := g) Omega))

/-- The smooth square multiplier `h_Pi`, pulled from the large-block lattice
to the ambient fine zero-cochain carrier. -/
noncomputable def cmp99RegionalSquareMultiplier
    (P : CMP99SourceSquarePartition Q) (cell : FinBox 4 Q) :
    CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) :=
  finitePiLpScalarMultiplier (g := g) fun x =>
    P.value cell (blockSite M (2 * Q) x)

/-- Geometric support condition: the square cutoff for `cell` vanishes
outside the local Dirichlet region assigned to that cell. -/
def CMP99RegionalSquarePartitionSupported
    (P : CMP99SourceSquarePartition Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q))) : Prop :=
  ∀ cell x,
    P.value cell (blockSite M (2 * Q) x) ≠ 0 → x ∈ (Omega cell).sites

/-- Quantified collar separating every nonzero square cutoff from the
complement of its Dirichlet region.  The number `finiteRange` is the physical
range of the ambient precision.  This condition is deliberately stronger
than `CMP99RegionalSquarePartitionSupported`: it is the source-facing margin
needed later to prove locality and smallness of the regional commutator
defect.  The exact inverse-sandwich identities below use only support
inclusion and therefore do not consume this premise. -/
def CMP99RegionalSquarePartitionHasFiniteRangeMargin
    (P : CMP99SourceSquarePartition Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (finiteRange : ℕ) : Prop :=
  ∀ cell x y,
    P.value cell (blockSite M (2 * Q) x) ≠ 0 →
      y ∉ (Omega cell).sites →
        finiteRange < finBoxDist x y

/-- A positive finite-range collar in particular implies ordinary support
inside the corresponding Dirichlet region. -/
theorem cmp99RegionalSquarePartitionSupported_of_finiteRangeMargin
    (P : CMP99SourceSquarePartition Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (finiteRange : ℕ)
    (hmargin :
      CMP99RegionalSquarePartitionHasFiniteRangeMargin P Omega finiteRange) :
    CMP99RegionalSquarePartitionSupported P Omega := by
  intro cell x hx
  by_contra houtside
  have himpossible := hmargin cell x x hx houtside
  simpa using himpossible

/-- The partition multiplier is unchanged by the characteristic projector of
its supporting Dirichlet region. -/
theorem cmp99RegionalSquareMultiplier_comp_regionProjector
    (P : CMP99SourceSquarePartition Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (hsupport : CMP99RegionalSquarePartitionSupported P Omega)
    (cell : FinBox 4 Q) :
    (cmp99RegionalSquareMultiplier (M := M) (g := g) P cell).comp
        ((extendZeroZeroCLM (𝔤 := g) (Omega cell)).comp
          (restrictZeroCLM (𝔤 := g) (Omega cell))) =
      cmp99RegionalSquareMultiplier (M := M) (g := g) P cell := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  by_cases hx : x ∈ (Omega cell).sites
  · simp [cmp99RegionalSquareMultiplier, ContinuousLinearMap.comp_apply,
      finitePiLpScalarMultiplier_apply, extendZeroZeroCLM, restrictZeroCLM,
      hx]
  · have hzero : P.value cell (blockSite M (2 * Q) x) = 0 := by
      by_contra hne
      exact hx (hsupport cell x hne)
    simp [cmp99RegionalSquareMultiplier, ContinuousLinearMap.comp_apply,
      finitePiLpScalarMultiplier_apply, extendZeroZeroCLM, restrictZeroCLM,
      hx, hzero]

/-- Exact local inverse sandwich `h_Pi Delta' G'_Pi h_Pi = h_Pi^2`.
The Green is the internally generated Dirichlet inverse above. -/
theorem cmp99RegionalSquareMultiplier_precision_green_eq_sq
    (P : CMP99SourceSquarePartition Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (hsupport : CMP99RegionalSquarePartitionSupported P Omega)
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g))
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c)
    (cell : FinBox 4 Q) :
    (cmp99RegionalSquareMultiplier (M := M) (g := g) P cell).comp
        (K.comp
          ((cmp99RegionalExtendedDirichletGreen (Omega cell) K hc hK).comp
            (cmp99RegionalSquareMultiplier (M := M) (g := g) P cell))) =
      (cmp99RegionalSquareMultiplier (M := M) (g := g) P cell).comp
        (cmp99RegionalSquareMultiplier (M := M) (g := g) P cell) := by
  let H := cmp99RegionalSquareMultiplier (M := M) (g := g) P cell
  let E := extendZeroZeroCLM (𝔤 := g) (Omega cell)
  let R := restrictZeroCLM (𝔤 := g) (Omega cell)
  let Ki := cmp99RegionalDirichletPrecision (Omega cell) K
  let Gi := cmp99RegionalDirichletGreen (Omega cell) K hc hK
  have hKiGi : Ki.comp Gi =
      ContinuousLinearMap.id ℝ (ActiveGaugeZeroCochain (Omega cell) g) := by
    exact cmp99RegionalDirichletPrecision_comp_green (Omega cell) K hc hK
  have hproject : H.comp (E.comp R) = H := by
    exact cmp99RegionalSquareMultiplier_comp_regionProjector
      P Omega hsupport cell
  apply ContinuousLinearMap.ext
  intro phi
  have hinverse := congrArg
    (fun A => A (R (H phi))) hKiGi
  have hprojectHphi := congrArg (fun A => A (H phi)) hproject
  change H (K (E (Gi (R (H phi))))) = H (H phi)
  have hrestricted : R (K (E (Gi (R (H phi))))) = R (H phi) := by
    simpa [Ki, cmp99RegionalDirichletPrecision,
      ContinuousLinearMap.comp_apply] using hinverse
  have hprojected : H (E (R (K (E (Gi (R (H phi))))))) = H (H phi) := by
    rw [hrestricted]
    simpa [ContinuousLinearMap.comp_apply] using hprojectHphi
  have hleft : H (K (E (Gi (R (H phi))))) =
      H (E (R (K (E (Gi (R (H phi))))))) := by
    have h := congrArg (fun A => A (K (E (Gi (R (H phi)))))) hproject
    simpa [ContinuousLinearMap.comp_apply] using h.symm
  exact hleft.trans hprojected

/-- Literal commutator `K(h_Pi) = h_Pi Delta' - Delta' h_Pi`. -/
noncomputable def cmp99RegionalSquarePrecisionCommutator
    (P : CMP99SourceSquarePartition Q) (cell : FinBox 4 Q)
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g)) :=
  (cmp99RegionalSquareMultiplier (M := M) (g := g) P cell).comp K -
    K.comp (cmp99RegionalSquareMultiplier (M := M) (g := g) P cell)

/-- One local head `h_Pi G'_Pi h_Pi` in (3.87). -/
noncomputable def cmp99RegionalGreenHead
    (P : CMP99SourceSquarePartition Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g))
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c)
    (cell : FinBox 4 Q) :=
  let H := cmp99RegionalSquareMultiplier (M := M) (g := g) P cell
  H.comp ((cmp99RegionalExtendedDirichletGreen (Omega cell) K hc hK).comp H)

/-- One literal correction factor `K(h_Pi) G'_Pi h_Pi` in (3.88). -/
noncomputable def cmp99RegionalGreenCorrection
    (P : CMP99SourceSquarePartition Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g))
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c)
    (cell : FinBox 4 Q) :=
  (cmp99RegionalSquarePrecisionCommutator (M := M) (g := g) P cell K).comp
    ((cmp99RegionalExtendedDirichletGreen (Omega cell) K hc hK).comp
      (cmp99RegionalSquareMultiplier (M := M) (g := g) P cell))

/-- The exact single-square identity behind (3.88). -/
theorem comp_cmp99RegionalGreenHead_eq_sq_sub_correction
    (P : CMP99SourceSquarePartition Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (hsupport : CMP99RegionalSquarePartitionSupported P Omega)
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g))
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c)
    (cell : FinBox 4 Q) :
    K.comp (cmp99RegionalGreenHead P Omega K hc hK cell) =
      (cmp99RegionalSquareMultiplier (M := M) (g := g) P cell).comp
          (cmp99RegionalSquareMultiplier (M := M) (g := g) P cell) -
        cmp99RegionalGreenCorrection P Omega K hc hK cell := by
  have hsandwich := cmp99RegionalSquareMultiplier_precision_green_eq_sq
    P Omega hsupport K hc hK cell
  apply ContinuousLinearMap.ext
  intro phi
  have hsandwichPhi := congrArg (fun A => A phi) hsandwich
  simp only [cmp99RegionalGreenHead, cmp99RegionalGreenCorrection,
    cmp99RegionalSquarePrecisionCommutator,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply] at *
  rw [hsandwichPhi]
  abel

/-- The finite parametrix `G'_0` in (3.87). -/
noncomputable def cmp99RegionalGreenParametrix
    (P : CMP99SourceSquarePartition Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g))
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c) :=
  ∑ cell : FinBox 4 Q, cmp99RegionalGreenHead P Omega K hc hK cell

/-- The finite defect `R'` in (3.88). -/
noncomputable def cmp99RegionalGreenDefect
    (P : CMP99SourceSquarePartition Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g))
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c) :=
  ∑ cell : FinBox 4 Q, cmp99RegionalGreenCorrection P Omega K hc hK cell

/-- Exact global parametrix identity `Delta' G'_0 = 1 - R'`. -/
theorem comp_cmp99RegionalGreenParametrix_eq_id_sub_defect
    (P : CMP99SourceSquarePartition Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (hsupport : CMP99RegionalSquarePartitionSupported P Omega)
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g))
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c) :
    K.comp (cmp99RegionalGreenParametrix P Omega K hc hK) =
      ContinuousLinearMap.id ℝ
          (CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g)) -
        cmp99RegionalGreenDefect P Omega K hc hK := by
  apply ContinuousLinearMap.ext
  intro phi
  simp only [cmp99RegionalGreenParametrix, cmp99RegionalGreenDefect,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sum]
  have hpartition :
      (∑ cell : FinBox 4 Q,
        (cmp99RegionalSquareMultiplier (M := M) (g := g) P cell).comp
          (cmp99RegionalSquareMultiplier (M := M) (g := g) P cell)) =
        ContinuousLinearMap.id ℝ
          (CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g)) := by
    simpa [cmp99RegionalSquareMultiplier] using
      (sum_cmp99SourceSquarePartition_multiplier_sq_eq_id
        (g := g) P (blockSite M (2 * Q)))
  have hpartition_apply :
      (∑ cell : FinBox 4 Q,
        (cmp99RegionalSquareMultiplier (M := M) (g := g) P cell)
          ((cmp99RegionalSquareMultiplier (M := M) (g := g) P cell) phi)) =
        phi := by
    have h := DFunLike.congr_fun hpartition phi
    simpa only [ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h
  calc
    _ = ∑ cell : FinBox 4 Q, (
        (cmp99RegionalSquareMultiplier (M := M) (g := g) P cell)
            ((cmp99RegionalSquareMultiplier (M := M) (g := g) P cell) phi) -
          (cmp99RegionalGreenCorrection P Omega K hc hK cell) phi) := by
      apply Finset.sum_congr rfl
      intro cell _hcell
      exact DFunLike.congr_fun
        (comp_cmp99RegionalGreenHead_eq_sq_sub_correction
          P Omega hsupport K hc hK cell) phi
    _ = (∑ cell : FinBox 4 Q,
          (cmp99RegionalSquareMultiplier (M := M) (g := g) P cell)
            ((cmp99RegionalSquareMultiplier (M := M) (g := g) P cell) phi)) -
        ∑ cell : FinBox 4 Q,
          (cmp99RegionalGreenCorrection P Omega K hc hK cell) phi := by
      rw [Finset.sum_sub_distrib]
    _ = phi - ∑ cell : FinBox 4 Q,
          (cmp99RegionalGreenCorrection P Omega K hc hK cell) phi := by
      rw [hpartition_apply]

/-- The corrected regional parametrix, definitionally
`G'_0 * sum_n (R')^n`. -/
noncomputable def cmp99RegionalGreenNeumann
    (P : CMP99SourceSquarePartition Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g))
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c) :=
  cmp99CorrectedParametrix
    (cmp99RegionalGreenParametrix P Omega K hc hK)
    (-cmp99RegionalGreenDefect P Omega K hc hK)

/-- The corrected object is exactly the printed geometric series. -/
theorem cmp99RegionalGreenNeumann_eq_parametrix_comp_tsum_pow
    (P : CMP99SourceSquarePartition Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g))
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c) :
    cmp99RegionalGreenNeumann P Omega K hc hK =
      (cmp99RegionalGreenParametrix P Omega K hc hK).comp
        (∑' n : ℕ, (cmp99RegionalGreenDefect P Omega K hc hK) ^ n) := by
  simp [cmp99RegionalGreenNeumann, cmp99CorrectedParametrix,
    cmp99PatchedDefectNeumannInverse_neg_eq_tsum_pow]

/-- Under the one visible contraction, the regional Neumann construction is
an exact right inverse of the ambient precision. -/
theorem comp_cmp99RegionalGreenNeumann_eq_id
    (P : CMP99SourceSquarePartition Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (hsupport : CMP99RegionalSquarePartitionSupported P Omega)
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g))
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c)
    (hdefect : ‖cmp99RegionalGreenDefect P Omega K hc hK‖ < 1) :
    K.comp (cmp99RegionalGreenNeumann P Omega K hc hK) =
      ContinuousLinearMap.id ℝ
        (CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g)) := by
  apply comp_cmp99CorrectedParametrix_eq_id
  · rw [comp_cmp99RegionalGreenParametrix_eq_id_sub_defect
      P Omega hsupport K hc hK]
    abel
  · rw [norm_neg]
    exact hdefect

/-- CMP99 Theorem 3.7 on the common carrier: the internally patched local
series is the canonical ambient Green.  No equality to a caller-supplied
Green appears among the hypotheses. -/
theorem cmp99RegionalGreenNeumann_eq_ambientGreen
    (P : CMP99SourceSquarePartition Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (hsupport : CMP99RegionalSquarePartitionSupported P Omega)
    (K : CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g) →L[ℝ]
      CMP99RegionalAmbientZeroField (M := M) (Q := Q) (g := g))
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c)
    (hdefect : ‖cmp99RegionalGreenDefect P Omega K hc hK‖ < 1) :
    cmp99RegionalGreenNeumann P Omega K hc hK =
      covarianceOfIsCoerciveCLM K hc hK := by
  let G := covarianceOfIsCoerciveCLM K hc hK
  let GN := cmp99RegionalGreenNeumann P Omega K hc hK
  have hGK : G.comp K = ContinuousLinearMap.id ℝ _ :=
    covarianceOfIsCoerciveCLM_comp_precision K hc hK
  have hKGN : K.comp GN = ContinuousLinearMap.id ℝ _ :=
    comp_cmp99RegionalGreenNeumann_eq_id
      P Omega hsupport K hc hK hdefect
  calc
    GN = (ContinuousLinearMap.id ℝ _).comp GN := by simp
    _ = (G.comp K).comp GN := by rw [hGK]
    _ = G.comp (K.comp GN) := ContinuousLinearMap.comp_assoc _ _ _
    _ = G.comp (ContinuousLinearMap.id ℝ _) := by rw [hKGN]
    _ = G := by simp

end

end YangMills.RG
