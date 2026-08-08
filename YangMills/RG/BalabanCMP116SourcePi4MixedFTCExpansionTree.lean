/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Complex.RealDeriv
import YangMills.RG.BalabanCMP116FTCInterpolation
import YangMills.RG.BalabanCMP116SourcePi4MixedWeakenedCovarianceDerivativeSeries

/-!
# The source-specific iterated FTC tree

This module inserts the complete mixed physical weakening derivatives into the
finite FTC tree used by CMP116.  The remaining coordinates are set to their
fully coupled value in each node curve; the base and fiber recursively expand
the zero endpoint and the genuine mixed derivative, respectively.

Consequently, the tree records nested integrals of the actual length-ordered
physical covariance derivatives.  It is not an endpoint Möbius expansion.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Set every coordinate occurring in `L` to `z`, leaving all other
coordinates unchanged. -/
def cmp116SetWeakeningList
    {D : Type*} [DecidableEq D]
    (sigma : D → ℂ) (L : List D) (z : ℂ) : D → ℂ :=
  fun x => if x ∈ L then z else sigma x

theorem cmp116SetWeakeningList_nil
    {D : Type*} [DecidableEq D]
    (sigma : D → ℂ) (z : ℂ) :
    cmp116SetWeakeningList sigma [] z = sigma := by
  funext x
  simp [cmp116SetWeakeningList]

theorem cmp116SetWeakeningList_cons_of_not_mem
    {D : Type*} [DecidableEq D]
    (sigma : D → ℂ) (d : D) (L : List D) (z : ℂ)
    (_hdL : d ∉ L) :
    cmp116SetWeakeningList sigma (d :: L) z =
      Function.update (cmp116SetWeakeningList sigma L z) d z := by
  funext x
  by_cases hxd : x = d
  · subst x
    simp [cmp116SetWeakeningList]
  · simp [cmp116SetWeakeningList, hxd]

theorem cmp116SetWeakeningList_update_of_not_mem
    {D : Type*} [DecidableEq D]
    (sigma : D → ℂ) (d : D) (L : List D) (z w : ℂ)
    (hdL : d ∉ L) :
    cmp116SetWeakeningList (Function.update sigma d z) L w =
      Function.update (cmp116SetWeakeningList sigma L w) d z := by
  funext x
  by_cases hxL : x ∈ L
  · have hxd : x ≠ d := by
      intro h
      subst x
      exact hdL hxL
    simp [cmp116SetWeakeningList, hxL, hxd]
  · by_cases hxd : x = d
    · subst x
      simp [cmp116SetWeakeningList, hdL]
    · simp [cmp116SetWeakeningList, hxL, hxd]

private theorem cmp116SetWeakeningList_unitShifted
    {D : Type*} [DecidableEq D]
    (sigma : D → ℂ) (L : List D)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ)) :
    ∀ x, ‖cmp116SetWeakeningList sigma L 1 x - 1‖ ≤ (1 : ℝ) := by
  intro x
  by_cases hx : x ∈ L
  · simp [cmp116SetWeakeningList, hx]
  · simpa [cmp116SetWeakeningList, hx] using hsigma x

private theorem cmp116SetWeakeningList_cap
    {D : Type*} [DecidableEq D]
    (sigma : D → ℂ) (L : List D) (Rweak : ℝ)
    (hRweak : 1 ≤ Rweak) (hcap : ∀ x, ‖sigma x‖ ≤ Rweak) :
    ∀ x, ‖cmp116SetWeakeningList sigma L 1 x‖ ≤ Rweak := by
  intro x
  by_cases hx : x ∈ L
  · simpa [cmp116SetWeakeningList, hx] using hRweak
  · simpa [cmp116SetWeakeningList, hx] using hcap x

private theorem update_ofReal_unitShifted
    {D : Type*} [DecidableEq D]
    (sigma : D → ℂ) (d : D) (t : ℝ)
    (ht : t ∈ Set.uIcc (0 : ℝ) 1)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ)) :
    ∀ x, ‖Function.update sigma d (t : ℂ) x - 1‖ ≤ (1 : ℝ) := by
  have ht' : 0 ≤ t ∧ t ≤ 1 := by
    simpa [Set.uIcc_of_le zero_le_one] using ht
  intro x
  by_cases hx : x = d
  · subst x
    rw [Function.update_self, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr ht'.2)]
    linarith
  · rw [Function.update_of_ne hx]
    exact hsigma x

private theorem update_ofReal_cap
    {D : Type*} [DecidableEq D]
    (sigma : D → ℂ) (d : D) (t Rweak : ℝ)
    (ht : t ∈ Set.uIcc (0 : ℝ) 1)
    (hRweak : 1 ≤ Rweak) (hcap : ∀ x, ‖sigma x‖ ≤ Rweak) :
    ∀ x, ‖Function.update sigma d (t : ℂ) x‖ ≤ Rweak := by
  have ht' : 0 ≤ t ∧ t ≤ 1 := by
    simpa [Set.uIcc_of_le zero_le_one] using ht
  intro x
  by_cases hx : x = d
  · subst x
    rw [Function.update_self, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht'.1]
    exact ht'.2.trans hRweak
  · rw [Function.update_of_ne hx]
    exact hcap x

/-- The literal finite-depth FTC tree for one matrix entry of a mixed
physical covariance series. -/
noncomputable def cmp116SourcePi4MixedCovarianceFTCExpansionTree
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (L : List (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    CMP116FTCExpansionTree ℂ L.length :=
  match L with
  | [] =>
      .leaf
        (cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
          (R := R) anchor K hc hmass hK sigma S row col)
  | d :: tail =>
      let endpointSigma := cmp116SetWeakeningList sigma tail 1
      .node
        (fun t =>
          cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
            (R := R) anchor K hc hmass hK
            (Function.update endpointSigma d (t : ℂ)) S row col)
        (fun _ =>
          cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
            (R := R) anchor K hc hmass hK
            endpointSigma (insert d S) row col)
        (cmp116SourcePi4MixedCovarianceFTCExpansionTree
          (R := R) anchor K hc hmass hK
          (Function.update sigma d 0) S tail row col)
        (fun t =>
          cmp116SourcePi4MixedCovarianceFTCExpansionTree
            (R := R) anchor K hc hmass hK
            (Function.update sigma d (t : ℂ))
              (insert d S) tail row col)

/-- The coupled endpoint of the source-specific tree is the mixed covariance
with every listed remaining coordinate set to one. -/
theorem cmp116SourcePi4MixedCovarianceFTCExpansionTree_coupledEndpoint
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    (cmp116SourcePi4MixedCovarianceFTCExpansionTree
      (R := R) anchor K hc hmass hK sigma S L row col).coupledEndpoint =
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
        (R := R) anchor K hc hmass hK
        (cmp116SetWeakeningList sigma L 1) S row col := by
  induction L generalizing sigma S with
  | nil =>
      simp [cmp116SourcePi4MixedCovarianceFTCExpansionTree,
        CMP116FTCExpansionTree.coupledEndpoint,
        cmp116SetWeakeningList_nil]
  | cons d tail ih =>
      have hdTail : d ∉ tail := (List.nodup_cons.mp hL).1
      change
        cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
            (R := R) anchor K hc hmass hK
            (Function.update (cmp116SetWeakeningList sigma tail 1) d 1)
            S row col =
          cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
            (R := R) anchor K hc hmass hK
            (cmp116SetWeakeningList sigma (d :: tail) 1) S row col
      rw [cmp116SetWeakeningList_cons_of_not_mem sigma d tail 1 hdTail]

/-- The source-specific covariance tree is a valid iterated FTC expansion.
Every node derivative is the already-summed physical mixed derivative, and
all recursive fibers remain inside the unit weakening cube. -/
theorem cmp116SourcePi4MixedCovarianceFTCExpansionTree_valid
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (hFresh : ∀ d ∈ L, d ∉ S)
    (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    (cmp116SourcePi4MixedCovarianceFTCExpansionTree
      (R := R) anchor K hc hmass hK sigma S L row col).Valid := by
  letI : ContinuousSMul ℝ ℂ := {
    continuous_smul := by
      simpa [Complex.real_smul] using
        (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
  }
  induction L generalizing sigma S with
  | nil =>
      simp [cmp116SourcePi4MixedCovarianceFTCExpansionTree,
        CMP116FTCExpansionTree.Valid]
  | cons d tail ih =>
      have hdTail : d ∉ tail := (List.nodup_cons.mp hL).1
      have htailNodup : tail.Nodup := (List.nodup_cons.mp hL).2
      have hdS : d ∉ S := hFresh d (by simp)
      have hFreshTail : ∀ x ∈ tail, x ∉ S := by
        intro x hx
        exact hFresh x (by simp [hx])
      let endpointSigma := cmp116SetWeakeningList sigma tail 1
      have hendpointShift :
          ∀ x, ‖endpointSigma x - 1‖ ≤ (1 : ℝ) :=
        cmp116SetWeakeningList_unitShifted sigma tail hsigma
      have hendpointCap : ∀ x, ‖endpointSigma x‖ ≤ Rweak :=
        cmp116SetWeakeningList_cap sigma tail Rweak hRweak hcap
      have hbaseValid :=
        ih (Function.update sigma d 0) S htailNodup hFreshTail
          (update_ofReal_unitShifted sigma d 0 (by simp) hsigma)
          (update_ofReal_cap sigma d 0 Rweak (by simp) hRweak hcap)
      have hbaseSum :
          (cmp116SourcePi4MixedCovarianceFTCExpansionTree
              (R := R) anchor K hc hmass hK
              (Function.update sigma d 0) S tail row col).expansionSum =
            cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
              (R := R) anchor K hc hmass hK
              (Function.update endpointSigma d 0) S row col := by
        calc
          _ = (cmp116SourcePi4MixedCovarianceFTCExpansionTree
                (R := R) anchor K hc hmass hK
                (Function.update sigma d 0) S tail row col).coupledEndpoint :=
            CMP116FTCExpansionTree.expansionSum_eq_coupledEndpoint _ hbaseValid
          _ = cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
                (R := R) anchor K hc hmass hK
                (cmp116SetWeakeningList
                  (Function.update sigma d 0) tail 1) S row col :=
            cmp116SourcePi4MixedCovarianceFTCExpansionTree_coupledEndpoint
              anchor K hc hmass hK (Function.update sigma d 0) S tail
              htailNodup row col
          _ = _ := by
            rw [cmp116SetWeakeningList_update_of_not_mem
              sigma d tail 0 1 hdTail]
      have hfiber :
          ∀ t ∈ Set.uIcc (0 : ℝ) 1,
            (cmp116SourcePi4MixedCovarianceFTCExpansionTree
              (R := R) anchor K hc hmass hK
              (Function.update sigma d (t : ℂ)) (insert d S)
              tail row col).Valid ∧
            (cmp116SourcePi4MixedCovarianceFTCExpansionTree
              (R := R) anchor K hc hmass hK
              (Function.update sigma d (t : ℂ)) (insert d S)
              tail row col).expansionSum =
              cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
                (R := R) anchor K hc hmass hK endpointSigma
                (insert d S) row col := by
        intro t ht
        have hFreshInsert : ∀ x ∈ tail, x ∉ insert d S := by
          intro x hx
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun hxd => hdTail (hxd ▸ hx), hFreshTail x hx⟩
        have hvalid :=
          ih (Function.update sigma d (t : ℂ)) (insert d S)
            htailNodup hFreshInsert
            (update_ofReal_unitShifted sigma d t ht hsigma)
            (update_ofReal_cap sigma d t Rweak ht hRweak hcap)
        refine ⟨hvalid, ?_⟩
        calc
          _ = (cmp116SourcePi4MixedCovarianceFTCExpansionTree
                (R := R) anchor K hc hmass hK
                (Function.update sigma d (t : ℂ)) (insert d S)
                tail row col).coupledEndpoint :=
            CMP116FTCExpansionTree.expansionSum_eq_coupledEndpoint _ hvalid
          _ = cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
                (R := R) anchor K hc hmass hK
                (cmp116SetWeakeningList
                  (Function.update sigma d (t : ℂ)) tail 1)
                (insert d S) row col :=
            cmp116SourcePi4MixedCovarianceFTCExpansionTree_coupledEndpoint
              anchor K hc hmass hK
              (Function.update sigma d (t : ℂ)) (insert d S) tail
              htailNodup row col
          _ = cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
                (R := R) anchor K hc hmass hK
                (Function.update endpointSigma d (t : ℂ))
                (insert d S) row col := by
            rw [cmp116SetWeakeningList_update_of_not_mem
              sigma d tail (t : ℂ) 1 hdTail]
          _ = _ := congrFun (congrFun
            (cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative_update_of_mem
              anchor K hc hmass hK endpointSigma (insert d S) d
              (Finset.mem_insert_self d S) (t : ℂ)) row) col
      have hderiv :
          ∀ t ∈ Set.uIcc (0 : ℝ) 1,
            HasDerivAt
              (fun u : ℝ =>
                cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
                  (R := R) anchor K hc hmass hK
                  (Function.update endpointSigma d (u : ℂ)) S row col)
              (cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
                (R := R) anchor K hc hmass hK endpointSigma
                (insert d S) row col) t := by
        intro t _ht
        exact
          (hasDerivAt_cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative_update
            anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
            hΔ hΔ1 endpointSigma S d hdS hRweak hendpointShift hendpointCap
            hsmall row col (t : ℂ)).comp_ofReal
      have hint :
          IntervalIntegrable
            (fun _t : ℝ =>
              cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
                (R := R) anchor K hc hmass hK endpointSigma
                (insert d S) row col)
            MeasureTheory.volume 0 1 :=
        continuous_const.intervalIntegrable 0 1
      exact ⟨hbaseValid, hbaseSum, hfiber, hderiv, hint⟩

end

end YangMills.RG
