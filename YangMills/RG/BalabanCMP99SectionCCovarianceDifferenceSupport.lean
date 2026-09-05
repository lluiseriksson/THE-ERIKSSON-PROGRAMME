/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SectionCCovarianceDifference
import YangMills.RG.BalabanCMP99PatchedParametrixTransitionSupport

/-!
# Exact shell support of the CMP99 covariance-difference insertion

For nested physical supports `S1 ⊆ S0`, the change is the shell
`D = S0 \ S1`.  This file constructs its literal finite-range thickening and
proves the two projection identities needed to localize a finite-range
precision insertion on either side.

The endpoint is structural: it does not assume a small covariance difference
and does not replace support by an exponential bound.  Exponential collar
smallness is to be obtained only after inserting this exact support into the
second-resolvent identity.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Closed `R`-neighbourhood of a finite set of physical bonds. -/
def cmp99PhysicalBondThickening
    {d N : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R : ℕ) (S : Finset (PhysicalBond d N)) :
    Finset (PhysicalBond d N) :=
  Finset.univ.filter fun target =>
    ∃ source ∈ S, dist target source ≤ R

theorem mem_cmp99PhysicalBondThickening_iff
    {d N : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R : ℕ) (S : Finset (PhysicalBond d N))
    (target : PhysicalBond d N) :
    target ∈ cmp99PhysicalBondThickening dist R S ↔
      ∃ source ∈ S, dist target source ≤ R := by
  simp [cmp99PhysicalBondThickening]

/-- Every shell bond belongs to its closed thickening. -/
theorem subset_cmp99PhysicalBondThickening
    {d N : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hself : ∀ source, dist source source = 0)
    (R : ℕ) (S : Finset (PhysicalBond d N)) :
    S ⊆ cmp99PhysicalBondThickening dist R S := by
  intro source hsource
  rw [mem_cmp99PhysicalBondThickening_iff]
  exact ⟨source, hsource, by simp [hself source]⟩

/-- A bond outside the thickening is farther than `R` from every shell bond. -/
theorem cmp99PhysicalBondThickening_far_of_not_mem
    {d N : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R : ℕ) (S : Finset (PhysicalBond d N))
    {target : PhysicalBond d N}
    (htarget : target ∉ cmp99PhysicalBondThickening dist R S) :
    ∀ source, source ∈ S → R < dist target source := by
  intro source hsource
  by_contra hfar
  have hle : dist target source ≤ R := Nat.le_of_not_gt hfar
  exact htarget ((mem_cmp99PhysicalBondThickening_iff
    dist R S target).2 ⟨source, hsource, hle⟩)

/-- A finite-range operator fed from `S` has output in the `R`-thickening of
`S`.  This is the right-shell projection identity `P_{S⁺} K P_S = K P_S`. -/
theorem physicalBondThickening_projection_comp_finiteRange_comp_projection
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R : ℕ) (S : Finset (PhysicalBond d N))
    (hrange : PhysicalCovarianceFiniteRange K dist R) :
    (physicalBondProjection (cmp99PhysicalBondThickening dist R S) :
        PhysicalEndomorphism d N Nc).comp
        (K.comp (physicalBondProjection S)) =
      K.comp (physicalBondProjection S) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro target
  simp only [ContinuousLinearMap.comp_apply]
  by_cases htarget : target ∈ cmp99PhysicalBondThickening dist R S
  · rw [physicalBondProjection_apply_mem _ htarget]
  · rw [physicalBondProjection_apply_not_mem _ htarget]
    exact (physicalFiniteRange_apply_eq_zero_of_supported
      K dist R hrange S (physicalBondProjection S x)
      (DFunLike.congr_fun (physicalBondProjection_comp_self S) x)
      target (cmp99PhysicalBondThickening_far_of_not_mem
        dist R S htarget)).symm

/-- A finite-range operator observed on `S` reads input only from the
`R`-thickening of `S`.  Symmetry of the bond metric converts the output-side
finite-range statement into the left-shell identity
`P_S K = P_S K P_{S⁺}`. -/
theorem physicalBondProjection_comp_finiteRange_eq_comp_thickening
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (R : ℕ) (S : Finset (PhysicalBond d N))
    (hrange : PhysicalCovarianceFiniteRange K dist R) :
    (physicalBondProjection S : PhysicalEndomorphism d N Nc).comp K =
      ((physicalBondProjection S : PhysicalEndomorphism d N Nc).comp K).comp
        (physicalBondProjection (cmp99PhysicalBondThickening dist R S)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro target
  simp only [ContinuousLinearMap.comp_apply]
  by_cases htarget : target ∈ S
  · rw [physicalBondProjection_apply_mem S htarget,
        physicalBondProjection_apply_mem S htarget]
    let T := cmp99PhysicalBondThickening dist R S
    let z := x - physicalBondProjection T x
    have hz : K z target = 0 := by
      have hdecomp :
          z = ∑ source, singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source (z source) :=
        (sum_singlePhysicalBondCochain_eq z).symm
      rw [hdecomp, map_sum, physicalCochain_sum_apply]
      apply Finset.sum_eq_zero
      intro source _
      by_cases hsource : source ∈ T
      · have hzsource : z source = 0 := by
          change x source - physicalBondProjection T x source = 0
          rw [physicalBondProjection_apply_mem T hsource, sub_self]
        have hsingle :
            singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) source (z source) = 0 := by
          apply PiLp.ext
          intro q
          simp [hzsource, singlePhysicalBondCochain]
        rw [hsingle, map_zero, PiLp.zero_apply]
      · have hfar0 : R < dist source target :=
          cmp99PhysicalBondThickening_far_of_not_mem
            dist R S hsource target htarget
        exact hrange source target (z source) (by
          rw [hsymm target source]
          exact hfar0)
    have hx : physicalBondProjection T x + z = x := by
      dsimp [z]
      module
    calc
      K x target = K (physicalBondProjection T x + z) target := by rw [hx]
      _ = K (physicalBondProjection T x) target + K z target := by
        exact congrArg (fun y : PhysicalGaugeOneCochain d N Nc => y target)
          (map_add K (physicalBondProjection T x) z)
      _ = K (physicalBondProjection T x) target := by rw [hz, add_zero]
  · rw [physicalBondProjection_apply_not_mem S htarget,
        physicalBondProjection_apply_not_mem S htarget]

/-- Coordinate projections commute. -/
theorem physicalBondProjection_comp_comm
    {d N Nc : ℕ} [NeZero N]
    (S T : Finset (PhysicalBond d N)) :
    (physicalBondProjection S : PhysicalEndomorphism d N Nc).comp
        (physicalBondProjection T) =
      (physicalBondProjection T).comp (physicalBondProjection S) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro target
  simp only [ContinuousLinearMap.comp_apply]
  by_cases hS : target ∈ S <;> by_cases hT : target ∈ T <;>
    simp [hS, hT]

/-- For nested supports, the large projection is the sum of the small
projection and the projection onto the set-theoretic shell. -/
theorem physicalBondProjection_eq_add_sdiff
    {d N Nc : ℕ} [NeZero N]
    {S1 S0 : Finset (PhysicalBond d N)} (hsub : S1 ⊆ S0) :
    (physicalBondProjection S0 : PhysicalEndomorphism d N Nc) =
      physicalBondProjection S1 + physicalBondProjection (S0 \ S1) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro target
  by_cases h1 : target ∈ S1
  · have h0 := hsub h1
    simp [h0, h1]
  · by_cases h0 : target ∈ S0
    · simp [h0, h1]
    · simp [h0, h1]

/-- Exact shell expansion of the localized precision difference.  Every
summand contains the physical shell projection on at least one side. -/
theorem cmp99LocalizedPhysicalPrecision_sub_eq_shellExpansion
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    {S1 S0 : Finset (PhysicalBond d N)} (hsub : S1 ⊆ S0)
    (mass : ℝ) :
    cmp99LocalizedPhysicalPrecision K S1 mass -
        cmp99LocalizedPhysicalPrecision K S0 mass =
      -((physicalBondProjection S1).comp
          (K.comp (physicalBondProjection (S0 \ S1)))) -
        ((physicalBondProjection (S0 \ S1)).comp
          (K.comp (physicalBondProjection S1))) -
        ((physicalBondProjection (S0 \ S1)).comp
          (K.comp (physicalBondProjection (S0 \ S1)))) +
        mass • physicalBondProjection (S0 \ S1) := by
  rw [cmp99LocalizedPhysicalPrecision_sub_eq_projectionFormula]
  have hP := physicalBondProjection_eq_add_sdiff
    (Nc := Nc) hsub
  rw [hP]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, map_add]
  module

/-- A finite-range term whose right leg is supported on `D` is unchanged by
sandwiching with the thickening projection. -/
theorem physicalBondThickening_sandwich_projection_comp_finiteRange_comp
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R : ℕ) (A D : Finset (PhysicalBond d N))
    (hself : ∀ source, dist source source = 0)
    (hrange : PhysicalCovarianceFiniteRange K dist R) :
    let T := cmp99PhysicalBondThickening dist R D
    (physicalBondProjection T : PhysicalEndomorphism d N Nc).comp
        (((physicalBondProjection A).comp
          (K.comp (physicalBondProjection D))).comp
            (physicalBondProjection T)) =
      (physicalBondProjection A).comp
        (K.comp (physicalBondProjection D)) := by
  dsimp only
  let T := cmp99PhysicalBondThickening dist R D
  have hDT : D ⊆ T := subset_cmp99PhysicalBondThickening dist hself R D
  have hPTPD :
      (physicalBondProjection T : PhysicalEndomorphism d N Nc).comp
          (physicalBondProjection D) = physicalBondProjection D :=
    physicalBondProjection_comp_of_subset hDT
  have hPDPT :
      (physicalBondProjection D : PhysicalEndomorphism d N Nc).comp
          (physicalBondProjection T) = physicalBondProjection D := by
    rw [physicalBondProjection_comp_comm]
    exact hPTPD
  have hKT :=
    physicalBondThickening_projection_comp_finiteRange_comp_projection
      K dist R D hrange
  have hcomm := physicalBondProjection_comp_comm
    (Nc := Nc) T A
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply]
  have hPDx := DFunLike.congr_fun hPDPT x
  simp only [ContinuousLinearMap.comp_apply] at hPDx
  have hKx := DFunLike.congr_fun hKT x
  simp only [ContinuousLinearMap.comp_apply] at hKx
  have hcommx := DFunLike.congr_fun hcomm
    (K (physicalBondProjection D x))
  simp only [ContinuousLinearMap.comp_apply] at hcommx
  rw [hPDx, hcommx, hKx]

/-- A finite-range term whose left leg is supported on `D` is unchanged by
sandwiching with the thickening projection. -/
theorem physicalBondThickening_sandwich_projection_comp_finiteRange_left
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (R : ℕ) (D A : Finset (PhysicalBond d N))
    (hself : ∀ source, dist source source = 0)
    (hrange : PhysicalCovarianceFiniteRange K dist R) :
    let T := cmp99PhysicalBondThickening dist R D
    (physicalBondProjection T : PhysicalEndomorphism d N Nc).comp
        (((physicalBondProjection D).comp
          (K.comp (physicalBondProjection A))).comp
            (physicalBondProjection T)) =
      (physicalBondProjection D).comp
        (K.comp (physicalBondProjection A)) := by
  dsimp only
  let T := cmp99PhysicalBondThickening dist R D
  have hDT : D ⊆ T := subset_cmp99PhysicalBondThickening dist hself R D
  have hPTPD :
      (physicalBondProjection T : PhysicalEndomorphism d N Nc).comp
          (physicalBondProjection D) = physicalBondProjection D :=
    physicalBondProjection_comp_of_subset hDT
  have hread := physicalBondProjection_comp_finiteRange_eq_comp_thickening
    K dist hsymm R D hrange
  have hcomm := physicalBondProjection_comp_comm
    (Nc := Nc) A T
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply]
  have hleft := DFunLike.congr_fun hPTPD
    (K (physicalBondProjection A (physicalBondProjection T x)))
  simp only [ContinuousLinearMap.comp_apply] at hleft
  rw [hleft]
  have hcommx := DFunLike.congr_fun hcomm x
  simp only [ContinuousLinearMap.comp_apply] at hcommx
  rw [hcommx]
  have hreadx := DFunLike.congr_fun hread (physicalBondProjection A x)
  simp only [ContinuousLinearMap.comp_apply] at hreadx
  exact hreadx.symm

/-- The shell mass term is invariant under the same sandwich. -/
theorem physicalBondThickening_sandwich_projection
    {d N Nc : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hself : ∀ source, dist source source = 0)
    (R : ℕ) (D : Finset (PhysicalBond d N)) :
    let T := cmp99PhysicalBondThickening dist R D
    (physicalBondProjection T : PhysicalEndomorphism d N Nc).comp
        ((physicalBondProjection D).comp (physicalBondProjection T)) =
      physicalBondProjection D := by
  dsimp only
  have hDT := subset_cmp99PhysicalBondThickening dist hself R D
  have hPTPD :
      (physicalBondProjection (cmp99PhysicalBondThickening dist R D) :
        PhysicalEndomorphism d N Nc).comp (physicalBondProjection D) =
        physicalBondProjection D :=
    physicalBondProjection_comp_of_subset hDT
  have hPDPT :
      (physicalBondProjection D : PhysicalEndomorphism d N Nc).comp
        (physicalBondProjection (cmp99PhysicalBondThickening dist R D)) =
        physicalBondProjection D := by
    rw [physicalBondProjection_comp_comm]
    exact hPTPD
  rw [hPDPT]
  exact hPTPD

/-- **Exact bilateral shell support.**  For nested supports, the full
localized precision difference lives on the finite-range thickening of the
physical shell `S0 \ S1`. -/
theorem cmp99LocalizedPhysicalPrecision_sub_eq_thickening_sandwich
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    {S1 S0 : Finset (PhysicalBond d N)} (hsub : S1 ⊆ S0)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (hself : ∀ source, dist source source = 0)
    (R : ℕ) (hrange : PhysicalCovarianceFiniteRange K dist R)
    (mass : ℝ) :
    let D := S0 \ S1
    let T := cmp99PhysicalBondThickening dist R D
    cmp99LocalizedPhysicalPrecision K S1 mass -
        cmp99LocalizedPhysicalPrecision K S0 mass =
      (physicalBondProjection T).comp
        ((cmp99LocalizedPhysicalPrecision K S1 mass -
          cmp99LocalizedPhysicalPrecision K S0 mass).comp
            (physicalBondProjection T)) := by
  dsimp only
  let D := S0 \ S1
  let T := cmp99PhysicalBondThickening dist R D
  let A1 : PhysicalEndomorphism d N Nc :=
    (physicalBondProjection S1).comp (K.comp (physicalBondProjection D))
  let A2 : PhysicalEndomorphism d N Nc :=
    (physicalBondProjection D).comp (K.comp (physicalBondProjection S1))
  let A3 : PhysicalEndomorphism d N Nc :=
    (physicalBondProjection D).comp (K.comp (physicalBondProjection D))
  let PD : PhysicalEndomorphism d N Nc := physicalBondProjection D
  have hExpand := cmp99LocalizedPhysicalPrecision_sub_eq_shellExpansion
    K hsub mass
  have hA1 :=
    physicalBondThickening_sandwich_projection_comp_finiteRange_comp
      K dist R S1 D hself hrange
  have hA2 :=
    physicalBondThickening_sandwich_projection_comp_finiteRange_left
      K dist hsymm R D S1 hself hrange
  have hA3 :=
    physicalBondThickening_sandwich_projection_comp_finiteRange_left
      K dist hsymm R D D hself hrange
  have hPD := physicalBondThickening_sandwich_projection
    (Nc := Nc) dist hself R D
  rw [hExpand]
  change (-A1 - A2 - A3 + mass • PD) =
    (physicalBondProjection T).comp
      ((-A1 - A2 - A3 + mass • PD).comp (physicalBondProjection T))
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, map_sub, map_add, map_neg, map_smul]
  have hA1x := DFunLike.congr_fun hA1 x
  have hA2x := DFunLike.congr_fun hA2 x
  have hA3x := DFunLike.congr_fun hA3 x
  have hPDx := DFunLike.congr_fun hPD x
  simp only [ContinuousLinearMap.comp_apply] at hA1x hA2x hA3x hPDx
  dsimp [A1, A2, A3, PD, T, D] at hA1x hA2x hA3x hPDx ⊢
  rw [hA1x, hA2x, hA3x, hPDx]

/-- The printed Section-C covariance difference with the exact shell
projections exposed inside the second-resolvent product. -/
theorem cmp99SectionCCovarianceDifference_eq_thickening_resolventProduct
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    {S1 S0 : Finset (PhysicalBond d N)} (hsub : S1 ⊆ S0)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (hself : ∀ source, dist source source = 0)
    (R : ℕ) (hrange : PhysicalCovarianceFiniteRange K dist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) :
    let D := S0 \ S1
    let T := cmp99PhysicalBondThickening dist R D
    cmp99SectionCCovarianceDifference K S0 S1 hc hmass hK =
      (cmp99LocalizedPhysicalCovariance K S0 hc hmass hK).comp
        ((physicalBondProjection T).comp
          ((cmp99LocalizedPhysicalPrecision K S1 mass -
            cmp99LocalizedPhysicalPrecision K S0 mass).comp
              ((physicalBondProjection T).comp
                (cmp99LocalizedPhysicalCovariance K S1 hc hmass hK)))) := by
  dsimp only
  rw [cmp99SectionCCovarianceDifference_eq_resolventProduct]
  have hsupp :=
    cmp99LocalizedPhysicalPrecision_sub_eq_thickening_sandwich
      K hsub dist hsymm hself R hrange mass
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply]
  have hsuppx := DFunLike.congr_fun hsupp
    (cmp99LocalizedPhysicalCovariance K S1 hc hmass hK x)
  simp only [ContinuousLinearMap.comp_apply] at hsuppx
  rw [hsuppx]


end

end YangMills.RG
