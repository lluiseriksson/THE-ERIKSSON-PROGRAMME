/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalBilateralShellKernel

/-!
# Explicit kernel mass of the CMP99 shell precision insertion

This file constructs the literal four-term pointwise majorant of
`K[S1,m] - K[S0,m]` for nested supports.  Its three finite-range terms are
anchored on the physical shell `D = S0 \ S1`; its mass term is diagonal on
that shell.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Majorant of a compressed finite-range kernel with output in `A` and
input in `B`.  Kernel weights use the repository convention
`weight target source`. -/
def cmp99ShellCrossKernel
    {d N : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R : ℕ) (A B : Finset (PhysicalBond d N)) (CK : ℝ)
    (target source : PhysicalBond d N) : ℝ :=
  if target ∈ A ∧ source ∈ B ∧ dist target source ≤ R then CK else 0

/-- Diagonal mass majorant on the shell. -/
def cmp99ShellDiagonalKernel
    {d N : ℕ} [NeZero N]
    (D : Finset (PhysicalBond d N)) (mass : ℝ)
    (target source : PhysicalBond d N) : ℝ :=
  if target ∈ D ∧ target = source then |mass| else 0

/-- Literal majorant corresponding term by term to the exact shell expansion
of the localized precision difference. -/
def cmp99PrecisionShellKernelMajorant
    {d N : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R : ℕ) (S1 D : Finset (PhysicalBond d N))
    (CK mass : ℝ) (target source : PhysicalBond d N) : ℝ :=
  cmp99ShellCrossKernel dist R S1 D CK target source +
    cmp99ShellCrossKernel dist R D S1 CK target source +
    cmp99ShellCrossKernel dist R D D CK target source +
    cmp99ShellDiagonalKernel D mass target source

theorem physicalCovarianceKernelBound_neg_weight
    {d N Nc : ℕ} [NeZero N]
    (A : PhysicalEndomorphism d N Nc)
    (M : PhysicalBond d N → PhysicalBond d N → ℝ)
    (hA : PhysicalCovarianceKernelBound A M) :
    PhysicalCovarianceKernelBound (-A) M := by
  intro source target v
  change ‖-(A (singlePhysicalBondCochain source v)) target‖ ≤
    M target source * ‖v‖
  rw [norm_neg]
  exact hA source target v

theorem physicalCovarianceKernelBound_add_weight
    {d N Nc : ℕ} [NeZero N]
    (A B : PhysicalEndomorphism d N Nc)
    (MA MB : PhysicalBond d N → PhysicalBond d N → ℝ)
    (hA : PhysicalCovarianceKernelBound A MA)
    (hB : PhysicalCovarianceKernelBound B MB) :
    PhysicalCovarianceKernelBound (A + B)
      (fun target source => MA target source + MB target source) := by
  intro source target v
  calc
    ‖(A + B) (singlePhysicalBondCochain source v) target‖
        ≤ ‖A (singlePhysicalBondCochain source v) target‖ +
          ‖B (singlePhysicalBondCochain source v) target‖ := norm_add_le _ _
    _ ≤ MA target source * ‖v‖ + MB target source * ‖v‖ :=
      add_le_add (hA source target v) (hB source target v)
    _ = (MA target source + MB target source) * ‖v‖ := by ring

/-- Exact indicator kernel bound for a doubly compressed finite-range
operator. -/
theorem physicalCovarianceKernelBound_projection_comp_projection_shell
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R : ℕ) (A B : Finset (PhysicalBond d N)) {CK : ℝ}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hK : PhysicalCovarianceKernelBound K (fun _ _ => CK)) :
    PhysicalCovarianceKernelBound
      ((physicalBondProjection A).comp (K.comp (physicalBondProjection B)))
      (cmp99ShellCrossKernel dist R A B CK) := by
  intro source target v
  by_cases hs : source ∈ B
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      physicalBondProjection_single_mem B source v hs]
    by_cases ht : target ∈ A
    · rw [physicalBondProjection_apply_mem A ht]
      by_cases hnear : dist target source ≤ R
      · simpa [cmp99ShellCrossKernel, hs, ht, hnear] using hK source target v
      · have hfar : R < dist target source := Nat.lt_of_not_ge hnear
        rw [hrange source target v hfar, norm_zero]
        simp [cmp99ShellCrossKernel, hs, ht, hnear]
    · rw [physicalBondProjection_apply_not_mem A ht, norm_zero]
      simp [cmp99ShellCrossKernel, ht]
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      physicalBondProjection_single_not_mem B source v hs, map_zero, map_zero,
      PiLp.zero_apply, norm_zero]
    simp [cmp99ShellCrossKernel, hs]

/-- Exact diagonal indicator bound for the shell mass projection. -/
theorem physicalCovarianceKernelBound_smul_shellProjection
    {d N Nc : ℕ} [NeZero N]
    (D : Finset (PhysicalBond d N)) (mass : ℝ) :
    PhysicalCovarianceKernelBound
      (mass • (physicalBondProjection D : PhysicalEndomorphism d N Nc))
      (cmp99ShellDiagonalKernel D mass) := by
  intro source target v
  by_cases hs : source ∈ D
  · rw [ContinuousLinearMap.smul_apply,
      physicalBondProjection_single_mem D source v hs]
    by_cases hts : target = source
    · subst target
      change ‖(mass • singlePhysicalBondCochain source v) source‖ ≤ _
      simp [cmp99ShellDiagonalKernel, hs, singlePhysicalBondCochain,
        norm_smul, Real.norm_eq_abs]
    · change ‖(mass • singlePhysicalBondCochain source v) target‖ ≤ _
      simp [cmp99ShellDiagonalKernel, hts, singlePhysicalBondCochain]
  · rw [ContinuousLinearMap.smul_apply,
      physicalBondProjection_single_not_mem D source v hs, smul_zero]
    by_cases ht : target ∈ D
    · by_cases hts : target = source
      · subst target
        exact (hs ht).elim
      · simp [cmp99ShellDiagonalKernel, ht, hts]
    · simp [cmp99ShellDiagonalKernel, ht]

/-- Kernel bound for the right-associated four-term shell expansion. -/
theorem cmp99PrecisionShellExpansion_kernelBound
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (S1 D : Finset (PhysicalBond d N))
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R : ℕ) {CK : ℝ}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hK : PhysicalCovarianceKernelBound K (fun _ _ => CK))
    (mass : ℝ) :
    PhysicalCovarianceKernelBound
      (-((physicalBondProjection S1).comp
          (K.comp (physicalBondProjection D))) -
        ((physicalBondProjection D).comp
          (K.comp (physicalBondProjection S1))) -
        ((physicalBondProjection D).comp
          (K.comp (physicalBondProjection D))) +
        mass • physicalBondProjection D)
      (cmp99PrecisionShellKernelMajorant dist R S1 D CK mass) := by
  have h1 := physicalCovarianceKernelBound_neg_weight
    ((physicalBondProjection S1).comp (K.comp (physicalBondProjection D)))
    (cmp99ShellCrossKernel dist R S1 D CK)
    (physicalCovarianceKernelBound_projection_comp_projection_shell
      K dist R S1 D hrange hK)
  have h2 := physicalCovarianceKernelBound_neg_weight
    ((physicalBondProjection D).comp (K.comp (physicalBondProjection S1)))
    (cmp99ShellCrossKernel dist R D S1 CK)
    (physicalCovarianceKernelBound_projection_comp_projection_shell
      K dist R D S1 hrange hK)
  have h3 := physicalCovarianceKernelBound_neg_weight
    ((physicalBondProjection D).comp (K.comp (physicalBondProjection D)))
    (cmp99ShellCrossKernel dist R D D CK)
    (physicalCovarianceKernelBound_projection_comp_projection_shell
      K dist R D D hrange hK)
  have hm := physicalCovarianceKernelBound_smul_shellProjection
    (Nc := Nc) D mass
  have h12 := physicalCovarianceKernelBound_add_weight _ _ _ _ h1 h2
  have h123 := physicalCovarianceKernelBound_add_weight _ _ _ _ h12 h3
  have hall := physicalCovarianceKernelBound_add_weight _ _ _ _ h123 hm
  simpa only [cmp99PrecisionShellKernelMajorant, sub_eq_add_neg] using hall

/-- The exact localized precision difference has the literal four-term shell
majorant. -/
theorem cmp99LocalizedPhysicalPrecision_sub_kernelBound_shellMajorant
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    {S1 S0 : Finset (PhysicalBond d N)} (hsub : S1 ⊆ S0)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R : ℕ) {CK : ℝ}
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hK : PhysicalCovarianceKernelBound K (fun _ _ => CK))
    (mass : ℝ) :
    PhysicalCovarianceKernelBound
      (cmp99LocalizedPhysicalPrecision K S1 mass -
        cmp99LocalizedPhysicalPrecision K S0 mass)
      (cmp99PrecisionShellKernelMajorant dist R S1 (S0 \ S1) CK mass) := by
  let D := S0 \ S1
  let E : PhysicalEndomorphism d N Nc :=
    -((physicalBondProjection S1).comp
        (K.comp (physicalBondProjection D))) -
      ((physicalBondProjection D).comp
        (K.comp (physicalBondProjection S1))) -
      ((physicalBondProjection D).comp
        (K.comp (physicalBondProjection D))) +
      mass • physicalBondProjection D
  have hE : PhysicalCovarianceKernelBound E
      (cmp99PrecisionShellKernelMajorant dist R S1 D CK mass) := by
    dsimp [E]
    simpa only [sub_eq_add_neg] using
      (cmp99PrecisionShellExpansion_kernelBound
        K S1 D dist R hrange hK mass)
  intro source target v
  have hOp :
      cmp99LocalizedPhysicalPrecision K S1 mass -
        cmp99LocalizedPhysicalPrecision K S0 mass = E := by
    dsimp [E, D]
    exact cmp99LocalizedPhysicalPrecision_sub_eq_shellExpansion K hsub mass
  rw [hOp]
  exact hE source target v

/-- A cross-kernel term whose source lies in `B` has total mass controlled by
the shell cardinality times a uniform finite-range ball count.  The estimate
is independent of the ambient volume. -/
theorem sum_cmp99ShellCrossKernel_le_right
    {d N : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R : ℕ) (T A B : Finset (PhysicalBond d N))
    {CK NR : ℝ} (hCK : 0 ≤ CK) (hNR : 0 ≤ NR)
    (hball : ∀ source : PhysicalBond d N,
      (((Finset.univ.filter fun target => dist target source ≤ R).card : ℕ) : ℝ) ≤ NR) :
    ∑ target ∈ T, ∑ source ∈ T,
        cmp99ShellCrossKernel dist R A B CK target source ≤
      CK * NR * B.card := by
  classical
  rw [Finset.sum_comm]
  calc
    ∑ source ∈ T, ∑ target ∈ T,
        cmp99ShellCrossKernel dist R A B CK target source ≤
        ∑ source ∈ T, if source ∈ B then CK * NR else 0 := by
      apply Finset.sum_le_sum
      intro source hsourceT
      by_cases hsourceB : source ∈ B
      · rw [if_pos hsourceB]
        have hsum :
            (∑ target ∈ T,
                cmp99ShellCrossKernel dist R A B CK target source) =
              ((T.filter fun target =>
                target ∈ A ∧ dist target source ≤ R).card : ℝ) * CK := by
          simp only [cmp99ShellCrossKernel, hsourceB]
          rw [← Finset.sum_filter]
          simp
        rw [hsum]
        have hsubset :
            T.filter (fun target => target ∈ A ∧ dist target source ≤ R) ⊆
              Finset.univ.filter (fun target => dist target source ≤ R) := by
          intro target htarget
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ target, ?_⟩
          exact (Finset.mem_filter.mp htarget).2.2
        have hcardNat := Finset.card_le_card hsubset
        have hcard :
            ((T.filter fun target =>
                target ∈ A ∧ dist target source ≤ R).card : ℝ) ≤ NR := by
          exact le_trans (by exact_mod_cast hcardNat) (hball source)
        nlinarith
      · simp [cmp99ShellCrossKernel, hsourceB]
    _ = ((T.filter fun source => source ∈ B).card : ℝ) * (CK * NR) := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (B.card : ℝ) * (CK * NR) := by
      apply mul_le_mul_of_nonneg_right
      · have hsubset : T.filter (fun source => source ∈ B) ⊆ B := by
          intro source hsource
          exact (Finset.mem_filter.mp hsource).2
        exact_mod_cast Finset.card_le_card hsubset
      · exact mul_nonneg hCK hNR
    _ = CK * NR * B.card := by ring

/-- Transposed form of the preceding estimate.  Symmetry of the physical
distance lets the target shell, rather than the source shell, carry the
volume-independent cardinality factor. -/
theorem sum_cmp99ShellCrossKernel_le_left
    {d N : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R : ℕ) (T A B : Finset (PhysicalBond d N))
    {CK NR : ℝ} (hCK : 0 ≤ CK) (hNR : 0 ≤ NR)
    (hsymm : ∀ target source, dist target source = dist source target)
    (hball : ∀ source : PhysicalBond d N,
      (((Finset.univ.filter fun target => dist target source ≤ R).card : ℕ) : ℝ) ≤ NR) :
    ∑ target ∈ T, ∑ source ∈ T,
        cmp99ShellCrossKernel dist R A B CK target source ≤
      CK * NR * A.card := by
  classical
  calc
    ∑ target ∈ T, ∑ source ∈ T,
        cmp99ShellCrossKernel dist R A B CK target source =
        ∑ target ∈ T, ∑ source ∈ T,
          cmp99ShellCrossKernel dist R B A CK source target := by
      apply Finset.sum_congr rfl
      intro target htarget
      apply Finset.sum_congr rfl
      intro source hsource
      simp only [cmp99ShellCrossKernel]
      rw [hsymm target source]
      simp only [and_assoc, and_left_comm, and_comm]
    _ = ∑ source ∈ T, ∑ target ∈ T,
          cmp99ShellCrossKernel dist R B A CK source target := by
      rw [Finset.sum_comm]
    _ ≤ CK * NR * A.card :=
      sum_cmp99ShellCrossKernel_le_right
        dist R T B A hCK hNR hball

/-- The diagonal shell mass contributes exactly one possible source for each
target shell bond, hence at most `|mass| * |D|` to any restricted double
sum. -/
theorem sum_cmp99ShellDiagonalKernel_le
    {d N : ℕ} [NeZero N]
    (T D : Finset (PhysicalBond d N)) (mass : ℝ) :
    ∑ target ∈ T, ∑ source ∈ T,
        cmp99ShellDiagonalKernel D mass target source ≤
      |mass| * D.card := by
  classical
  have hdiag : ∀ target ∈ T,
      (∑ source ∈ T,
        cmp99ShellDiagonalKernel D mass target source) =
        if target ∈ D then |mass| else 0 := by
    intro target htarget
    by_cases htargetD : target ∈ D
    · simp [cmp99ShellDiagonalKernel, htargetD, htarget]
    · simp [cmp99ShellDiagonalKernel, htargetD]
  calc
    ∑ target ∈ T, ∑ source ∈ T,
        cmp99ShellDiagonalKernel D mass target source =
        ∑ target ∈ T, if target ∈ D then |mass| else 0 := by
      apply Finset.sum_congr rfl
      exact hdiag
    _ = ((T.filter fun target => target ∈ D).card : ℝ) * |mass| := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (D.card : ℝ) * |mass| := by
      apply mul_le_mul_of_nonneg_right
      · have hsubset : T.filter (fun target => target ∈ D) ⊆ D := by
          intro target htarget
          exact (Finset.mem_filter.mp htarget).2
        exact_mod_cast Finset.card_le_card hsubset
      · positivity
    _ = |mass| * D.card := by ring

/-- The literal shell majorant is pointwise nonnegative as soon as the
finite-range kernel amplitude is nonnegative. -/
theorem cmp99PrecisionShellKernelMajorant_nonneg
    {d N : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R : ℕ) (S1 D : Finset (PhysicalBond d N))
    {CK : ℝ} (hCK : 0 ≤ CK) (mass : ℝ)
    (target source : PhysicalBond d N) :
    0 ≤ cmp99PrecisionShellKernelMajorant
      dist R S1 D CK mass target source := by
  unfold cmp99PrecisionShellKernelMajorant cmp99ShellCrossKernel
    cmp99ShellDiagonalKernel
  split_ifs <;> positivity

/-- Explicit double-mass bound for the CMP99 precision-shell insertion.
All three finite-range pieces are charged to the physical shell `D`; no
ambient-volume cardinality occurs. -/
theorem sum_cmp99PrecisionShellKernelMajorant_le
    {d N : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R : ℕ) (T S1 D : Finset (PhysicalBond d N))
    {CK NR : ℝ} (hCK : 0 ≤ CK) (hNR : 0 ≤ NR)
    (hsymm : ∀ target source, dist target source = dist source target)
    (hball : ∀ source : PhysicalBond d N,
      (((Finset.univ.filter fun target => dist target source ≤ R).card : ℕ) : ℝ) ≤ NR)
    (mass : ℝ) :
    ∑ target ∈ T, ∑ source ∈ T,
        cmp99PrecisionShellKernelMajorant
          dist R S1 D CK mass target source ≤
      (3 * CK * NR + |mass|) * D.card := by
  have h1 := sum_cmp99ShellCrossKernel_le_right
    dist R T S1 D hCK hNR hball
  have h2 := sum_cmp99ShellCrossKernel_le_left
    dist R T D S1 hCK hNR hsymm hball
  have h3 := sum_cmp99ShellCrossKernel_le_right
    dist R T D D hCK hNR hball
  have hm := sum_cmp99ShellDiagonalKernel_le T D mass
  calc
    ∑ target ∈ T, ∑ source ∈ T,
        cmp99PrecisionShellKernelMajorant
          dist R S1 D CK mass target source =
        (∑ target ∈ T, ∑ source ∈ T,
          cmp99ShellCrossKernel dist R S1 D CK target source) +
        (∑ target ∈ T, ∑ source ∈ T,
          cmp99ShellCrossKernel dist R D S1 CK target source) +
        (∑ target ∈ T, ∑ source ∈ T,
          cmp99ShellCrossKernel dist R D D CK target source) +
        (∑ target ∈ T, ∑ source ∈ T,
          cmp99ShellDiagonalKernel D mass target source) := by
      simp only [cmp99PrecisionShellKernelMajorant, Finset.sum_add_distrib]
    _ ≤ CK * NR * D.card + CK * NR * D.card +
        CK * NR * D.card + |mass| * D.card := by
      exact add_le_add (add_le_add (add_le_add h1 h2) h3) hm
    _ = (3 * CK * NR + |mass|) * D.card := by ring

/-- Source-level bilateral covariance decay with the abstract middle-kernel
majorant and its abstract double mass eliminated.  The only counting input is
the finite-range ball bound `NR`; the middle cost is explicitly proportional
to the physical shell `S0 \ S1`. -/
theorem cmp99SectionCCovarianceDifference_bilateralShellDecay_of_finiteRangeKernelBound
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    {S1 S0 : Finset (PhysicalBond d N)} (hsub : S1 ⊆ S0)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (hself : ∀ p, dist p p = 0)
    (R : ℕ) (hrange : PhysicalCovarianceFiniteRange K dist R)
    {CK NR c mass A0 A1 mu : ℝ}
    (hCK : 0 ≤ CK) (hNR : 0 ≤ NR)
    (hkernel : PhysicalCovarianceKernelBound K (fun _ _ => CK))
    (hball : ∀ source : PhysicalBond d N,
      (((Finset.univ.filter fun target => dist target source ≤ R).card : ℕ) : ℝ) ≤ NR)
    (hc : 0 < c) (hmass : 0 < mass) (hcoercive : IsCoerciveCLM K c)
    (hC0 : PhysicalCovarianceExponentialKernelBound
      (cmp99LocalizedPhysicalCovariance K S0 hc hmass hcoercive) dist A0 mu)
    (hC1 : PhysicalCovarianceExponentialKernelBound
      (cmp99LocalizedPhysicalCovariance K S1 hc hmass hcoercive) dist A1 mu)
    {source target : PhysicalBond d N} {dx dy : ℕ}
    (hx : let T := cmp99PhysicalBondThickening dist R (S0 \ S1)
      ∀ u, u ∈ T → dx ≤ dist target u)
    (hy : let T := cmp99PhysicalBondThickening dist R (S0 \ S1)
      ∀ v, v ∈ T → dy ≤ dist v source)
    (v0 : SUNLieCoord Nc) :
    ‖cmp99SectionCCovarianceDifference K S0 S1 hc hmass hcoercive
        (singlePhysicalBondCochain source v0) target‖ ≤
      A0 * A1 * ((3 * CK * NR + |mass|) * (S0 \ S1).card) *
        Real.exp (-(mu * (dx : ℝ))) *
        Real.exp (-(mu * (dy : ℝ))) * ‖v0‖ := by
  let D := S0 \ S1
  let T := cmp99PhysicalBondThickening dist R D
  let M := cmp99PrecisionShellKernelMajorant dist R S1 D CK mass
  have hDelta : PhysicalCovarianceKernelBound
      (cmp99LocalizedPhysicalPrecision K S1 mass -
        cmp99LocalizedPhysicalPrecision K S0 mass) M := by
    dsimp [M, D]
    exact cmp99LocalizedPhysicalPrecision_sub_kernelBound_shellMajorant
      K hsub dist R hrange hkernel mass
  have hM : ∀ source target, 0 ≤ M source target := by
    intro source' target'
    dsimp [M]
    exact cmp99PrecisionShellKernelMajorant_nonneg
      dist R S1 D hCK mass source' target'
  have hB :
      ∑ target' ∈ T, ∑ source' ∈ T, M target' source' ≤
        (3 * CK * NR + |mass|) * D.card := by
    dsimp [M]
    exact sum_cmp99PrecisionShellKernelMajorant_le
      dist R T S1 D hCK hNR hsymm hball mass
  dsimp [D] at hx hy ⊢
  exact cmp99SectionCCovarianceDifference_bilateralShellDecay
    K hsub dist hsymm hself R hrange hc hmass hcoercive hC0 hC1 M
    hDelta hM hB hx hy v0

end

end YangMills.RG
