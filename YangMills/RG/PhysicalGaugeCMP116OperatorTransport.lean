/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.LocalLinearOperator
import YangMills.RG.PhysicalGaugeCovarianceLocalization

/-!
# Physical covariance-root operators in CMP116 coordinates

This file transports a physical positive-bond operator into CMP116 fluctuation
coordinates and packages exact finite support of finite-range or explicitly
truncated root operators.

It does not construct the covariance root, prove exponential truncation,
construct local activities, or prove raw activity decay.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

/-- Coordinate projection on a finite set of physical positive bonds. -/
noncomputable def physicalBondProjection
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N)) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ =>
        WithLp.toLp 2 fun b =>
          if b ∈ S then ξ b else 0
      map_add' := fun ξ η => by
        apply PiLp.ext
        intro b
        by_cases hb : b ∈ S <;> simp [hb]
      map_smul' := fun c ξ => by
        apply PiLp.ext
        intro b
        by_cases hb : b ∈ S <;> simp [hb] }

@[simp] theorem physicalBondProjection_apply_mem
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N))
    {b : PhysicalBond d N} (hb : b ∈ S)
    (ξ : PhysicalGaugeOneCochain d N Nc) :
    physicalBondProjection S ξ b = ξ b := by
  simp [physicalBondProjection, hb]

@[simp] theorem physicalBondProjection_apply_not_mem
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N))
    {b : PhysicalBond d N} (hb : b ∉ S)
    (ξ : PhysicalGaugeOneCochain d N Nc) :
    physicalBondProjection S ξ b = 0 := by
  simp [physicalBondProjection, hb]

/-- Physical bonds assigned to a finite CMP116 cube set. -/
noncomputable def physicalBondsOver
    {dPhys N d L : ℕ} [NeZero N] [NeZero L]
    (bondToCube : PhysicalBond dPhys N → Cube d L)
    (X : Finset (Cube d L)) :
    Finset (PhysicalBond dPhys N) := by
  classical
  exact Finset.univ.filter fun b => bondToCube b ∈ X

@[simp] theorem mem_physicalBondsOver
    {dPhys N d L : ℕ} [NeZero N] [NeZero L]
    (bondToCube : PhysicalBond dPhys N → Cube d L)
    (X : Finset (Cube d L))
    (b : PhysicalBond dPhys N) :
    b ∈ physicalBondsOver bondToCube X ↔
      bondToCube b ∈ X := by
  classical
  simp [physicalBondsOver]

/-- Conjugate a physical positive-bond operator into CMP116 coordinates. -/
noncomputable def cmp116OperatorOfPhysical
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    (coordinates :
      CMP116FluctuationField d L lieDim ≃L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (T :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc) :
    CMP116FluctuationField d L lieDim →L[ℝ]
      CMP116FluctuationField d L lieDim :=
  coordinates.symm.toContinuousLinearMap.comp
    (T.comp coordinates.toContinuousLinearMap)

/-- Exact coordinate/support transport for a physical covariance-root operator.

`root_kernel_bound_transport` is deliberately a field: converting the physical
single-bond estimate to a cube-vector estimate requires the concrete coordinate
dictionary and its finite block norm constants. -/
structure PhysicalRootToCMP116OperatorTransport
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ) where
  bondToCube :
    PhysicalBond dPhys N → Cube d L
  coordinates :
    CMP116FluctuationField d L lieDim ≃L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc
  support_projection :
    ∀ X : Finset (Cube d L),
      coordinates.toContinuousLinearMap.comp
          (cmp116FieldProjection (lieDim := lieDim) X) =
        (physicalBondProjection
          (physicalBondsOver bondToCube X)).comp
            coordinates.toContinuousLinearMap
  cmpWeight :
    Cube d L → Cube d L → ℝ
  root_kernel_bound_transport :
    PhysicalCovarianceKernelBound root rootWeight →
      CMP116LinearMapKernelBound
        (cmp116OperatorOfPhysical coordinates root)
        cmpWeight

namespace PhysicalRootToCMP116OperatorTransport

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
variable
  {root :
    PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc}
variable
  {rootWeight :
    PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}

/-- The certified physical root written as a CMP116 endomorphism. -/
noncomputable def rootOperator
    (A :
      PhysicalRootToCMP116OperatorTransport
        (d := d) (L := L) (lieDim := lieDim) root rootWeight) :
    CMP116FluctuationField d L lieDim →L[ℝ]
      CMP116FluctuationField d L lieDim :=
  cmp116OperatorOfPhysical A.coordinates root

/-- Restrict the Gaussian input coordinates to `Xin` before applying the
transported root. -/
noncomputable def localizedRootOperator
    (A :
      PhysicalRootToCMP116OperatorTransport
        (d := d) (L := L) (lieDim := lieDim) root rootWeight)
    (Xin : Finset (Cube d L)) :
    CMP116FluctuationField d L lieDim →L[ℝ]
      CMP116FluctuationField d L lieDim :=
  (rootOperator A).comp
    (cmp116FieldProjection Xin)

@[simp] theorem coordinates_rootOperator
    (A :
      PhysicalRootToCMP116OperatorTransport
        (d := d) (L := L) (lieDim := lieDim) root rootWeight)
    (ξ : CMP116FluctuationField d L lieDim) :
    A.coordinates (rootOperator A ξ) =
      root (A.coordinates ξ) := by
  change
    A.coordinates
        (A.coordinates.symm
          (root (A.coordinates ξ))) =
      root (A.coordinates ξ)
  exact A.coordinates.apply_symm_apply _

@[simp] theorem coordinates_localizedRootOperator
    (A :
      PhysicalRootToCMP116OperatorTransport
        (d := d) (L := L) (lieDim := lieDim) root rootWeight)
    (Xin : Finset (Cube d L))
    (ξ : CMP116FluctuationField d L lieDim) :
    A.coordinates (localizedRootOperator A Xin ξ) =
      root
        (A.coordinates
          (cmp116FieldProjection Xin ξ)) := by
  change
    A.coordinates
        (A.coordinates.symm
          (root
            (A.coordinates
              (cmp116FieldProjection Xin ξ)))) =
      root
        (A.coordinates
          (cmp116FieldProjection Xin ξ))
  exact A.coordinates.apply_symm_apply _

/-- The root certificate's physical kernel estimate transported to CMP116
coordinates by the supplied coordinate transport theorem. -/
theorem rootOperator_kernelBound_of_certificate
    {precision covariance :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    (hcert :
      PhysicalLocalizedCovarianceRootCertificate
        precision covariance root covNormBound rootNormBound
        covWeight rootWeight)
    (A :
      PhysicalRootToCMP116OperatorTransport
        (d := d) (L := L) (lieDim := lieDim) root rootWeight) :
    CMP116LinearMapKernelBound
      (rootOperator A) A.cmpWeight :=
  A.root_kernel_bound_transport hcert.root_kernel_bound

/-- Finite-range transported kernel bounds give exact input/output support for
the projected CMP116 root operator. -/
theorem localizedRootOperator_supportedBetween
    (A :
      PhysicalRootToCMP116OperatorTransport
        (d := d) (L := L) (lieDim := lieDim) root rootWeight)
    (hkernel :
      PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : Finset (Cube d L))
    (hfinite :
      CMP116KernelFiniteRange A.cmpWeight dist R) :
    OperatorSupportedBetween
      Xin
      (cmp116FiniteRangeClosure dist R Xin)
      (localizedRootOperator A Xin) := by
  simpa [localizedRootOperator, rootOperator] using
    OperatorSupportedBetween.of_kernel_bound_finiteRange
      (A.root_kernel_bound_transport hkernel)
      hfinite

/-- Agreement on `Xin` is enough before any output finite-range theorem is
available, because input projection is part of the definition. -/
theorem localizedRootOperator_eq_of_agreeOn
    (A :
      PhysicalRootToCMP116OperatorTransport
        (d := d) (L := L) (lieDim := lieDim) root rootWeight)
    (Xin : Finset (Cube d L))
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn Xin ξ η) :
    localizedRootOperator A Xin ξ =
      localizedRootOperator A Xin η := by
  simp only [localizedRootOperator, ContinuousLinearMap.comp_apply]
  rw [cmp116FieldProjection_eq_of_agreeOn hξη]

/-- Pointwise zero output outside the finite-range closure. -/
theorem localizedRootOperator_apply_eq_zero_outside
    (A :
      PhysicalRootToCMP116OperatorTransport
        (d := d) (L := L) (lieDim := lieDim) root rootWeight)
    (hkernel :
      PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : Finset (Cube d L))
    (hfinite :
      CMP116KernelFiniteRange A.cmpWeight dist R)
    (ξ : CMP116FluctuationField d L lieDim)
    {q : Cube d L}
    (hq : q ∉ cmp116FiniteRangeClosure dist R Xin)
    (a : Fin lieDim) :
    localizedRootOperator A Xin ξ q a = 0 :=
  OperatorSupportedBetween.apply_eq_zero_outside
    (localizedRootOperator_supportedBetween
      A hkernel dist R Xin hfinite)
    ξ hq a

noncomputable def localizedRootLinearMap
    (A :
      PhysicalRootToCMP116OperatorTransport
        (d := d) (L := L) (lieDim := lieDim) root rootWeight)
    (hkernel :
      PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : Finset (Cube d L))
    (hfinite :
      CMP116KernelFiniteRange A.cmpWeight dist R) :
    CMP116LocalizedLinearMap
      (lieDim := lieDim)
      Xin
      (cmp116FiniteRangeClosure dist R Xin) where
  toContinuousLinearMap :=
    localizedRootOperator A Xin
  supportedBetween :=
    localizedRootOperator_supportedBetween
      A hkernel dist R Xin hfinite

end PhysicalRootToCMP116OperatorTransport

end YangMills.RG
