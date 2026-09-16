/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexPhysicalWalkMatrix
import YangMills.RG.BalabanCMP116Eq214PhysicalContourDensity

/-!
# Installing the physical walk matrix as the CMP116 contour Gamma

In the source decomposition, the `sigma` weakening variables deform the
patched-walk Gamma operator, while the `tau` variables weight the localized
potential terms.  This module installs the literal complex physical walk
matrix in `CMP116Eq214PhysicalContourDensity` without changing any covariance,
precision, determinant, or potential data.

The real base Gamma is not supplied independently: it is the same finite
contour family evaluated at `sigma = 0`.  Hence `contourGamma_zero` follows
definitionally, and the correction matrices `R1` and `R3` consume the
physical random-walk matrix rather than an arbitrary matrix-valued function.
-/

namespace YangMills.RG

noncomputable section

universe u v

set_option synthInstance.maxHeartbeats 800000

namespace CMP116Eq214PhysicalContourDensity

/-- Replace the abstract Gamma fields by the literal complex physical
random-walk matrix.  The walk terms may depend on the two retained real
fields, but the weakening carrier itself is fixed by the source geometry. -/
def withComplexPhysicalWalkGamma
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ)
    (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc) :
    CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1) where
  spectatorSupport := C.spectatorSupport
  fluctuationSupport := C.fluctuationSupport
  deltaRadius := C.deltaRadius
  yRadius := C.yRadius
  referenceRoot := C.referenceRoot
  baseGamma := fun psi phi =>
    cmp116ComplexPhysicalWalkContourBaseMatrix emb active (term psi phi)
  contourGamma := fun sigma _ psi phi =>
    cmp116ComplexPhysicalWalkContourMatrix emb active (term psi phi) sigma
  baseCovariance := C.baseCovariance
  contourCovariance := C.contourCovariance
  basePrecision := C.basePrecision
  contourPrecision := C.contourPrecision
  determinantDensity := C.determinantDensity
  potential := C.potential
  bondField := C.bondField
  threshold := C.threshold
  contourGamma_zero := by
    intro psi phi
    exact cmp116ComplexPhysicalWalkContourMatrix_zero
      emb active (term psi phi)
  contourCovariance_zero := C.contourCovariance_zero
  contourPrecision_zero := C.contourPrecision_zero
  determinantDensity_zero := C.determinantDensity_zero
  determinantDensity_sq_mul_basePrecision_det :=
    C.determinantDensity_sq_mul_basePrecision_det
  potential_zero := C.potential_zero

@[simp]
theorem withComplexPhysicalWalkGamma_baseGamma
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ)
    (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withComplexPhysicalWalkGamma emb active term).baseGamma psi phi =
      cmp116ComplexPhysicalWalkContourBaseMatrix
        emb active (term psi phi) :=
  rfl

@[simp]
theorem withComplexPhysicalWalkGamma_contourGamma
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ)
    (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withComplexPhysicalWalkGamma emb active term).contourGamma
        sigma tau psi phi =
      cmp116ComplexPhysicalWalkContourMatrix
        emb active (term psi phi) sigma :=
  rfl

/-- After installation, the literal complex `R3` is the weakened physical
walk matrix minus its zero-contour base matrix. -/
theorem withComplexPhysicalWalkGamma_r3Matrix
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ)
    (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withComplexPhysicalWalkGamma emb active term).r3Matrix
        sigma tau psi phi =
      cmp116ComplexPhysicalWalkContourMatrix
          emb active (term psi phi) sigma -
        cmp116ComplexPhysicalWalkContourBaseMatrix
          emb active (term psi phi) :=
  rfl

/-- The installed `R1` is the source-prescribed covariance sandwich formed
from the same literal physical walk matrices. -/
theorem withComplexPhysicalWalkGamma_r1Matrix
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ)
    (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (C.withComplexPhysicalWalkGamma emb active term).r1Matrix
        sigma tau psi phi =
      Matrix.transpose
          (cmp116ComplexPhysicalWalkContourMatrix
            emb active (term psi phi) sigma) *
          C.contourCovariance sigma tau psi phi *
          cmp116ComplexPhysicalWalkContourMatrix
            emb active (term psi phi) sigma -
        Matrix.transpose
          (cmp116ComplexPhysicalWalkContourBaseMatrix
            emb active (term psi phi)) *
          C.baseCovariance psi phi *
          cmp116ComplexPhysicalWalkContourBaseMatrix
            emb active (term psi phi) :=
  rfl

/-- A radial physical operator estimate supplies the exact Cauchy boundary
certificate for every entry of the installed `contourGamma`.  The `tau`
variables and retained real fields remain fixed while the source-ordered
`sigma` family is traversed. -/
theorem withComplexPhysicalWalkGamma_contourGamma_entry_cauchyBoundary
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ)
    (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (radius : Fin nDelta → ℝ)
    (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (row col : CMP116PhysicalWalkCoordinate d N Nc)
    (R : ℝ)
    (hR : 1 ≤ R) (hcap : ∀ i, 1 + radius i ≤ R)
    (hsum : Summable fun walk =>
      R ^ (active walk).card • term psi phi walk) :
    CMP116Eq214CauchyBoundaryBound nDelta radius
      (fun sigma =>
        (C.withComplexPhysicalWalkGamma emb active term).contourGamma
          sigma tau psi phi row col)
      (∑' walk, R ^ (active walk).card *
        ‖cmp116ComplexPhysicalOperatorCoefficient
          (term psi phi walk) col.1 row.1 col.2 row.2‖) := by
  simpa using
    (cmp116Eq214CauchyBoundaryBound_of_complexPhysicalWalkMatrix_entry
      emb radius active (term psi phi) row col R hR hcap hsum)

/-- The literal correction entry `R3 = Gamma(sigma) - Gamma(0)` inherits the
Cauchy boundary certificate with no free base majorant: the only additional
quantity is the norm of the actual zero-contour matrix entry. -/
theorem withComplexPhysicalWalkGamma_r3Matrix_entry_cauchyBoundary
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ)
    (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (radius : Fin nDelta → ℝ)
    (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (row col : CMP116PhysicalWalkCoordinate d N Nc)
    (R : ℝ)
    (hR : 1 ≤ R) (hcap : ∀ i, 1 + radius i ≤ R)
    (hsum : Summable fun walk =>
      R ^ (active walk).card • term psi phi walk) :
    CMP116Eq214CauchyBoundaryBound nDelta radius
      (fun sigma =>
        (C.withComplexPhysicalWalkGamma emb active term).r3Matrix
          sigma tau psi phi row col)
      ((∑' walk, R ^ (active walk).card *
          ‖cmp116ComplexPhysicalOperatorCoefficient
            (term psi phi walk) col.1 row.1 col.2 row.2‖) +
        ‖cmp116ComplexPhysicalWalkContourBaseMatrix
          emb active (term psi phi) row col‖) := by
  have hgamma :=
    C.withComplexPhysicalWalkGamma_contourGamma_entry_cauchyBoundary
      emb active term radius tau psi phi row col R hR hcap hsum
  have hsub :=
    CMP116Eq214CauchyBoundaryBound.sub_const
      nDelta radius
      (fun sigma =>
        (C.withComplexPhysicalWalkGamma emb active term).contourGamma
          sigma tau psi phi row col)
      (∑' walk, R ^ (active walk).card *
        ‖cmp116ComplexPhysicalOperatorCoefficient
          (term psi phi walk) col.1 row.1 col.2 row.2‖)
      ((C.withComplexPhysicalWalkGamma emb active term).baseGamma
        psi phi row col)
      hgamma
  simpa [r3Matrix] using hsub

/-- Closed `R3` entry estimate generated entirely from the radial physical
operator family.  Both the contour value and its literal base value are
controlled by the same majorant, hence the explicit factor two. -/
theorem withComplexPhysicalWalkGamma_r3Matrix_entry_cauchyBoundary_closed
    {Δ : Type u} {ω : Type v}
    {nDelta nY d N Nc : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d N) Site Psi Phi E (Nc ^ 2 - 1))
    (emb : Fin nDelta ↪ Δ)
    (active : ω → Finset Δ)
    (term :
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (radius : Fin nDelta → ℝ)
    (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (row col : CMP116PhysicalWalkCoordinate d N Nc)
    (R : ℝ)
    (hR : 1 ≤ R) (hcap : ∀ i, 1 + radius i ≤ R)
    (hsum : Summable fun walk =>
      R ^ (active walk).card • term psi phi walk) :
    CMP116Eq214CauchyBoundaryBound nDelta radius
      (fun sigma =>
        (C.withComplexPhysicalWalkGamma emb active term).r3Matrix
          sigma tau psi phi row col)
      (2 * (∑' walk, R ^ (active walk).card *
        ‖cmp116ComplexPhysicalOperatorCoefficient
          (term psi phi walk) col.1 row.1 col.2 row.2‖)) := by
  let M : ℝ := ∑' walk, R ^ (active walk).card *
    ‖cmp116ComplexPhysicalOperatorCoefficient
      (term psi phi walk) col.1 row.1 col.2 row.2‖
  have hboundary :=
    C.withComplexPhysicalWalkGamma_r3Matrix_entry_cauchyBoundary
      emb active term radius tau psi phi row col R hR hcap hsum
  have hbase :
      ‖cmp116ComplexPhysicalWalkContourBaseMatrix
        emb active (term psi phi) row col‖ ≤ M := by
    exact norm_cmp116ComplexPhysicalWalkContourBaseMatrix_entry_le
      emb active (term psi phi) row col R hR hsum
  apply CMP116Eq214CauchyBoundaryBound.mono
    nDelta radius _ _ hboundary
  dsimp [M]
  linarith

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
