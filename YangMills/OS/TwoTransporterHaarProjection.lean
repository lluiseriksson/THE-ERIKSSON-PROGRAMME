import Mathlib

/-!
# Haar projection for two free transporters

This module is independent of the frozen SU(2) Wilson-reflection lane.  It
isolates the measure-theoretic no-go used by
`docs/SU2-TWO-TRANSPORTER-NOGO-20260731.md`.

Only left invariance of the probability measure is consumed.  The weight
hypothesis is pointwise algebra: `w (a * z⁻¹ * a⁻¹) = w z`.  For the reduced
SU(2) Wilson weight it follows from conjugation invariance of trace and
`Re (tr z⁻¹) = Re (tr z)`.
-/

open MeasureTheory

namespace YangMills.OS.TwoTransporterHaarProjection

variable {G : Type*} [MeasurableSpace G] [Group G] [MeasurableMul G]

/-- Pointwise symmetry needed by the left-Haar proof.  This is an algebraic
hypothesis on the weight, not an invariance hypothesis on the measure. -/
def ConjugationInverseInvariant (w : G → ℂ) : Prop :=
  ∀ a z, w (a * z⁻¹ * a⁻¹) = w z

/-- A left translation in the freely integrated variable turns `A * c⁻¹`
into a conjugate of `z⁻¹`; the pointwise weight symmetry removes it. -/
theorem integral_weight_mul_inv_eq
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (w : G → ℂ) (hw : ConjugationInverseInvariant w) (A : G) :
    (∫ c, w (A * c⁻¹) ∂μ) = ∫ z, w z ∂μ := by
  calc
    (∫ c, w (A * c⁻¹) ∂μ) = ∫ z, w (A * (A * z)⁻¹) ∂μ :=
      (MeasureTheory.integral_mul_left_eq_self (fun c => w (A * c⁻¹)) A).symm
    _ = ∫ z, w z ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simpa [mul_assoc] using hw A z

/-- Orientation D: one freely integrated transporter already removes all
dependence on `x`, `y`, and the other transporter. -/
theorem orientationD_inner_projection
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (w : G → ℂ) (hw : ConjugationInverseInvariant w)
    (x c₁ y : G) :
    (∫ c₂, w (x * c₁ * y⁻¹ * c₂⁻¹) ∂μ) = ∫ z, w z ∂μ := by
  simpa [mul_assoc] using
    integral_weight_mul_inv_eq μ w hw (x * c₁ * y⁻¹)

/-- Orientation D: integrating both independent transporters against a
left-invariant probability measure gives the weight partition constant. -/
theorem orientationD_twoTransporter_projection
    (μ : Measure G) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (w : G → ℂ) (hw : ConjugationInverseInvariant w)
    (x y : G) :
    (∫ c₁, ∫ c₂, w (x * c₁ * y⁻¹ * c₂⁻¹) ∂μ ∂μ) =
      ∫ z, w z ∂μ := by
  simp_rw [orientationD_inner_projection μ w hw]
  simp

/-- Orientation E after the two left translations `u=x*c₁`, `v=y*c₂`:
the freely integrated kernel `w (u*v⁻¹)` is the same partition constant. -/
theorem orientationE_uv_projection
    (μ : Measure G) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (w : G → ℂ) (hw : ConjugationInverseInvariant w) :
    (∫ u, ∫ v, w (u * v⁻¹) ∂μ ∂μ) = ∫ z, w z ∂μ := by
  simp_rw [integral_weight_mul_inv_eq μ w hw]
  simp

/-- Orientation E with the two original independent transporters.  Both
changes of variables are left translations; no right-invariance instance is
used. -/
theorem orientationE_twoTransporter_projection
    (μ : Measure G) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (w : G → ℂ) (hw : ConjugationInverseInvariant w)
    (x y : G) :
    (∫ c₁, ∫ c₂, w (x * c₁ * c₂⁻¹ * y⁻¹) ∂μ ∂μ) =
      ∫ z, w z ∂μ := by
  calc
    (∫ c₁, ∫ c₂, w (x * c₁ * c₂⁻¹ * y⁻¹) ∂μ ∂μ) =
        ∫ u, ∫ c₂, w (x * (x⁻¹ * u) * c₂⁻¹ * y⁻¹) ∂μ ∂μ :=
      (MeasureTheory.integral_mul_left_eq_self
        (fun c₁ => ∫ c₂, w (x * c₁ * c₂⁻¹ * y⁻¹) ∂μ) x⁻¹).symm
    _ = ∫ u, ∫ c₂, w (u * c₂⁻¹ * y⁻¹) ∂μ ∂μ := by simp
    _ = ∫ u, ∫ v, w (u * v⁻¹) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with u
      calc
        (∫ c₂, w (u * c₂⁻¹ * y⁻¹) ∂μ) =
            ∫ v, w (u * (y⁻¹ * v)⁻¹ * y⁻¹) ∂μ :=
          (MeasureTheory.integral_mul_left_eq_self
            (fun c₂ => w (u * c₂⁻¹ * y⁻¹)) y⁻¹).symm
        _ = ∫ v, w (u * v⁻¹) ∂μ := by simp [mul_assoc]
    _ = ∫ z, w z ∂μ := orientationE_uv_projection μ w hw

/-- The four-fold quadratic form for orientation D. -/
noncomputable def quadraticD
    (μ : Measure G) (w F : G → ℂ) : ℂ :=
  ∫ x, ∫ y, ∫ c₁, ∫ c₂,
    (starRingEnd ℂ) (F x) * w (x * c₁ * y⁻¹ * c₂⁻¹) * F y
    ∂μ ∂μ ∂μ ∂μ

/-- The four-fold quadratic form for orientation E. -/
noncomputable def quadraticE
    (μ : Measure G) (w F : G → ℂ) : ℂ :=
  ∫ x, ∫ y, ∫ c₁, ∫ c₂,
    (starRingEnd ℂ) (F x) * w (x * c₁ * c₂⁻¹ * y⁻¹) * F y
    ∂μ ∂μ ∂μ ∂μ

omit [Group G] [MeasurableMul G] in
private theorem pull_constants_through_two_integrals
    (μ : Measure G) (a b : ℂ) (f : G → G → ℂ) :
    (∫ s, ∫ t, a * f s t * b ∂μ ∂μ) =
      a * (∫ s, ∫ t, f s t ∂μ ∂μ) * b := by
  calc
    (∫ s, ∫ t, a * f s t * b ∂μ ∂μ) =
        ∫ s, a * (∫ t, f s t ∂μ) * b ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with s
      calc
        (∫ t, a * f s t * b ∂μ) = (∫ t, a * f s t ∂μ) * b :=
          integral_mul_const b (fun t => a * f s t)
        _ = (a * ∫ t, f s t ∂μ) * b :=
          congrArg (fun q => q * b)
            (integral_const_mul a (fun t => f s t))
    _ = a * (∫ s, ∫ t, f s t ∂μ ∂μ) * b := by
      calc
        (∫ s, a * (∫ t, f s t ∂μ) * b ∂μ) =
            (∫ s, a * (∫ t, f s t ∂μ) ∂μ) * b :=
          integral_mul_const b (fun s => a * (∫ t, f s t ∂μ))
        _ = a * (∫ s, ∫ t, f s t ∂μ ∂μ) * b :=
          congrArg (fun q => q * b)
            (integral_const_mul a (fun s => ∫ t, f s t ∂μ))

omit [Group G] [MeasurableMul G] in
private theorem separated_quadratic_eq
    (μ : Measure G) (Z : ℂ) (F : G → ℂ) :
    (∫ x, ∫ y, (starRingEnd ℂ) (F x) * Z * F y ∂μ ∂μ) =
      Z * (starRingEnd ℂ) (∫ x, F x ∂μ) * (∫ y, F y ∂μ) := by
  calc
    (∫ x, ∫ y, (starRingEnd ℂ) (F x) * Z * F y ∂μ ∂μ) =
        ∫ x, ((starRingEnd ℂ) (F x) * Z) * (∫ y, F y ∂μ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact integral_const_mul ((starRingEnd ℂ) (F x) * Z) F
    _ = ((∫ x, (starRingEnd ℂ) (F x) ∂μ) * Z) *
          (∫ y, F y ∂μ) := by
      calc
        (∫ x, ((starRingEnd ℂ) (F x) * Z) * (∫ y, F y ∂μ) ∂μ) =
            (∫ x, (starRingEnd ℂ) (F x) * Z ∂μ) * (∫ y, F y ∂μ) :=
          integral_mul_const (∫ y, F y ∂μ)
            (fun x => (starRingEnd ℂ) (F x) * Z)
        _ = ((∫ x, (starRingEnd ℂ) (F x) ∂μ) * Z) *
              (∫ y, F y ∂μ) :=
          congrArg (fun q => q * (∫ y, F y ∂μ))
            (integral_mul_const Z (fun x => (starRingEnd ℂ) (F x)))
    _ = Z * (starRingEnd ℂ) (∫ x, F x ∂μ) * (∫ y, F y ∂μ) := by
      rw [show (∫ x, (starRingEnd ℂ) (F x) ∂μ) =
        (starRingEnd ℂ) (∫ x, F x ∂μ) from integral_conj]
      ring

/-- Full orientation-D no-go: two free transporters absent from `F` project
the quadratic form to the Haar mean of `F`. -/
theorem quadraticD_eq_partition_mul_mean_sq
    (μ : Measure G) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (w : G → ℂ) (hw : ConjugationInverseInvariant w) (F : G → ℂ) :
    quadraticD μ w F =
      (∫ z, w z ∂μ) * (starRingEnd ℂ) (∫ x, F x ∂μ) * (∫ y, F y ∂μ) := by
  unfold quadraticD
  have htransport (x y : G) :
      (∫ c₁, ∫ c₂,
          (starRingEnd ℂ) (F x) * w (x * c₁ * y⁻¹ * c₂⁻¹) * F y
          ∂μ ∂μ) =
        (starRingEnd ℂ) (F x) * (∫ z, w z ∂μ) * F y := by
    rw [pull_constants_through_two_integrals]
    rw [orientationD_twoTransporter_projection μ w hw x y]
  simp_rw [htransport]
  exact separated_quadratic_eq μ (∫ z, w z ∂μ) F

/-- Full orientation-E no-go: the diagonal-regressing orientation has exactly
the same trivial-sector projection as orientation D. -/
theorem quadraticE_eq_partition_mul_mean_sq
    (μ : Measure G) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (w : G → ℂ) (hw : ConjugationInverseInvariant w) (F : G → ℂ) :
    quadraticE μ w F =
      (∫ z, w z ∂μ) * (starRingEnd ℂ) (∫ x, F x ∂μ) * (∫ y, F y ∂μ) := by
  unfold quadraticE
  have htransport (x y : G) :
      (∫ c₁, ∫ c₂,
          (starRingEnd ℂ) (F x) * w (x * c₁ * c₂⁻¹ * y⁻¹) * F y
          ∂μ ∂μ) =
        (starRingEnd ℂ) (F x) * (∫ z, w z ∂μ) * F y := by
    rw [pull_constants_through_two_integrals]
    rw [orientationE_twoTransporter_projection μ w hw x y]
  simp_rw [htransport]
  exact separated_quadratic_eq μ (∫ z, w z ∂μ) F

end YangMills.OS.TwoTransporterHaarProjection
