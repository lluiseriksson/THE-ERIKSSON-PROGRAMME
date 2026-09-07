import tmp.P3BlockGaussianAlgebra

/-!
PRE-VALIDATION SCRATCH: source present under `tmp`; no `.olean` has been
materialized and no declaration in this file has been compiler-verified.

Scratch-only typed bridge from the abstract noncommutative certificates to
the three-space CMP85 Schur complement.

`Qdag` and `Rdag` are explicit source-weighted adjoints.  They are not
silently replaced by Lean's counting-Hilbert adjoints.  This file is not
compiler evidence and is not imported by the tracked tree.
-/

namespace YangMills.RG

noncomputable section

variable {H K L : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]
variable [NormedAddCommGroup L] [NormedSpace ℝ L]

/-- Source-oriented one-step projector on the intermediate field space. -/
noncomputable def scratch_cmp85TypedStepProjector
    (R : K →L[ℝ] L) (Rdag : L →L[ℝ] K) : K →L[ℝ] K :=
  Rdag.comp R

/-- Fine Green sandwich on the intermediate field space. -/
noncomputable def scratch_cmp85TypedGreenSandwich
    (Q : H →L[ℝ] K) (Qdag : K →L[ℝ] H)
    (G : H →L[ℝ] H) : K →L[ℝ] K :=
  Q.comp (G.comp Qdag)

/-- Literal source-oriented Schur precision
`b I - b² Q G Qdag + c Rdag R`. -/
noncomputable def scratch_cmp85TypedSchurPrecision
    (Q : H →L[ℝ] K) (Qdag : K →L[ℝ] H)
    (R : K →L[ℝ] L) (Rdag : L →L[ℝ] K)
    (G : H →L[ℝ] H) (b c : ℝ) : K →L[ℝ] K :=
  b • ContinuousLinearMap.id ℝ K -
      b ^ 2 • scratch_cmp85TypedGreenSandwich Q Qdag G +
    c • scratch_cmp85TypedStepProjector R Rdag

/-- The exact one-step coisometry makes `Rdag R` a projector. -/
theorem scratch_cmp85TypedStepProjector_idempotent
    (R : K →L[ℝ] L) (Rdag : L →L[ℝ] K)
    (hcoiso : R.comp Rdag = ContinuousLinearMap.id ℝ L) :
    (scratch_cmp85TypedStepProjector R Rdag).comp
        (scratch_cmp85TypedStepProjector R Rdag) =
      scratch_cmp85TypedStepProjector R Rdag := by
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg
    (fun T : L →L[ℝ] L => Rdag (T (R x))) hcoiso
  simpa only [scratch_cmp85TypedStepProjector,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hx

/-- The same coisometry gives the source-facing absorption `R P = R` used
in (2.41). -/
theorem scratch_cmp85TypedStepProjector_absorb_left
    (R : K →L[ℝ] L) (Rdag : L →L[ℝ] K)
    (hcoiso : R.comp Rdag = ContinuousLinearMap.id ℝ L) :
    R.comp (scratch_cmp85TypedStepProjector R Rdag) = R := by
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun T : L →L[ℝ] L => T (R x)) hcoiso
  simpa only [scratch_cmp85TypedStepProjector,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hx

/-- Right-ordered typed Schur bracket.  This is the exact intermediate-space
identity consumed by the right-inverse calculation for (2.42). -/
theorem scratch_cmp85Typed_rightSchurBracket_eq_zero
    (Q : H →L[ℝ] K) (Qdag : K →L[ℝ] H)
    (R : K →L[ℝ] L) (Rdag : L →L[ℝ] K)
    (G : H →L[ℝ] H) (C : K →L[ℝ] K)
    (b c beta : ℝ)
    (hcoiso : R.comp Rdag = ContinuousLinearMap.id ℝ L)
    (hC : (scratch_cmp85TypedSchurPrecision Q Qdag R Rdag G b c).comp C =
      ContinuousLinearMap.id ℝ K)
    (hrec : beta * (b + c) = b * c) :
    let P := scratch_cmp85TypedStepProjector R Rdag
    let S := scratch_cmp85TypedGreenSandwich Q Qdag G
    let E := beta • P - b • ContinuousLinearMap.id ℝ K
    E + b ^ 2 • C + b ^ 2 • E.comp (S.comp C) = 0 := by
  let P := scratch_cmp85TypedStepProjector R Rdag
  let S := scratch_cmp85TypedGreenSandwich Q Qdag G
  have hP : P * P = P := by
    rw [ContinuousLinearMap.mul_def]
    exact scratch_cmp85TypedStepProjector_idempotent R Rdag hcoiso
  have hC' :
      ((algebraMap ℝ (K →L[ℝ] K) b) -
          (algebraMap ℝ (K →L[ℝ] K) b) ^ 2 * S +
          (algebraMap ℝ (K →L[ℝ] K) c) * P) * C = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg (fun T : K →L[ℝ] K => T x) hC
    simpa only [P, S, scratch_cmp85TypedSchurPrecision,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.algebraMap_apply,
      pow_two, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.one_apply, one_smul, smul_smul] using hx
  have h := scratch_cmp85_rightSchurBracket_eq_zero
    (A := K →L[ℝ] K) b c beta P S C hP hC' hrec
  dsimp only at h ⊢
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun T : K →L[ℝ] K => T x) h
  simpa only [ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.algebraMap_apply, pow_two,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    one_smul, smul_smul] using hx

/-- Left-ordered typed Schur bracket.  It is deliberately independent of
the right bracket so the physical specialization must provide both inverse
laws of `C`. -/
theorem scratch_cmp85Typed_leftSchurBracket_eq_zero
    (Q : H →L[ℝ] K) (Qdag : K →L[ℝ] H)
    (R : K →L[ℝ] L) (Rdag : L →L[ℝ] K)
    (G : H →L[ℝ] H) (C : K →L[ℝ] K)
    (b c beta : ℝ)
    (hcoiso : R.comp Rdag = ContinuousLinearMap.id ℝ L)
    (hC : C.comp (scratch_cmp85TypedSchurPrecision
      Q Qdag R Rdag G b c) = ContinuousLinearMap.id ℝ K)
    (hrec : beta * (b + c) = b * c) :
    let P := scratch_cmp85TypedStepProjector R Rdag
    let S := scratch_cmp85TypedGreenSandwich Q Qdag G
    let E := beta • P - b • ContinuousLinearMap.id ℝ K
    E + b ^ 2 • C + b ^ 2 • C.comp (S.comp E) = 0 := by
  let P := scratch_cmp85TypedStepProjector R Rdag
  let S := scratch_cmp85TypedGreenSandwich Q Qdag G
  have hP : P * P = P := by
    rw [ContinuousLinearMap.mul_def]
    exact scratch_cmp85TypedStepProjector_idempotent R Rdag hcoiso
  have hC' :
      C * ((algebraMap ℝ (K →L[ℝ] K) b) -
          (algebraMap ℝ (K →L[ℝ] K) b) ^ 2 * S +
          (algebraMap ℝ (K →L[ℝ] K) c) * P) = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg (fun T : K →L[ℝ] K => T x) hC
    simpa only [P, S, scratch_cmp85TypedSchurPrecision,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.algebraMap_apply,
      pow_two, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.one_apply, one_smul, smul_smul] using hx
  have h := scratch_cmp85_leftSchurBracket_eq_zero
    (A := K →L[ℝ] K) b c beta P S C hP hC' hrec
  dsimp only at h ⊢
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun T : K →L[ℝ] K => T x) h
  simpa only [ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.algebraMap_apply, pow_two,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    one_smul, smul_smul] using hx

/-- Exact source-oriented averaging identity extracted from the right Schur
inverse.  The coefficient is visibly `b+c`; no normalization from (2.41) is
inserted here. -/
theorem scratch_cmp85Typed_rightAveragingIdentity
    (Q : H →L[ℝ] K) (Qdag : K →L[ℝ] H)
    (R : K →L[ℝ] L) (Rdag : L →L[ℝ] K)
    (G : H →L[ℝ] H) (C : K →L[ℝ] K)
    (b c : ℝ)
    (hcoiso : R.comp Rdag = ContinuousLinearMap.id ℝ L)
    (hC : (scratch_cmp85TypedSchurPrecision Q Qdag R Rdag G b c).comp C =
      ContinuousLinearMap.id ℝ K) :
    R.comp
        (ContinuousLinearMap.id ℝ K +
          b ^ 2 • (scratch_cmp85TypedGreenSandwich Q Qdag G).comp C) =
      (b + c) • R.comp C := by
  let P := scratch_cmp85TypedStepProjector R Rdag
  let S := scratch_cmp85TypedGreenSandwich Q Qdag G
  have hRP : R.comp P = R :=
    scratch_cmp85TypedStepProjector_absorb_left R Rdag hcoiso
  apply ContinuousLinearMap.ext
  intro x
  have hCx := congrArg (fun T : K →L[ℝ] K => T x) hC
  have hlinear :
      x + b ^ 2 • S (C x) = b • C x + c • P (C x) := by
    have hbase : b • C x - b ^ 2 • S (C x) + c • P (C x) = x := by
      simpa only [P, S, scratch_cmp85TypedSchurPrecision,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply] using hCx
    calc
      x + b ^ 2 • S (C x) =
          (b • C x - b ^ 2 • S (C x) + c • P (C x)) +
            b ^ 2 • S (C x) :=
        congrArg (fun y : K => y + b ^ 2 • S (C x)) hbase.symm
      _ = b • C x + c • P (C x) := by abel
  have hRlinear := congrArg R hlinear
  have hRPx : R (P (C x)) = R (C x) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : K →L[ℝ] L => T (C x)) hRP
  simp only [map_add, map_smul] at hRlinear
  rw [hRPx] at hRlinear
  simpa only [S, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_add, map_smul, add_smul] using
      hRlinear

end

end YangMills.RG
