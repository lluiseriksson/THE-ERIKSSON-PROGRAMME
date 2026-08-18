import tmp.P3ScalarRecurrence

/-!
PRE-VALIDATION SCRATCH: source present under `tmp`; no `.olean` has been
materialized and no declaration in this file has been compiler-verified.

Scratch-only noncommutative algebra gate for CMP85 (2.41)--(2.42).

The two identities below expose every relation used by the block-Gaussian
inverse calculation.  In particular, neither the next Green operator nor the
recurrence formula is accepted as an operator-valued hypothesis: the only
scalar input is `beta * (b + c) = b * c`.

This file is not compiler evidence and is not imported by the tracked tree.
-/

namespace YangMills.RG

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The right Schur bracket vanishes from a right inverse of
`b·1 - b²S + cP`, the projector law, and the source recurrence.

The displayed certificate deliberately keeps the algebra noncommutative;
only scalar images from `ℝ` commute with the operator variables. -/
theorem scratch_cmp85_rightSchurBracket_eq_zero
    (b c beta : ℝ) (P S C : A)
    (hP : P * P = P)
    (hC :
      ((algebraMap ℝ A b) - (algebraMap ℝ A b) ^ 2 * S +
          (algebraMap ℝ A c) * P) * C = 1)
    (hrec : beta * (b + c) = b * c) :
    let B := algebraMap ℝ A b
    let C0 := algebraMap ℝ A c
    let Beta := algebraMap ℝ A beta
    let E := Beta * P - B
    E + B ^ 2 * C + B ^ 2 * E * S * C = 0 := by
  let B := algebraMap ℝ A b
  let C0 := algebraMap ℝ A c
  let Beta := algebraMap ℝ A beta
  let E := Beta * P - B
  let R := (B - B ^ 2 * S + C0 * P) * C - 1
  have hR : R = 0 := by
    dsimp [R, B, C0]
    rw [hC]
    exact sub_self 1
  have hP0 : P * P - P = 0 := sub_eq_zero.mpr hP
  have hrec0 : Beta * (B + C0) - B * C0 = 0 := by
    apply sub_eq_zero.mpr
    simpa only [Beta, B, C0, map_add, map_mul] using
      congrArg (algebraMap ℝ A) hrec
  change E + B ^ 2 * C + B ^ 2 * E * S * C = 0
  calc
    E + B ^ 2 * C + B ^ 2 * E * S * C =
        B * R - Beta * P * R + Beta * C0 * (P * P - P) * C +
          (Beta * (B + C0) - B * C0) * P * C := by
            dsimp [E, R, B, C0, Beta]
            noncomm_ring [Algebra.commutes]
    _ = 0 := by rw [hR, hP0, hrec0]; noncomm_ring

/-- Left-handed companion of `scratch_cmp85_rightSchurBracket_eq_zero`.
It is kept separate so that the eventual physical producer must supply both
inverse laws rather than infer one from an unrecorded symmetry argument. -/
theorem scratch_cmp85_leftSchurBracket_eq_zero
    (b c beta : ℝ) (P S C : A)
    (hP : P * P = P)
    (hC :
      C * ((algebraMap ℝ A b) - (algebraMap ℝ A b) ^ 2 * S +
          (algebraMap ℝ A c) * P) = 1)
    (hrec : beta * (b + c) = b * c) :
    let B := algebraMap ℝ A b
    let C0 := algebraMap ℝ A c
    let Beta := algebraMap ℝ A beta
    let E := Beta * P - B
    E + B ^ 2 * C + B ^ 2 * C * S * E = 0 := by
  let B := algebraMap ℝ A b
  let C0 := algebraMap ℝ A c
  let Beta := algebraMap ℝ A beta
  let E := Beta * P - B
  let R := C * (B - B ^ 2 * S + C0 * P) - 1
  have hR : R = 0 := by
    dsimp [R, B, C0]
    rw [hC]
    exact sub_self 1
  have hP0 : P * P - P = 0 := sub_eq_zero.mpr hP
  have hrec0 : Beta * (B + C0) - B * C0 = 0 := by
    apply sub_eq_zero.mpr
    simpa only [Beta, B, C0, map_add, map_mul] using
      congrArg (algebraMap ℝ A) hrec
  change E + B ^ 2 * C + B ^ 2 * C * S * E = 0
  calc
    E + B ^ 2 * C + B ^ 2 * C * S * E =
        B * R - Beta * R * P + Beta * C0 * C * (P * P - P) +
          (Beta * (B + C0) - B * C0) * C * P := by
            dsimp [E, R, B, C0, Beta]
            noncomm_ring [Algebra.commutes]
    _ = 0 := by rw [hR, hP0, hrec0]; noncomm_ring

end

end YangMills.RG
