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

private theorem scratch_cmp85_commute_assoc
    {x y : A} (hxy : x * y = y * x) (z : A) :
    x * (y * z) = y * (x * z) := by
  rw [← mul_assoc, hxy, mul_assoc]

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
  have hBP : B * P = P * B := Algebra.commutes b P
  have hBS : B * S = S * B := Algebra.commutes b S
  have hBC : B * C = C * B := Algebra.commutes b C
  have hBC0 : B * C0 = C0 * B := Algebra.commutes b C0
  have hBBeta : B * Beta = Beta * B := Algebra.commutes b Beta
  have hC0P : C0 * P = P * C0 := Algebra.commutes c P
  have hC0S : C0 * S = S * C0 := Algebra.commutes c S
  have hC0C : C0 * C = C * C0 := Algebra.commutes c C
  have hC0Beta : C0 * Beta = Beta * C0 := Algebra.commutes c Beta
  have hBetaP : Beta * P = P * Beta := Algebra.commutes beta P
  have hBetaS : Beta * S = S * Beta := Algebra.commutes beta S
  have hBetaC : Beta * C = C * Beta := Algebra.commutes beta C
  change E + B ^ 2 * C + B ^ 2 * E * S * C = 0
  calc
    E + B ^ 2 * C + B ^ 2 * E * S * C =
        B * R - Beta * P * R + Beta * C0 * (P * P - P) * C +
          (Beta * (B + C0) - B * C0) * P * C := by
            dsimp [E, R]
            noncomm_ring [hBP, hBS, hBC, hBC0, hBBeta, hC0P, hC0S,
              hC0C, hC0Beta, hBetaP, hBetaS, hBetaC,
              scratch_cmp85_commute_assoc hBP,
              scratch_cmp85_commute_assoc hBS,
              scratch_cmp85_commute_assoc hBC,
              scratch_cmp85_commute_assoc hBC0,
              scratch_cmp85_commute_assoc hBBeta,
              scratch_cmp85_commute_assoc hC0P,
              scratch_cmp85_commute_assoc hC0S,
              scratch_cmp85_commute_assoc hC0C,
              scratch_cmp85_commute_assoc hC0Beta,
              scratch_cmp85_commute_assoc hBetaP,
              scratch_cmp85_commute_assoc hBetaS,
              scratch_cmp85_commute_assoc hBetaC]
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
  have hBP : B * P = P * B := Algebra.commutes b P
  have hBS : B * S = S * B := Algebra.commutes b S
  have hBC : B * C = C * B := Algebra.commutes b C
  have hBC0 : B * C0 = C0 * B := Algebra.commutes b C0
  have hBBeta : B * Beta = Beta * B := Algebra.commutes b Beta
  have hC0P : C0 * P = P * C0 := Algebra.commutes c P
  have hC0S : C0 * S = S * C0 := Algebra.commutes c S
  have hC0C : C0 * C = C * C0 := Algebra.commutes c C
  have hC0Beta : C0 * Beta = Beta * C0 := Algebra.commutes c Beta
  have hBetaP : Beta * P = P * Beta := Algebra.commutes beta P
  have hBetaS : Beta * S = S * Beta := Algebra.commutes beta S
  have hBetaC : Beta * C = C * Beta := Algebra.commutes beta C
  change E + B ^ 2 * C + B ^ 2 * C * S * E = 0
  calc
    E + B ^ 2 * C + B ^ 2 * C * S * E =
        B * R - Beta * R * P + Beta * C0 * C * (P * P - P) +
          (Beta * (B + C0) - B * C0) * C * P := by
            dsimp [E, R]
            noncomm_ring [hBP, hBS, hBC, hBC0, hBBeta, hC0P, hC0S,
              hC0C, hC0Beta, hBetaP, hBetaS, hBetaC,
              scratch_cmp85_commute_assoc hBP,
              scratch_cmp85_commute_assoc hBS,
              scratch_cmp85_commute_assoc hBC,
              scratch_cmp85_commute_assoc hBC0,
              scratch_cmp85_commute_assoc hBBeta,
              scratch_cmp85_commute_assoc hC0P,
              scratch_cmp85_commute_assoc hC0S,
              scratch_cmp85_commute_assoc hC0C,
              scratch_cmp85_commute_assoc hC0Beta,
              scratch_cmp85_commute_assoc hBetaP,
              scratch_cmp85_commute_assoc hBetaS,
              scratch_cmp85_commute_assoc hBetaC]
    _ = 0 := by rw [hR, hP0, hrec0]; noncomm_ring

end

end YangMills.RG
