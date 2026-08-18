import Mathlib

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℝ A]

theorem reproRightSchurBracket
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
              hC0C, hC0Beta, hBetaP, hBetaS, hBetaC]
    _ = 0 := by rw [hR, hP0, hrec0]; noncomm_ring

theorem reproLeftSchurBracket
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
              hC0C, hC0Beta, hBetaP, hBetaS, hBetaC]
    _ = 0 := by rw [hR, hP0, hrec0]; noncomm_ring

end
