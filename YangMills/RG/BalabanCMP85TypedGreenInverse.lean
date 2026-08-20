import YangMills.RG.BalabanCMP85TypedSchurBrackets
/-!
outer inverse calculation for CMP85 (2.42).

The candidate Green operator is constructed from `G` and `C`. The next Green operator is intentionally absent: it may enter only after these two inverse laws, through uniqueness.

-/

namespace YangMills.RG

noncomputable section

variable {H K L : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]
variable [NormedAddCommGroup L] [NormedSpace ℝ L]

/-- Fine precision with the explicit source-weighted adjoint. -/
noncomputable def cmp85TypedFinePrecision
    (A : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qdag : K →L[ℝ] H)
    (b : ℝ) : H →L[ℝ] H :=
  A + b • Qdag.comp Q

/-- Next precision before inversion, using the composite projector
`Qdag (Rdag R) Q`. -/
noncomputable def cmp85TypedNextPrecision
    (A : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qdag : K →L[ℝ] H)
    (R : K →L[ℝ] L) (Rdag : L →L[ℝ] K)
    (beta : ℝ) : H →L[ℝ] H :=
  A + beta • Qdag.comp
    ((cmp85TypedStepProjector R Rdag).comp Q)

/-- Candidate right-hand side of CMP85 (2.42). -/
noncomputable def cmp85TypedGreenCandidate
    (Q : H →L[ℝ] K) (Qdag : K →L[ℝ] H)
    (G : H →L[ℝ] H) (C : K →L[ℝ] K) (b : ℝ) : H →L[ℝ] H :=
  G + b ^ 2 • G.comp (Qdag.comp (C.comp (Q.comp G)))

/-- The next precision differs from the fine precision by the literal error
`Qdag (beta P - b I) Q`. -/
theorem cmp85TypedNextPrecision_eq_fine_add_error
    (A : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qdag : K →L[ℝ] H)
    (R : K →L[ℝ] L) (Rdag : L →L[ℝ] K)
    (b beta : ℝ) :
    let P := cmp85TypedStepProjector R Rdag
    let E := beta • P - b • ContinuousLinearMap.id ℝ K
    cmp85TypedNextPrecision A Q Qdag R Rdag beta =
      cmp85TypedFinePrecision A Q Qdag b + Qdag.comp (E.comp Q) := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro x
  simp only [cmp85TypedNextPrecision,
    cmp85TypedFinePrecision, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    map_sub, map_smul]
  abel

/-- The candidate (2.42) is a right inverse of the literal next precision. -/
theorem cmp85TypedGreenCandidate_rightInverse
    (A : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qdag : K →L[ℝ] H)
    (R : K →L[ℝ] L) (Rdag : L →L[ℝ] K)
    (G : H →L[ℝ] H) (C : K →L[ℝ] K)
    (b c beta : ℝ)
    (hcoiso : R.comp Rdag = ContinuousLinearMap.id ℝ L)
    (hFine : (cmp85TypedFinePrecision A Q Qdag b).comp G =
      ContinuousLinearMap.id ℝ H)
    (hC : (cmp85TypedSchurPrecision Q Qdag R Rdag G b c).comp C =
      ContinuousLinearMap.id ℝ K)
    (hrec : beta * (b + c) = b * c) :
    (cmp85TypedNextPrecision A Q Qdag R Rdag beta).comp
        (cmp85TypedGreenCandidate Q Qdag G C b) =
      ContinuousLinearMap.id ℝ H := by
  let P := cmp85TypedStepProjector R Rdag
  let S := cmp85TypedGreenSandwich Q Qdag G
  let E := beta • P - b • ContinuousLinearMap.id ℝ K
  let Kb := cmp85TypedFinePrecision A Q Qdag b
  have hnext :
      cmp85TypedNextPrecision A Q Qdag R Rdag beta =
        Kb + Qdag.comp (E.comp Q) := by
    exact cmp85TypedNextPrecision_eq_fine_add_error
      A Q Qdag R Rdag b beta
  have hFinePoint (z : H) : Kb (G z) = z := by
    have hz := congrArg (fun T : H →L[ℝ] H => T z) hFine
    simpa only [Kb, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hz
  have hbr := cmp85Typed_rightSchurBracket_eq_zero
    Q Qdag R Rdag G C b c beta hcoiso hC hrec
  dsimp only at hbr
  apply ContinuousLinearMap.ext
  intro x
  let y : K := Q (G x)
  have hbrQ := congrArg
    (fun T : K →L[ℝ] K => Qdag (T y)) hbr
  have hcorr :
      Qdag (E y) + b ^ 2 • Qdag (C y) +
          b ^ 2 • Qdag (E (S (C y))) = 0 := by
    simpa only [E, S, P, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, map_add, map_sub, map_smul,
      map_zero, smul_smul] using hbrQ
  rw [hnext]
  simp only [cmp85TypedGreenCandidate,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, map_add, map_smul]
  rw [hFinePoint x, hFinePoint (Qdag (C y))]
  simpa only [y, S, cmp85TypedGreenSandwich,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    smul_add, add_zero, add_assoc, add_comm, add_left_comm] using
    congrArg (fun z : H => x + z) hcorr

/-- The candidate (2.42) is also a left inverse.  This consumes the opposite
inverse laws of both `G` and `C`; it is not derived from symmetry. -/
theorem cmp85TypedGreenCandidate_leftInverse
    (A : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qdag : K →L[ℝ] H)
    (R : K →L[ℝ] L) (Rdag : L →L[ℝ] K)
    (G : H →L[ℝ] H) (C : K →L[ℝ] K)
    (b c beta : ℝ)
    (hcoiso : R.comp Rdag = ContinuousLinearMap.id ℝ L)
    (hFine : G.comp (cmp85TypedFinePrecision A Q Qdag b) =
      ContinuousLinearMap.id ℝ H)
    (hC : C.comp (cmp85TypedSchurPrecision
      Q Qdag R Rdag G b c) = ContinuousLinearMap.id ℝ K)
    (hrec : beta * (b + c) = b * c) :
    (cmp85TypedGreenCandidate Q Qdag G C b).comp
        (cmp85TypedNextPrecision A Q Qdag R Rdag beta) =
      ContinuousLinearMap.id ℝ H := by
  let P := cmp85TypedStepProjector R Rdag
  let S := cmp85TypedGreenSandwich Q Qdag G
  let E := beta • P - b • ContinuousLinearMap.id ℝ K
  let Kb := cmp85TypedFinePrecision A Q Qdag b
  have hnext :
      cmp85TypedNextPrecision A Q Qdag R Rdag beta =
        Kb + Qdag.comp (E.comp Q) := by
    exact cmp85TypedNextPrecision_eq_fine_add_error
      A Q Qdag R Rdag b beta
  have hFinePoint (z : H) : G (Kb z) = z := by
    have hz := congrArg (fun T : H →L[ℝ] H => T z) hFine
    simpa only [Kb, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hz
  have hbr := cmp85Typed_leftSchurBracket_eq_zero
    Q Qdag R Rdag G C b c beta hcoiso hC hrec
  dsimp only at hbr
  apply ContinuousLinearMap.ext
  intro x
  let y : K := Q x
  have hbrG := congrArg
    (fun T : K →L[ℝ] K => G (Qdag (T y))) hbr
  have hcorr :
      G (Qdag (E y)) + b ^ 2 • G (Qdag (C y)) +
          b ^ 2 • G (Qdag (C (S (E y)))) = 0 := by
    simpa only [E, S, P, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, map_add, map_sub, map_smul,
      map_zero, smul_smul] using hbrG
  rw [hnext]
  simp only [cmp85TypedGreenCandidate,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, map_add]
  rw [hFinePoint x]
  simpa only [y, S, cmp85TypedGreenSandwich,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    smul_add, add_zero, add_assoc, add_comm, add_left_comm] using
    congrArg (fun z : H => x + z) hcorr

/-- Inverse uniqueness identifies the independently supplied next Green
operator with the internally constructed candidate.  `Gnext` is not used in
the construction of that candidate. -/
theorem cmp85TypedGreen_eq_candidate
    (A : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qdag : K →L[ℝ] H)
    (R : K →L[ℝ] L) (Rdag : L →L[ℝ] K)
    (G Gnext : H →L[ℝ] H) (C : K →L[ℝ] K)
    (b c beta : ℝ)
    (hcoiso : R.comp Rdag = ContinuousLinearMap.id ℝ L)
    (hFineRight : (cmp85TypedFinePrecision A Q Qdag b).comp G =
      ContinuousLinearMap.id ℝ H)
    (hCRight :
      (cmp85TypedSchurPrecision Q Qdag R Rdag G b c).comp C =
        ContinuousLinearMap.id ℝ K)
    (hNextLeft : Gnext.comp
      (cmp85TypedNextPrecision A Q Qdag R Rdag beta) =
        ContinuousLinearMap.id ℝ H)
    (hrec : beta * (b + c) = b * c) :
    Gnext = cmp85TypedGreenCandidate Q Qdag G C b := by
  have hCandidateRight := cmp85TypedGreenCandidate_rightInverse
    A Q Qdag R Rdag G C b c beta hcoiso hFineRight hCRight hrec
  apply ContinuousLinearMap.ext
  intro x
  have hright := congrArg
    (fun T : H →L[ℝ] H => T x) hCandidateRight
  have hleft := congrArg
    (fun T : H →L[ℝ] H =>
      T (cmp85TypedGreenCandidate Q Qdag G C b x)) hNextLeft
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hright hleft
  rw [hright] at hleft
  exact hleft

/-- Exact typed recurrence (2.41), still before substituting the printed
source normalization for `b+c`.  Its proof uses the independently derived
(2.42) candidate equality and the right averaging identity. -/
theorem cmp85Typed_averagedGreenRecurrence
    (A : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qdag : K →L[ℝ] H)
    (R : K →L[ℝ] L) (Rdag : L →L[ℝ] K)
    (G Gnext : H →L[ℝ] H) (C : K →L[ℝ] K)
    (b c beta : ℝ)
    (hcoiso : R.comp Rdag = ContinuousLinearMap.id ℝ L)
    (hFineRight : (cmp85TypedFinePrecision A Q Qdag b).comp G =
      ContinuousLinearMap.id ℝ H)
    (hCRight :
      (cmp85TypedSchurPrecision Q Qdag R Rdag G b c).comp C =
        ContinuousLinearMap.id ℝ K)
    (hNextLeft : Gnext.comp
      (cmp85TypedNextPrecision A Q Qdag R Rdag beta) =
        ContinuousLinearMap.id ℝ H)
    (hrec : beta * (b + c) = b * c) :
    R.comp (Q.comp Gnext) =
      (b + c) • R.comp (C.comp (Q.comp G)) := by
  have hGreen := cmp85TypedGreen_eq_candidate
    A Q Qdag R Rdag G Gnext C b c beta hcoiso hFineRight hCRight
      hNextLeft hrec
  have hAverage := cmp85Typed_rightAveragingIdentity
    Q Qdag R Rdag G C b c hcoiso hCRight
  rw [hGreen]
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg
    (fun T : K →L[ℝ] L => T (Q (G x))) hAverage
  simpa only [cmp85TypedGreenCandidate,
    cmp85TypedGreenSandwich, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_add, map_smul] using hx

end

end YangMills.RG
