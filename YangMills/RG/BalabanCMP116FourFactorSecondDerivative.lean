import YangMills.RG.BalabanCMP116WilsonHessianDifferential

/-!
# Exact second derivative of an ordered four-factor product

This module isolates the noncommutative product rule needed by the local
Wilson-plaquette calculation at an arbitrary background.  It does not assume
that the four matrix curves commute.

For factor values `Wᵢ`, first variations `Xᵢ`, and second variations `Yᵢ`,
the second variation contains four diagonal terms and the six ordered
cross-pairs, each with multiplicity two.  Keeping this formula independent of
the lattice dictionary makes the later orientation and Lipschitz arguments
auditable separately.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

/-- The real trace as a continuous real-linear map. -/
def fourFactorTraceRealCLM :
    Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] ℝ :=
  ∑ i : Fin Nc, Complex.reCLM.comp (matrixEntryCLM i i)

@[simp]
theorem fourFactorTraceRealCLM_apply
    (A : Matrix (Fin Nc) (Fin Nc) ℂ) :
    fourFactorTraceRealCLM A = ambientTraceReal A := by
  simp only [fourFactorTraceRealCLM, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
  unfold ambientTraceReal
  apply Finset.sum_congr rfl
  intro i hi
  rw [matrixEntryCLM_apply]

/-- Ordered product of four matrix-valued curves. -/
def fourFactorProduct
    (F : Fin 4 → ℝ → Matrix (Fin Nc) (Fin Nc) ℂ) (t : ℝ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((F 0 t * F 1 t) * F 2 t) * F 3 t

/-- The exact first product-rule expression for four ordered factors. -/
def fourFactorFirst
    (F dF : Fin 4 → ℝ → Matrix (Fin Nc) (Fin Nc) ℂ) (t : ℝ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  (((dF 0 t * F 1 t + F 0 t * dF 1 t) * F 2 t +
      (F 0 t * F 1 t) * dF 2 t) * F 3 t) +
    ((F 0 t * F 1 t) * F 2 t) * dF 3 t

/-- Fully expanded second variation of an ordered four-factor product.

The six cross-pairs occur twice because either of the two differentiated
factors can be hit first.  Their matrix order remains the original order
`0,1,2,3`.
-/
def fourFactorSecond
    (W X Y : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((Y 0 * W 1) * W 2) * W 3 +
  2 • (((X 0 * X 1) * W 2) * W 3) +
  2 • (((X 0 * W 1) * X 2) * W 3) +
  2 • (((X 0 * W 1) * W 2) * X 3) +
  ((W 0 * Y 1) * W 2) * W 3 +
  2 • (((W 0 * X 1) * X 2) * W 3) +
  2 • (((W 0 * X 1) * W 2) * X 3) +
  ((W 0 * W 1) * Y 2) * W 3 +
  2 • (((W 0 * W 1) * X 2) * X 3) +
  ((W 0 * W 1) * W 2) * Y 3

/-- First derivative of an ordered four-factor product. -/
theorem hasDerivAt_fourFactorProduct
    (F dF : Fin 4 → ℝ → Matrix (Fin Nc) (Fin Nc) ℂ) (t : ℝ)
    (hF : ∀ i : Fin 4, HasDerivAt (F i) (dF i t) t) :
    HasDerivAt (fourFactorProduct F) (fourFactorFirst F dF t) t := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  have hraw := (((hF 0).mul (hF 1)).mul (hF 2)).mul (hF 3)
  exact hraw

/-- Second derivative of the ordered product, expressed using the factor
values and their first and second variations at the differentiation point. -/
theorem hasDerivAt_fourFactorFirst
    (F dF : Fin 4 → ℝ → Matrix (Fin Nc) (Fin Nc) ℂ)
    (Y : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) (t : ℝ)
    (hF : ∀ i : Fin 4, HasDerivAt (F i) (dF i t) t)
    (hdF : ∀ i : Fin 4, HasDerivAt (dF i) (Y i) t) :
    HasDerivAt (fourFactorFirst F dF)
      (fourFactorSecond (fun i => F i t) (fun i => dF i t) Y) t := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  have h01 := (hF 0).mul (hF 1)
  have hd01 := ((hdF 0).mul (hF 1)).add ((hF 0).mul (hdF 1))
  have h012 := h01.mul (hF 2)
  have hd012 := (hd01.mul (hF 2)).add (h01.mul (hdF 2))
  have hraw := (hd012.mul (hF 3)).add (h012.mul (hdF 3))
  convert hraw using 1
  simp only [fourFactorSecond, two_smul, Pi.mul_apply, Pi.add_apply]
  noncomm_ring

/-- Second derivative of the scalar real trace of the ordered product. -/
theorem hasDerivAt_traceReal_fourFactorFirst
    (F dF : Fin 4 → ℝ → Matrix (Fin Nc) (Fin Nc) ℂ)
    (Y : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) (t : ℝ)
    (hF : ∀ i : Fin 4, HasDerivAt (F i) (dF i t) t)
    (hdF : ∀ i : Fin 4, HasDerivAt (dF i) (Y i) t) :
    HasDerivAt (fun u => ambientTraceReal (fourFactorFirst F dF u))
      (ambientTraceReal
        (fourFactorSecond (fun i => F i t) (fun i => dF i t) Y)) t := by
  have htrace :=
    (fourFactorTraceRealCLM (Nc := Nc)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_fourFactorFirst F dF Y t hF hdF)
  convert htrace using 1
  · funext u
    exact (fourFactorTraceRealCLM_apply (fourFactorFirst F dF u)).symm
  · exact (fourFactorTraceRealCLM_apply
      (fourFactorSecond (fun i => F i t) (fun i => dF i t) Y)).symm

end

end YangMills.RG
