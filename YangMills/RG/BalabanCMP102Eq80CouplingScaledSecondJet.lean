/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80CouplingScaledThirdJet
import YangMills.RG.BalabanCMP116RadialTaylor

/-!
# Second jet after the physical CMP109 substitution

Equation (1.43) controls a Hessian after the literal substitution
`B ↦ g_k C B`.  This module records the exact order-two chain rule and the
resulting operator-norm cost.  The coupling factor is not hidden in a free
constant: the volume-uniform bound is

`(|g_k| * (1 + M^3))^2`.

No equation-(1.43) estimate is assumed here.  A source Hessian bound is
transported to Gaussian coordinates with this explicit quadratic cost.
-/

namespace YangMills.RG

noncomputable section

private abbrev CoupledSecondField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Exact second-jet chain rule for the physical precomposition. -/
theorem iteratedFDeriv_two_cmp102Eq80CouplingScaledPotential
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) (f : CoupledSecondField M Q Nc → ℝ)
    (hf : ContDiff ℝ 2 f) (B : CoupledSecondField M Q Nc) :
    iteratedFDeriv ℝ 2
        (cmp102Eq80CouplingScaledPotential gk f) B =
      (iteratedFDeriv ℝ 2 f
          (cmp109ConstrainedLinearFluctuation (L := M) gk B)).compContinuousLinearMap
        (fun _ =>
          cmp109ConstrainedLinearFluctuationCLM
            (M := M) (Q := Q) (Nc := Nc) gk) := by
  change iteratedFDeriv ℝ 2
      (f ∘ cmp109ConstrainedLinearFluctuationCLM
        (M := M) (Q := Q) (Nc := Nc) gk) B = _
  simpa using
    ContinuousLinearMap.iteratedFDeriv_comp_right
      (cmp109ConstrainedLinearFluctuationCLM
        (M := M) (Q := Q) (Nc := Nc) gk)
      hf B (i := 2) le_rfl

/-- Exact Hessian chain rule after evaluating the two multilinear directions.
This formulation interfaces directly with the nested-CLM Hessians used by the
literal CMP102 producer. -/
theorem cmp116FDerivHessian_cmp102Eq80CouplingScaledPotential
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) (f : CoupledSecondField M Q Nc → ℝ)
    (hf : ContDiff ℝ 2 f) (B A A' : CoupledSecondField M Q Nc) :
    cmp116FDerivHessian
        (cmp102Eq80CouplingScaledPotential gk f) B A' A =
      cmp116FDerivHessian f
        (cmp109ConstrainedLinearFluctuation (L := M) gk B)
        (cmp109ConstrainedLinearFluctuation (L := M) gk A')
        (cmp109ConstrainedLinearFluctuation (L := M) gk A) := by
  let directions : Fin 2 → CoupledSecondField M Q Nc := ![A', A]
  have h := congrArg (fun H => H directions)
    (iteratedFDeriv_two_cmp102Eq80CouplingScaledPotential gk f hf B)
  have hleft :
      (iteratedFDeriv ℝ 2
        (cmp102Eq80CouplingScaledPotential gk f) B) directions =
        cmp116FDerivHessian
          (cmp102Eq80CouplingScaledPotential gk f) B A' A := by
    rw [iteratedFDeriv_two_apply]
    rfl
  have hright :
      (iteratedFDeriv ℝ 2 f
          (cmp109ConstrainedLinearFluctuation (L := M) gk B))
          (fun i =>
            cmp109ConstrainedLinearFluctuation (L := M) gk (directions i)) =
        cmp116FDerivHessian f
          (cmp109ConstrainedLinearFluctuation (L := M) gk B)
          (cmp109ConstrainedLinearFluctuation (L := M) gk A')
          (cmp109ConstrainedLinearFluctuation (L := M) gk A) := by
    rw [iteratedFDeriv_two_apply]
    rfl
  have h' :
      (iteratedFDeriv ℝ 2
        (cmp102Eq80CouplingScaledPotential gk f) B) directions =
        (iteratedFDeriv ℝ 2 f
          (cmp109ConstrainedLinearFluctuation (L := M) gk B))
          (fun i =>
            cmp109ConstrainedLinearFluctuation (L := M) gk (directions i)) := by
    simpa [cmp109ConstrainedLinearFluctuationCLM_apply] using h
  exact hleft.symm.trans (h'.trans hright)

set_option synthInstance.maxHeartbeats 100000 in
/-- The second jet of the precomposed potential is bounded by the source
second jet times the square of the physical linear-map norm. -/
theorem norm_iteratedFDeriv_two_cmp102Eq80CouplingScaledPotential_le
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) (f : CoupledSecondField M Q Nc → ℝ)
    (hf : ContDiff ℝ 2 f) (B : CoupledSecondField M Q Nc) :
    ‖iteratedFDeriv ℝ 2
        (cmp102Eq80CouplingScaledPotential gk f) B‖ ≤
      ‖iteratedFDeriv ℝ 2 f
          (cmp109ConstrainedLinearFluctuation (L := M) gk B)‖ *
        ‖cmp109ConstrainedLinearFluctuationCLM
          (M := M) (Q := Q) (Nc := Nc) gk‖ ^ 2 := by
  rw [iteratedFDeriv_two_cmp102Eq80CouplingScaledPotential gk f hf B]
  simpa using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ 2 f
        (cmp109ConstrainedLinearFluctuation (L := M) gk B))
      (fun _ =>
        cmp109ConstrainedLinearFluctuationCLM
          (M := M) (Q := Q) (Nc := Nc) gk)

set_option synthInstance.maxHeartbeats 100000 in
/-- A source Hessian-norm estimate yields the corresponding matrix-element
estimate after the physical substitution, with no hidden constant. -/
theorem abs_cmp116FDerivHessian_cmp102Eq80CouplingScaledPotential_le_of_source
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) (f : CoupledSecondField M Q Nc → ℝ)
    (hf : ContDiff ℝ 2 f)
    (B A A' : CoupledSecondField M Q Nc)
    (sourceMajorant : ℝ)
    (hsource :
      ‖iteratedFDeriv ℝ 2 f
          (cmp109ConstrainedLinearFluctuation (L := M) gk B)‖ ≤
        sourceMajorant) :
    |cmp116FDerivHessian
        (cmp102Eq80CouplingScaledPotential gk f) B A' A| ≤
      sourceMajorant *
        ‖cmp109ConstrainedLinearFluctuationCLM
          (M := M) (Q := Q) (Nc := Nc) gk‖ ^ 2 * ‖A‖ * ‖A'‖ := by
  have hsource0 : 0 ≤ sourceMajorant :=
    (norm_nonneg
      (iteratedFDeriv ℝ 2 f
        (cmp109ConstrainedLinearFluctuation (L := M) gk B))).trans hsource
  have hscaled :
      ‖iteratedFDeriv ℝ 2
          (cmp102Eq80CouplingScaledPotential gk f) B‖ ≤
        sourceMajorant *
          ‖cmp109ConstrainedLinearFluctuationCLM
            (M := M) (Q := Q) (Nc := Nc) gk‖ ^ 2 := by
    calc
      ‖iteratedFDeriv ℝ 2
          (cmp102Eq80CouplingScaledPotential gk f) B‖ ≤
        ‖iteratedFDeriv ℝ 2 f
            (cmp109ConstrainedLinearFluctuation (L := M) gk B)‖ *
          ‖cmp109ConstrainedLinearFluctuationCLM
            (M := M) (Q := Q) (Nc := Nc) gk‖ ^ 2 :=
        norm_iteratedFDeriv_two_cmp102Eq80CouplingScaledPotential_le
          gk f hf B
      _ ≤ sourceMajorant *
          ‖cmp109ConstrainedLinearFluctuationCLM
            (M := M) (Q := Q) (Nc := Nc) gk‖ ^ 2 := by
        gcongr
  let directions : Fin 2 → CoupledSecondField M Q Nc := ![A', A]
  have heval :
      ‖(iteratedFDeriv ℝ 2
          (cmp102Eq80CouplingScaledPotential gk f) B) directions‖ ≤
        ‖iteratedFDeriv ℝ 2
          (cmp102Eq80CouplingScaledPotential gk f) B‖ *
          ∏ i, ‖directions i‖ :=
    ContinuousMultilinearMap.le_opNorm _ _
  rw [Real.norm_eq_abs] at heval
  have hrewrite :
      (iteratedFDeriv ℝ 2
          (cmp102Eq80CouplingScaledPotential gk f) B) directions =
        cmp116FDerivHessian
          (cmp102Eq80CouplingScaledPotential gk f) B A' A := by
    rw [iteratedFDeriv_two_apply]
    rfl
  rw [hrewrite] at heval
  calc
    |cmp116FDerivHessian
        (cmp102Eq80CouplingScaledPotential gk f) B A' A| ≤
      ‖iteratedFDeriv ℝ 2
          (cmp102Eq80CouplingScaledPotential gk f) B‖ *
        ∏ i, ‖directions i‖ := heval
    _ ≤ (sourceMajorant *
        ‖cmp109ConstrainedLinearFluctuationCLM
          (M := M) (Q := Q) (Nc := Nc) gk‖ ^ 2) *
        ∏ i, ‖directions i‖ :=
      mul_le_mul_of_nonneg_right hscaled
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = sourceMajorant *
        ‖cmp109ConstrainedLinearFluctuationCLM
          (M := M) (Q := Q) (Nc := Nc) gk‖ ^ 2 * ‖A‖ * ‖A'‖ := by
      simp [directions]
      ring

/-- Fully explicit volume-uniform version of the order-two transport. -/
theorem abs_cmp116FDerivHessian_cmp102Eq80CouplingScaledPotential_le_explicit
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) (f : CoupledSecondField M Q Nc → ℝ)
    (hf : ContDiff ℝ 2 f)
    (B A A' : CoupledSecondField M Q Nc)
    (sourceMajorant : ℝ)
    (hsource :
      ‖iteratedFDeriv ℝ 2 f
          (cmp109ConstrainedLinearFluctuation (L := M) gk B)‖ ≤
        sourceMajorant) :
    |cmp116FDerivHessian
        (cmp102Eq80CouplingScaledPotential gk f) B A' A| ≤
      sourceMajorant * (|gk| * (1 + (M : ℝ) ^ 3)) ^ 2 * ‖A‖ * ‖A'‖ := by
  have hsource0 : 0 ≤ sourceMajorant :=
    (norm_nonneg
      (iteratedFDeriv ℝ 2 f
        (cmp109ConstrainedLinearFluctuation (L := M) gk B))).trans hsource
  calc
    |cmp116FDerivHessian
        (cmp102Eq80CouplingScaledPotential gk f) B A' A| ≤
      sourceMajorant *
          ‖cmp109ConstrainedLinearFluctuationCLM
            (M := M) (Q := Q) (Nc := Nc) gk‖ ^ 2 * ‖A‖ * ‖A'‖ :=
      abs_cmp116FDerivHessian_cmp102Eq80CouplingScaledPotential_le_of_source
        gk f hf B A A' sourceMajorant hsource
    _ ≤ sourceMajorant * (|gk| * (1 + (M : ℝ) ^ 3)) ^ 2 * ‖A‖ * ‖A'‖ := by
      gcongr
      exact norm_cmp109ConstrainedLinearFluctuationCLM_le
        (M := M) (Q := Q) (Nc := Nc) gk

set_option synthInstance.maxHeartbeats 100000 in
/-- A nested-CLM source Hessian bound transports through the literal physical
substitution.  This is the interface used by the reconstructed CMP102 domain
Hessian, and again the quadratic coupling cost is explicit. -/
theorem abs_cmp116FDerivHessian_cmp102Eq80CouplingScaledPotential_le_explicit_of_hessian
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (gk : ℝ) (f : CoupledSecondField M Q Nc → ℝ)
    (hf : ContDiff ℝ 2 f)
    (B A A' : CoupledSecondField M Q Nc)
    (sourceMajorant : ℝ)
    (hsource :
      ‖cmp116FDerivHessian f
          (cmp109ConstrainedLinearFluctuation (L := M) gk B)‖ ≤
        sourceMajorant) :
    |cmp116FDerivHessian
        (cmp102Eq80CouplingScaledPotential gk f) B A' A| ≤
      sourceMajorant * (|gk| * (1 + (M : ℝ) ^ 3)) ^ 2 * ‖A‖ * ‖A'‖ := by
  let L := cmp109ConstrainedLinearFluctuationCLM
    (M := M) (Q := Q) (Nc := Nc) gk
  let H := cmp116FDerivHessian f (L B)
  have hsource0 : 0 ≤ sourceMajorant :=
    (norm_nonneg H).trans (by simpa [H, L] using hsource)
  have hinner :
      |H (L A') (L A)| ≤ ‖H‖ * ‖L A'‖ * ‖L A‖ := by
    rw [← Real.norm_eq_abs]
    calc
      ‖H (L A') (L A)‖ ≤ ‖H (L A')‖ * ‖L A‖ :=
        (H (L A')).le_opNorm (L A)
      _ ≤ (‖H‖ * ‖L A'‖) * ‖L A‖ := by
        gcongr
        exact H.le_opNorm (L A')
  rw [cmp116FDerivHessian_cmp102Eq80CouplingScaledPotential gk f hf B A A']
  change |H (L A') (L A)| ≤ _
  calc
    |H (L A') (L A)| ≤ ‖H‖ * ‖L A'‖ * ‖L A‖ := hinner
    _ ≤ sourceMajorant * (‖L‖ * ‖A'‖) * (‖L‖ * ‖A‖) := by
      gcongr
      · simpa [H, L] using hsource
      · exact L.le_opNorm A'
      · exact L.le_opNorm A
    _ ≤ sourceMajorant * (|gk| * (1 + (M : ℝ) ^ 3)) ^ 2 * ‖A‖ * ‖A'‖ := by
      have hL := norm_cmp109ConstrainedLinearFluctuationCLM_le
        (M := M) (Q := Q) (Nc := Nc) gk
      have hL' : ‖L‖ ≤ |gk| * (1 + (M : ℝ) ^ 3) := by
        simpa [L] using hL
      have hsq : ‖L‖ ^ 2 ≤ (|gk| * (1 + (M : ℝ) ^ 3)) ^ 2 := by
        exact (sq_le_sq₀ (norm_nonneg L) (by positivity)).2 hL'
      calc
        sourceMajorant * (‖L‖ * ‖A'‖) * (‖L‖ * ‖A‖) =
            sourceMajorant * ‖L‖ ^ 2 * ‖A‖ * ‖A'‖ := by ring
        _ ≤ sourceMajorant * (|gk| * (1 + (M : ℝ) ^ 3)) ^ 2 * ‖A‖ * ‖A'‖ := by
          gcongr

end

end YangMills.RG
