import YangMills.RG.BalabanCMP89Eq246FinePointSourceFibreGreen
import YangMills.RG.BalabanCMP89Eq251SignedContourPhase

/-!
# PRE-VALIDATION: directed endpoint phase below CMP89 (2.46)

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.

This module records the algebraic gate needed after the finite diagonal
solution estimate.  The target synthesis phase must be combined with the
literal fine-point-source phase before taking norms.  On the signed contour
selected by `targetEndpoint - sourceEndpoint`, their product has the exact
relative-endpoint decay.  No separate absolute endpoint bounds are used.

This is phase algebra only.  It does not yet transport the directed source
envelope through the rank-one solution, deform the contour, construct the
continuous Green certificate, or attain window 15.
-/

namespace YangMills.RG

noncomputable section

/-- The signed pairing used before the final endpoint cancellation.  It is
kept separate from the `ell^1` norm because the rank-one branch mixes alias
indices: only the common imaginary momentum, not a same-alias product,
passes through that branch. -/
def cmp89Eq246SignedEndpointPairing {d : ℕ}
    (displacement endpoint : Fin d → ℝ) : ℝ :=
  ∑ mu, (SignType.sign (displacement mu) : ℝ) * endpoint mu

/-- Every reciprocal alias of the literal point source has the same exact
directed growth on a signed contour. -/
theorem norm_cmp89Eq246FinePointSourceAliasVector_signedContour
    {d L j : ℕ} (rho : ℝ) (p : Fin d → ℝ)
    (displacement sourceEndpoint : Fin d → ℝ)
    (m : CMP89Eq246AliasIndex d L j) :
    ‖cmp89Eq246FinePointSourceAliasVector d L j
        (cmp89Eq251SignedContourMomentum rho p displacement)
        sourceEndpoint m‖ =
      Real.exp (rho *
        cmp89Eq246SignedEndpointPairing displacement sourceEndpoint) := by
  have hnegI (w : ℂ) : (-Complex.I * w).re = w.im := by
    simp [Complex.mul_re]
  rw [cmp89Eq246FinePointSourceAliasVector, Complex.norm_exp, hnegI,
    cmp89Eq251EntireAliasPhase_im]
  congr 1
  rw [cmp89Eq246SignedEndpointPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  rw [cmp89Eq251SignedContourMomentum_im]
  ring

/-- Every target synthesis phase has the matching exact directed decay,
again independently of its reciprocal alias. -/
theorem norm_cmp89Eq246TargetPhase_signedContour
    {d L j : ℕ} (rho : ℝ) (p : Fin d → ℝ)
    (displacement targetEndpoint : Fin d → ℝ)
    (m : CMP89Eq246AliasIndex d L j) :
    ‖Complex.exp
        (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum
            (cmp89Eq251SignedContourMomentum rho p displacement) m.1)
          targetEndpoint)‖ =
      Real.exp (-(rho *
        cmp89Eq246SignedEndpointPairing displacement targetEndpoint)) := by
  rw [norm_exp_I_cmp89Eq251EntireAliasPhase]
  congr 2
  rw [cmp89Eq246SignedEndpointPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  rw [cmp89Eq251SignedContourMomentum_im]
  ring

/-- With `displacement = target - source`, the two common directed scalar
budgets recombine to the literal relative-endpoint `ell^1` decay. -/
theorem cmp89Eq246_targetDecay_mul_sourceGrowth
    {d : ℕ} (rho : ℝ) (targetEndpoint sourceEndpoint : Fin d → ℝ) :
    Real.exp (-(rho * cmp89Eq246SignedEndpointPairing
          (fun mu => targetEndpoint mu - sourceEndpoint mu) targetEndpoint)) *
        Real.exp (rho * cmp89Eq246SignedEndpointPairing
          (fun mu => targetEndpoint mu - sourceEndpoint mu) sourceEndpoint) =
      Real.exp (-(rho * cmp89Eq251DisplacementL1
        (fun mu => targetEndpoint mu - sourceEndpoint mu))) := by
  have hsum :
      (∑ mu, (SignType.sign
          (targetEndpoint mu - sourceEndpoint mu) : ℝ) * targetEndpoint mu) -
        (∑ mu, (SignType.sign
          (targetEndpoint mu - sourceEndpoint mu) : ℝ) * sourceEndpoint mu) =
      ∑ mu, |targetEndpoint mu - sourceEndpoint mu| := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro mu _
    rw [← sign_mul_self (targetEndpoint mu - sourceEndpoint mu)]
    ring
  rw [← Real.exp_add]
  congr 1
  rw [cmp89Eq246SignedEndpointPairing, cmp89Eq246SignedEndpointPairing,
    cmp89Eq251DisplacementL1]
  calc
    -(rho * ∑ mu, (SignType.sign
          (targetEndpoint mu - sourceEndpoint mu) : ℝ) * targetEndpoint mu) +
        rho * ∑ mu, (SignType.sign
          (targetEndpoint mu - sourceEndpoint mu) : ℝ) * sourceEndpoint mu =
      -(rho * ((∑ mu, (SignType.sign
          (targetEndpoint mu - sourceEndpoint mu) : ℝ) * targetEndpoint mu) -
        ∑ mu, (SignType.sign
          (targetEndpoint mu - sourceEndpoint mu) : ℝ) * sourceEndpoint mu)) := by
          ring
    _ = _ := by rw [hsum]

/-- The target synthesis phase and the literal point-source phase combine
exactly into the relative endpoint phase, before norms are taken. -/
theorem cmp89Eq246TargetPhase_mul_finePointSourceAliasVector
    {d L j : ℕ} (z : Fin d → ℂ) (m : CMP89Eq246AliasIndex d L j)
    (targetEndpoint sourceEndpoint : Fin d → ℝ) :
    Complex.exp
        (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint) *
      cmp89Eq246FinePointSourceAliasVector
        d L j z sourceEndpoint m =
    Complex.exp
      (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m.1)
        (fun mu => targetEndpoint mu - sourceEndpoint mu)) := by
  rw [cmp89Eq246FinePointSourceAliasVector, ← Complex.exp_add]
  congr 1
  simp only [cmp89Eq251EntirePhase, map_sub, Finset.sum_sub_distrib]
  ring

/-- On the signed contour chosen by the literal endpoint difference, the
combined target/source phase has exact alias-independent `ell^1` decay. -/
theorem norm_cmp89Eq246TargetPhase_mul_finePointSourceAliasVector_signedContour
    {d L j : ℕ} (rho : ℝ) (p : Fin d → ℝ)
    (m : CMP89Eq246AliasIndex d L j)
    (targetEndpoint sourceEndpoint : Fin d → ℝ) :
    ‖Complex.exp
          (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum
              (cmp89Eq251SignedContourMomentum rho p
                (fun mu => targetEndpoint mu - sourceEndpoint mu)) m.1)
            targetEndpoint) *
        cmp89Eq246FinePointSourceAliasVector d L j
          (cmp89Eq251SignedContourMomentum rho p
            (fun mu => targetEndpoint mu - sourceEndpoint mu))
          sourceEndpoint m‖ =
      Real.exp (-(rho * cmp89Eq251DisplacementL1
        (fun mu => targetEndpoint mu - sourceEndpoint mu))) := by
  rw [cmp89Eq246TargetPhase_mul_finePointSourceAliasVector]
  exact norm_exp_I_cmp89Eq251EntireAliasPhase_signedContour
    rho p (fun mu => targetEndpoint mu - sourceEndpoint mu) m.1

end

end YangMills.RG
