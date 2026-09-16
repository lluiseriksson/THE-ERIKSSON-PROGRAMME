import YangMills.RG.PhysicalGaugeCochains

/-!
RETRACTED PRE-VALIDATION: this algebraic covariant derivative may be useful for
CMP99 (3.39), but it is not the `nabla^eta A` printed in (3.35).  It must not be
promoted as C6c.8f0a.  No `.olean` or compiler verdict ever existed for it.

# Retracted C6c.8f0a candidate: covariant derivative of a one-cochain

CMP99 (3.39) uses the full tensor `(D^U_mu A_nu)(x)`, not the
antisymmetrized plaquette curl.  The definition below derives every `nu`
component from the already literal site-field derivative `covariantD0CLM`.
It therefore does not accept an arbitrary derivative carrying the desired
bound.
-/

namespace YangMills.RG

noncomputable section

variable {d N Nc : ℕ}
variable [NeZero d] [NeZero N] [NeZero Nc]

/-- The source index `(x, mu, nu)` for the full tensor
`(D^U_mu A_nu)(x)` of CMP99 (3.39). -/
abbrev CMP99PhysicalCovariantOneDerivativeIndex (d N : ℕ) [NeZero N] :=
  FinBox d N × (Fin d × Fin d)

/-- The full derivative tensor equipped with the source maximum norm. -/
abbrev CMP99PhysicalCovariantOneDerivativeSup (d N Nc : ℕ) [NeZero N] :=
  PiLp ⊤ (fun _ : CMP99PhysicalCovariantOneDerivativeIndex d N =>
    SUNLieCoord Nc)

/-- The `nu` component of a physical one-cochain, viewed as a site field. -/
noncomputable def cmp99PhysicalOneCochainComponent
    (A : PhysicalGaugeOneCochain d N Nc) (nu : Fin d) :
    PhysicalGaugeZeroCochain d N Nc :=
  WithLp.toLp 2 fun x => A (x, nu)

@[simp] theorem cmp99PhysicalOneCochainComponent_apply
    (A : PhysicalGaugeOneCochain d N Nc) (nu : Fin d) (x : FinBox d N) :
    cmp99PhysicalOneCochainComponent A nu x = A (x, nu) :=
  rfl

/-- Literal physical realization of CMP99 (3.3) componentwise on a
one-cochain.

The repository convention for `covariantD0CLM` is
`A(x) - R(U(x,x+mu)) A(x+mu)`.  CMP99 (3.3) prints the opposite difference,
divided by the fine lattice spacing `eta`; hence the visible scalar
`-(eta⁻¹)` below. -/
noncomputable def cmp99PhysicalCovariantOneDerivative
    (rho : SUNAdjointModel Nc) (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    CMP99PhysicalCovariantOneDerivativeSup d N Nc :=
  WithLp.toLp ⊤ fun i =>
    (-eta⁻¹) •
      covariantD0CLM rho U
        (cmp99PhysicalOneCochainComponent A i.2.2) (i.1, i.2.1)

@[simp] theorem cmp99PhysicalCovariantOneDerivative_apply
    (rho : SUNAdjointModel Nc) (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (x : FinBox d N) (mu nu : Fin d) :
    cmp99PhysicalCovariantOneDerivative rho eta U A (x, mu, nu) =
      (-eta⁻¹) •
        covariantD0CLM rho U
          (cmp99PhysicalOneCochainComponent A nu) (x, mu) :=
  rfl

/-- Source-facing form of CMP99 (3.3).  This theorem makes the orientation of
the transported endpoint and the visible lattice-spacing factor auditable;
it is not merely an unfolding to the repository's opposite-sign convention. -/
theorem cmp99PhysicalCovariantOneDerivative_source_apply
    (rho : SUNAdjointModel Nc) (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (x : FinBox d N) (mu nu : Fin d) :
    cmp99PhysicalCovariantOneDerivative rho eta U A (x, mu, nu) =
      eta⁻¹ •
        (rho.adCLM (U (ConcreteEdge.mk x mu true))
            (A (x.shift mu, nu)) - A (x, nu)) := by
  rw [cmp99PhysicalCovariantOneDerivative_apply, covariantD0CLM_apply]
  simp only [cmp99PhysicalOneCochainComponent_apply, neg_smul, smul_sub]
  abel

/-- The literal local amplitude clause in (3.35), expressed on base sites of
positive physical bonds. -/
def CMP99PhysicalOneCochainAmplitudeBoundOn
    (cube : Finset (FinBox d N))
    (A : PhysicalGaugeOneCochain d N Nc) (bound : ℝ) : Prop :=
  ∀ x, x ∈ cube → ∀ nu : Fin d, ‖A (x, nu)‖ < bound

/-- The literal local full-derivative clause in (3.35).  This deliberately
quantifies over both `mu` and `nu`; replacing it by the plaquette curl norm
would weaken the source hypothesis. -/
def CMP99PhysicalCovariantOneDerivativeBoundOn
    (cube : Finset (FinBox d N))
    (rho : SUNAdjointModel Nc) (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) (bound : ℝ) : Prop :=
  ∀ x, x ∈ cube → ∀ mu nu : Fin d,
    ‖cmp99PhysicalCovariantOneDerivative rho eta U A (x, mu, nu)‖ < bound

end

end YangMills.RG
