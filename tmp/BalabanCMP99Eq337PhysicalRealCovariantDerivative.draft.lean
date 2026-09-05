import YangMills.RG.BalabanCMP99Eq335PhysicalForwardDerivative
import YangMills.RG.PhysicalGaugeCochains

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# CMP99 (3.37): real-slice covariant derivative of the perturbation

Printed p. 396 bounds `nabla_U^eta A'` in (3.37), and printed p. 397 defines
the corresponding supremum norm through the full tensor
`(D^U_mu A'_nu)(x)` in (3.39).  This module constructs the physical real
slice of that tensor from the literal site-field derivative `covariantD0CLM`.

It is deliberately separate from the ordinary `nabla^eta A` used for the
baseline regularity condition (3.35).  It also does not claim the later
complexified producer required by the analytic theorem.
-/

namespace YangMills.RG

noncomputable section

variable {d N Nc : ℕ}
variable [NeZero d] [NeZero N] [NeZero Nc]

/-- Source index `(x,mu,nu)` for the full real-slice tensor
`(D^U_mu A_nu)(x)` appearing in the norm of (3.37)/(3.39). -/
abbrev CMP99Eq337PhysicalRealCovariantDerivativeIndex
    (d N : ℕ) [NeZero N] :=
  FinBox d N × (Fin d × Fin d)

/-- The full real-slice covariant derivative with the source supremum norm. -/
abbrev CMP99Eq337PhysicalRealCovariantDerivativeSup
    (d N Nc : ℕ) [NeZero N] :=
  PiLp ⊤ (fun _ : CMP99Eq337PhysicalRealCovariantDerivativeIndex d N =>
    SUNLieCoord Nc)

/-- The `nu` component of a physical one-cochain, viewed as a site field. -/
noncomputable def cmp99Eq337PhysicalRealOneCochainComponent
    (A : PhysicalGaugeOneCochain d N Nc) (nu : Fin d) :
    PhysicalGaugeZeroCochain d N Nc :=
  WithLp.toLp 2 fun x => A (x, nu)

@[simp] theorem cmp99Eq337PhysicalRealOneCochainComponent_apply
    (A : PhysicalGaugeOneCochain d N Nc) (nu : Fin d) (x : FinBox d N) :
    cmp99Eq337PhysicalRealOneCochainComponent A nu x = A (x, nu) :=
  rfl

/-- Literal physical real-slice realization of CMP99 (3.3), used by the
`nabla_U^eta A'` clause in (3.37).

The repository convention for `covariantD0CLM` is
`A(x) - R(U(x,x+mu)) A(x+mu)`.  CMP99 (3.3) prints the opposite difference,
divided by `eta`; hence the visible scalar `-(eta^-1)` below. -/
noncomputable def cmp99Eq337PhysicalRealCovariantDerivative
    (rho : SUNAdjointModel Nc) (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    CMP99Eq337PhysicalRealCovariantDerivativeSup d N Nc :=
  WithLp.toLp ⊤ fun i =>
    (-eta⁻¹) •
      covariantD0CLM rho U
        (cmp99Eq337PhysicalRealOneCochainComponent A i.2.2) (i.1, i.2.1)

@[simp] theorem cmp99Eq337PhysicalRealCovariantDerivative_apply
    (rho : SUNAdjointModel Nc) (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (x : FinBox d N) (mu nu : Fin d) :
    cmp99Eq337PhysicalRealCovariantDerivative rho eta U A (x, mu, nu) =
      (-eta⁻¹) •
        covariantD0CLM rho U
          (cmp99Eq337PhysicalRealOneCochainComponent A nu) (x, mu) :=
  rfl

/-- Source-facing form of CMP99 (3.3).  This named theorem fixes the endpoint
orientation and the visible lattice-spacing factor used by (3.37). -/
theorem cmp99Eq337PhysicalRealCovariantDerivative_source_apply
    (rho : SUNAdjointModel Nc) (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (x : FinBox d N) (mu nu : Fin d) :
    cmp99Eq337PhysicalRealCovariantDerivative rho eta U A (x, mu, nu) =
      eta⁻¹ •
        (rho.adCLM (U (ConcreteEdge.mk x mu true))
            (A (x.shift mu, nu)) - A (x, nu)) := by
  rw [cmp99Eq337PhysicalRealCovariantDerivative_apply, covariantD0CLM_apply]
  simp only [cmp99Eq337PhysicalRealOneCochainComponent_apply, neg_smul,
    smul_sub]
  abel

/-- Literal real-slice local clause `|nabla_U^eta A'| < bound` from (3.37),
with both tensor indices visible.  The complexified analogue remains an open
source dictionary and is not supplied by this predicate. -/
def CMP99Eq337PhysicalRealCovariantDerivativeBoundOn
    (region : Finset (FinBox d N))
    (rho : SUNAdjointModel Nc) (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) (bound : ℝ) : Prop :=
  ∀ x, x ∈ region → ∀ mu nu : Fin d,
    ‖cmp99Eq337PhysicalRealCovariantDerivative rho eta U A
        (x, mu, nu)‖ < bound

end

end YangMills.RG
