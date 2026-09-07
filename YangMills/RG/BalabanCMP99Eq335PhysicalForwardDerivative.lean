/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FiniteTorusCurlDiv
import YangMills.RG.PhysicalGaugeCochains

/-!
# CMP99 (3.35): the fine-lattice first derivative of a one-cochain

Printed p. 396 uses `nabla^eta A` in (3.35).  It does not use the covariant
tensor `D^U A` introduced later in (3.39).  This module therefore applies the
already literal periodic forward difference to every `(mu,nu)` component and
keeps the factor `eta^-1` visible.
-/

namespace YangMills.RG

noncomputable section

variable {d N Nc : ℕ}
variable [NeZero d] [NeZero N] [NeZero Nc]

/-- Index `(x,mu,nu)` for the complete first-difference tensor. -/
abbrev CMP99PhysicalForwardOneDerivativeIndex (d N : ℕ) [NeZero N] :=
  FinBox d N × (Fin d × Fin d)

/-- The first-difference tensor with the source maximum norm. -/
abbrev CMP99PhysicalForwardOneDerivativeSup (d N Nc : ℕ) [NeZero N] :=
  PiLp ⊤ (fun _ : CMP99PhysicalForwardOneDerivativeIndex d N =>
    SUNLieCoord Nc)

/-- Literal `eta`-scale forward derivative of every component `A_nu` in the
direction `mu`. -/
noncomputable def cmp99PhysicalForwardOneDerivative
    (eta : ℝ) (A : PhysicalGaugeOneCochain d N Nc) :
    CMP99PhysicalForwardOneDerivativeSup d N Nc :=
  WithLp.toLp ⊤ fun i =>
    eta⁻¹ • torusForwardDiff i.2.1 (fun y => A (y, i.2.2)) i.1

@[simp] theorem cmp99PhysicalForwardOneDerivative_apply
    (eta : ℝ) (A : PhysicalGaugeOneCochain d N Nc)
    (x : FinBox d N) (mu nu : Fin d) :
    cmp99PhysicalForwardOneDerivative eta A (x, mu, nu) =
      eta⁻¹ • (A (x.shift mu, nu) - A (x, nu)) := by
  rfl

/-- Literal local amplitude clause in (3.35). -/
def CMP99PhysicalOneCochainAmplitudeBoundOn
    (cube : Finset (FinBox d N))
    (A : PhysicalGaugeOneCochain d N Nc) (bound : ℝ) : Prop :=
  ∀ x, x ∈ cube → ∀ nu : Fin d, ‖A (x, nu)‖ < bound

/-- Literal local `|nabla^eta A|` clause in (3.35), with both tensor indices
visible and no background configuration parameter. -/
def CMP99PhysicalForwardOneDerivativeBoundOn
    (cube : Finset (FinBox d N)) (eta : ℝ)
    (A : PhysicalGaugeOneCochain d N Nc) (bound : ℝ) : Prop :=
  ∀ x, x ∈ cube → ∀ mu nu : Fin d,
    ‖cmp99PhysicalForwardOneDerivative eta A (x, mu, nu)‖ < bound

end

end YangMills.RG
