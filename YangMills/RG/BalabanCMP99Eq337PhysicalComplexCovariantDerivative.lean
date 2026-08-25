import YangMills.RG.BalabanCMP99Eq337PhysicalRealCovariantDerivative
import YangMills.RG.BalabanCMP99PhysicalFibreComplexification

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# CMP99 (3.37): complexified covariant derivative of the perturbation

The baseline background `U` remains `SUN`-valued in (3.37), while `A'` takes
values in the complexified Lie algebra.  This module extends the real adjoint
action complex-linearly in the explicit coordinate fibre and constructs the
full `(mu,nu)` derivative tensor.  It accepts no arbitrary derivative family.

It does not yet construct the complex group element `exp(i eta A') U` or its
localized `Qprime` tower.
-/

namespace YangMills.RG

noncomputable section

variable {d N Nc : ℕ}
variable [NeZero d] [NeZero N] [NeZero Nc]

/-- Real part of the explicit complexified Lie-coordinate fibre. -/
def cmp99SUNLieComplexCoordRealPart (Z : SUNLieComplexCoord Nc) :
    SUNLieCoord Nc :=
  WithLp.toLp 2 fun a => (Z a).re

/-- Imaginary part of the explicit complexified Lie-coordinate fibre. -/
def cmp99SUNLieComplexCoordImagPart (Z : SUNLieComplexCoord Nc) :
    SUNLieCoord Nc :=
  WithLp.toLp 2 fun a => (Z a).im

@[simp] theorem cmp99SUNLieComplexCoordRealPart_complexification
    (X : SUNLieCoord Nc) :
    cmp99SUNLieComplexCoordRealPart
        (cmp99SUNLieCoordComplexificationLM Nc X) = X := by
  ext a
  rfl

@[simp] theorem cmp99SUNLieComplexCoordImagPart_complexification
    (X : SUNLieCoord Nc) :
    cmp99SUNLieComplexCoordImagPart
        (cmp99SUNLieCoordComplexificationLM Nc X) = 0 := by
  ext a
  change ((X a : ℂ)).im = 0
  simp

theorem cmp99SUNLieComplexCoordRealPart_add
    (Z W : SUNLieComplexCoord Nc) :
    cmp99SUNLieComplexCoordRealPart (Z + W) =
      cmp99SUNLieComplexCoordRealPart Z +
        cmp99SUNLieComplexCoordRealPart W := by
  ext a
  simp [cmp99SUNLieComplexCoordRealPart]

theorem cmp99SUNLieComplexCoordImagPart_add
    (Z W : SUNLieComplexCoord Nc) :
    cmp99SUNLieComplexCoordImagPart (Z + W) =
      cmp99SUNLieComplexCoordImagPart Z +
        cmp99SUNLieComplexCoordImagPart W := by
  ext a
  simp [cmp99SUNLieComplexCoordImagPart]

theorem cmp99SUNLieComplexCoordRealPart_smul
    (c : ℂ) (Z : SUNLieComplexCoord Nc) :
    cmp99SUNLieComplexCoordRealPart (c • Z) =
      c.re • cmp99SUNLieComplexCoordRealPart Z -
        c.im • cmp99SUNLieComplexCoordImagPart Z := by
  ext a
  change (c * Z a).re = c.re * (Z a).re - c.im * (Z a).im
  rw [Complex.mul_re]

theorem cmp99SUNLieComplexCoordImagPart_smul
    (c : ℂ) (Z : SUNLieComplexCoord Nc) :
    cmp99SUNLieComplexCoordImagPart (c • Z) =
      c.im • cmp99SUNLieComplexCoordRealPart Z +
        c.re • cmp99SUNLieComplexCoordImagPart Z := by
  ext a
  change (c * Z a).im = c.im * (Z a).re + c.re * (Z a).im
  rw [Complex.mul_im]
  ac_rfl

/-- Canonical complex-linear extension of the physical adjoint action of
one compact background link. -/
noncomputable def cmp99SUNAdjointComplexActionLM
    (rho : SUNAdjointModel Nc) (g : SUN Nc) :
    SUNLieComplexCoord Nc →ₗ[ℂ] SUNLieComplexCoord Nc where
  toFun Z :=
    cmp99SUNLieCoordComplexificationLM Nc
        (rho.adCLM g (cmp99SUNLieComplexCoordRealPart Z)) +
      Complex.I • cmp99SUNLieCoordComplexificationLM Nc
        (rho.adCLM g (cmp99SUNLieComplexCoordImagPart Z))
  map_add' Z W := by
    rw [cmp99SUNLieComplexCoordRealPart_add,
      cmp99SUNLieComplexCoordImagPart_add, map_add, map_add]
    ext a
    simp
    ring
  map_smul' c Z := by
    rw [cmp99SUNLieComplexCoordRealPart_smul,
      cmp99SUNLieComplexCoordImagPart_smul,
      map_sub, map_add, map_smul, map_smul, map_smul, map_smul]
    ext a
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]
      ring
    · simp [Complex.mul_re, Complex.mul_im]

/-- Complex-linear extension, written explicitly by real and imaginary
parts, of the physical adjoint action of one compact background link. -/
def cmp99SUNAdjointComplexAction
    (rho : SUNAdjointModel Nc) (g : SUN Nc)
    (Z : SUNLieComplexCoord Nc) : SUNLieComplexCoord Nc :=
  cmp99SUNAdjointComplexActionLM rho g Z

/-- The complex action agrees with the physical adjoint action on the real
slice. -/
theorem cmp99SUNAdjointComplexAction_complexification
    (rho : SUNAdjointModel Nc) (g : SUN Nc) (X : SUNLieCoord Nc) :
    cmp99SUNAdjointComplexAction rho g
        (cmp99SUNLieCoordComplexificationLM Nc X) =
      cmp99SUNLieCoordComplexificationLM Nc (rho.adCLM g X) := by
  simp [cmp99SUNAdjointComplexAction]

/-- One complexified Lie-coordinate value per positive physical bond. -/
abbrev CMP99Eq337PhysicalComplexOneCochain (d N Nc : ℕ) [NeZero N] :=
  PiLp 2 (fun _ : PhysicalBond d N => SUNLieComplexCoord Nc)

/-- Coordinatewise inclusion of a physical real one-cochain into the
explicit complexified fibre. -/
noncomputable def cmp99Eq337PhysicalComplexifyOneCochain
    (A : PhysicalGaugeOneCochain d N Nc) :
    CMP99Eq337PhysicalComplexOneCochain d N Nc :=
  WithLp.toLp 2 fun b => cmp99SUNLieCoordComplexificationLM Nc (A b)

@[simp] theorem cmp99Eq337PhysicalComplexifyOneCochain_apply
    (A : PhysicalGaugeOneCochain d N Nc) (b : PhysicalBond d N) :
    cmp99Eq337PhysicalComplexifyOneCochain A b =
      cmp99SUNLieCoordComplexificationLM Nc (A b) :=
  rfl

/-- Source index `(x,mu,nu)` for the full complex tensor. -/
abbrev CMP99Eq337PhysicalComplexCovariantDerivativeIndex
    (d N : ℕ) [NeZero N] :=
  FinBox d N × (Fin d × Fin d)

/-- The complete complex covariant derivative with the source supremum norm. -/
abbrev CMP99Eq337PhysicalComplexCovariantDerivativeSup
    (d N Nc : ℕ) [NeZero N] :=
  PiLp ⊤ (fun _ : CMP99Eq337PhysicalComplexCovariantDerivativeIndex d N =>
    SUNLieComplexCoord Nc)

/-- The `nu` component of a complex physical one-cochain as a site field. -/
def cmp99Eq337PhysicalComplexOneCochainComponent
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc) (nu : Fin d) :
    FinBox d N → SUNLieComplexCoord Nc :=
  fun x => A (x, nu)

/-- Complex-linear operator underlying the literal complexification of
CMP99 (3.3), with source orientation and visible real lattice spacing. -/
noncomputable def cmp99Eq337PhysicalComplexCovariantDerivativeLM
    (rho : SUNAdjointModel Nc) (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc) :
    CMP99Eq337PhysicalComplexOneCochain d N Nc →ₗ[ℂ]
      CMP99Eq337PhysicalComplexCovariantDerivativeSup d N Nc where
  toFun A := WithLp.toLp ⊤ fun i =>
      ((eta : ℂ)⁻¹) •
        (cmp99SUNAdjointComplexActionLM rho
            (U (ConcreteEdge.mk i.1 i.2.1 true))
            (A (i.1.shift i.2.1, i.2.2)) -
          A (i.1, i.2.2))
  map_add' A B := by
    apply PiLp.ext
    intro i
    simp
    module
  map_smul' c A := by
    apply PiLp.ext
    intro i
    simp
    module

/-- Literal complexified component of CMP99 (3.3), exposed as the value of
the internally constructed complex-linear operator. -/
noncomputable def cmp99Eq337PhysicalComplexCovariantDerivative
    (rho : SUNAdjointModel Nc) (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc) :
    CMP99Eq337PhysicalComplexCovariantDerivativeSup d N Nc :=
  cmp99Eq337PhysicalComplexCovariantDerivativeLM rho eta U A

@[simp] theorem cmp99Eq337PhysicalComplexCovariantDerivative_apply
    (rho : SUNAdjointModel Nc) (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (x : FinBox d N) (mu nu : Fin d) :
    cmp99Eq337PhysicalComplexCovariantDerivative rho eta U A
        (x, mu, nu) =
      ((eta : ℂ)⁻¹) •
        (cmp99SUNAdjointComplexAction rho
            (U (ConcreteEdge.mk x mu true)) (A (x.shift mu, nu)) -
          A (x, nu)) :=
  rfl

/-- The complex tensor restricts exactly to the physical real tensor.  This
proves that the complex-linear extension is not an independently chosen
derivative with a coincidentally matching bound. -/
theorem cmp99Eq337PhysicalComplexCovariantDerivative_complexification
    (rho : SUNAdjointModel Nc) (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (x : FinBox d N) (mu nu : Fin d) :
    cmp99Eq337PhysicalComplexCovariantDerivative rho eta U
        (cmp99Eq337PhysicalComplexifyOneCochain A) (x, mu, nu) =
      cmp99SUNLieCoordComplexificationLM Nc
        (cmp99Eq337PhysicalRealCovariantDerivative rho eta U A
          (x, mu, nu)) := by
  rw [cmp99Eq337PhysicalComplexCovariantDerivative_apply,
    cmp99Eq337PhysicalComplexifyOneCochain_apply,
    cmp99SUNAdjointComplexAction_complexification,
    cmp99Eq337PhysicalComplexifyOneCochain_apply,
    cmp99Eq337PhysicalRealCovariantDerivative_source_apply]
  ext a
  simp

/-- Literal complex amplitude clause in (3.37). -/
def CMP99Eq337PhysicalComplexAmplitudeBoundOn
    (region : Finset (FinBox d N))
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (bound : ℝ) : Prop :=
  ∀ x, x ∈ region → ∀ nu : Fin d, ‖A (x, nu)‖ < bound

/-- Literal complex covariant-derivative clause in (3.37). -/
def CMP99Eq337PhysicalComplexCovariantDerivativeBoundOn
    (region : Finset (FinBox d N))
    (rho : SUNAdjointModel Nc) (eta : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (bound : ℝ) : Prop :=
  ∀ x, x ∈ region → ∀ mu nu : Fin d,
    ‖cmp99Eq337PhysicalComplexCovariantDerivative rho eta U A
        (x, mu, nu)‖ < bound

end

end YangMills.RG
