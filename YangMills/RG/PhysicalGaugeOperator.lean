/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.L0_Lattice.FiniteLatticeGeometryInstance
import YangMills.RG.AveragingAdjoint
import YangMills.RG.GaugeFixedPrecision

/-!
# Finite physical gauge-operator interface

This module starts the P4 physical-operator layer without claiming a physical
Yang--Mills Hessian theorem.  It implements the source-faithful direction
chosen for the next step: work on the full fluctuation space with a soft
block-constraint mass `a Q†Q`.

The key naming distinction is explicit:

* a gauge constraint is a condition such as a divergence or axial gauge;
* the block constraint is the RG block-average derivative `Q`.

The module provides finite positive-bond cochains, active regions with
Dirichlet zero-extension maps, flat coboundary operators, the flat gauge
constraint, the positive-bond version of the existing scaled averaging
operator, and the soft full-space precision shell
`physicalKslice + a Q†Q`.

It does not define the nonabelian Wilson Hessian from a source formula, prove
the Hodge/Poincare estimate, or identify the later hard-constrained covariance.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

/-- The physical spacetime dimension used by the target Yang--Mills problem. -/
abbrev PhysicalDim : ℕ := 4

/-- One fine side length after one block step. -/
abbrev FineSide (L N' : ℕ) : ℕ := L * N'

/-- Positively oriented independent bonds.  Unlike `ConcreteEdge`, this type
does not duplicate the reverse orientation. -/
abbrev PositiveBond (d N : ℕ) := FinBox d N × Fin d

/-- Full zero-cochains on sites. -/
abbrev GaugeZeroCochain (d N : ℕ) (𝔤 : Type*) :=
  PiLp 2 (fun _ : FinBox d N => 𝔤)

/-- Full one-cochains on positively oriented bonds. -/
abbrev GaugeOneCochain (d N : ℕ) (𝔤 : Type*) :=
  PiLp 2 (fun _ : PositiveBond d N => 𝔤)

/-- Full two-cochains on concrete plaquettes. -/
abbrev GaugeTwoCochain (d N : ℕ) (𝔤 : Type*) :=
  PiLp 2 (fun _ : ConcretePlaquette d N => 𝔤)

/-- A finite active site region.  Boundary conventions are supplied by the
restriction and zero-extension maps below. -/
structure ActiveGaugeRegion (d N : ℕ) where
  sites : Finset (FinBox d N)

namespace ActiveGaugeRegion

variable {d N : ℕ} [NeZero N]

/-- Active positive bonds: both endpoints lie in the active site set. -/
def bonds (Ω : ActiveGaugeRegion d N) : Finset (PositiveBond d N) :=
  Finset.univ.filter fun b =>
    b.1 ∈ Ω.sites ∧ FinBox.shift b.1 b.2 ∈ Ω.sites

/-- Active plaquettes: all four vertices lie in the active site set. -/
def plaquettes (Ω : ActiveGaugeRegion d N) :
    Finset (ConcretePlaquette d N) :=
  Finset.univ.filter fun p =>
    ∀ i : Fin 4, p.vertices i ∈ Ω.sites

/-- Active site subtype. -/
abbrev Site (Ω : ActiveGaugeRegion d N) :=
  {x : FinBox d N // x ∈ Ω.sites}

/-- Active positive-bond subtype. -/
abbrev Bond (Ω : ActiveGaugeRegion d N) :=
  {b : PositiveBond d N // b ∈ Ω.bonds}

/-- Active plaquette subtype. -/
abbrev Plaquette (Ω : ActiveGaugeRegion d N) :=
  {p : ConcretePlaquette d N // p ∈ Ω.plaquettes}

end ActiveGaugeRegion

/-- Active zero-cochains. -/
abbrev ActiveGaugeZeroCochain {d N : ℕ} [NeZero N]
    (Ω : ActiveGaugeRegion d N) (𝔤 : Type*) :=
  PiLp 2 (fun _ : ActiveGaugeRegion.Site Ω => 𝔤)

/-- Active one-cochains. -/
abbrev ActiveGaugeOneCochain {d N : ℕ} [NeZero N]
    (Ω : ActiveGaugeRegion d N) (𝔤 : Type*) :=
  PiLp 2 (fun _ : ActiveGaugeRegion.Bond Ω => 𝔤)

/-- Active two-cochains. -/
abbrev ActiveGaugeTwoCochain {d N : ℕ} [NeZero N]
    (Ω : ActiveGaugeRegion d N) (𝔤 : Type*) :=
  PiLp 2 (fun _ : ActiveGaugeRegion.Plaquette Ω => 𝔤)

section ActiveMaps

variable {d N : ℕ} [NeZero N] {𝔤 : Type*}
variable [NormedAddCommGroup 𝔤] [InnerProductSpace ℝ 𝔤]
variable [FiniteDimensional ℝ 𝔤]

/-- Dirichlet zero-extension for active zero-cochains. -/
noncomputable def extendZeroZeroCLM (Ω : ActiveGaugeRegion d N) :
    ActiveGaugeZeroCochain Ω 𝔤 →L[ℝ] GaugeZeroCochain d N 𝔤 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun φ =>
        WithLp.toLp 2 fun x =>
          if hx : x ∈ Ω.sites then φ ⟨x, hx⟩ else 0
      map_add' := fun φ ψ => by
        ext x
        by_cases hx : x ∈ Ω.sites <;> simp [hx]
      map_smul' := fun r φ => by
        ext x
        by_cases hx : x ∈ Ω.sites <;> simp [hx] }

/-- Restriction to active sites. -/
noncomputable def restrictZeroCLM (Ω : ActiveGaugeRegion d N) :
    GaugeZeroCochain d N 𝔤 →L[ℝ] ActiveGaugeZeroCochain Ω 𝔤 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun φ =>
        WithLp.toLp 2 fun x : ActiveGaugeRegion.Site Ω => φ x.1
      map_add' := fun φ ψ => by ext x; rfl
      map_smul' := fun r φ => by ext x; rfl }

/-- Dirichlet zero-extension for active one-cochains. -/
noncomputable def extendZeroOneCLM (Ω : ActiveGaugeRegion d N) :
    ActiveGaugeOneCochain Ω 𝔤 →L[ℝ] GaugeOneCochain d N 𝔤 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        WithLp.toLp 2 fun b =>
          if hb : b ∈ Ω.bonds then A ⟨b, hb⟩ else 0
      map_add' := fun A B => by
        ext b
        by_cases hb : b ∈ Ω.bonds <;> simp [hb]
      map_smul' := fun r A => by
        ext b
        by_cases hb : b ∈ Ω.bonds <;> simp [hb] }

/-- Restriction to active positive bonds. -/
noncomputable def restrictOneCLM (Ω : ActiveGaugeRegion d N) :
    GaugeOneCochain d N 𝔤 →L[ℝ] ActiveGaugeOneCochain Ω 𝔤 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        WithLp.toLp 2 fun b : ActiveGaugeRegion.Bond Ω => A b.1
      map_add' := fun A B => by ext b; rfl
      map_smul' := fun r A => by ext b; rfl }

/-- Dirichlet zero-extension for active two-cochains. -/
noncomputable def extendZeroTwoCLM (Ω : ActiveGaugeRegion d N) :
    ActiveGaugeTwoCochain Ω 𝔤 →L[ℝ] GaugeTwoCochain d N 𝔤 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun F =>
        WithLp.toLp 2 fun p =>
          if hp : p ∈ Ω.plaquettes then F ⟨p, hp⟩ else 0
      map_add' := fun F H => by
        ext p
        by_cases hp : p ∈ Ω.plaquettes <;> simp [hp]
      map_smul' := fun r F => by
        ext p
        by_cases hp : p ∈ Ω.plaquettes <;> simp [hp] }

/-- Restriction to active plaquettes. -/
noncomputable def restrictTwoCLM (Ω : ActiveGaugeRegion d N) :
    GaugeTwoCochain d N 𝔤 →L[ℝ] ActiveGaugeTwoCochain Ω 𝔤 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun F =>
        WithLp.toLp 2 fun p : ActiveGaugeRegion.Plaquette Ω => F p.1
      map_add' := fun F H => by ext p; rfl
      map_smul' := fun r F => by ext p; rfl }

end ActiveMaps

section FlatDifferentials

variable {d N : ℕ} [NeZero N] {𝔤 : Type*}
variable [NormedAddCommGroup 𝔤] [InnerProductSpace ℝ 𝔤]
variable [FiniteDimensional ℝ 𝔤]

/-- Full flat exterior derivative from zero- to one-cochains. -/
noncomputable def flatD0FullCLM :
    GaugeZeroCochain d N 𝔤 →L[ℝ] GaugeOneCochain d N 𝔤 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun φ =>
        WithLp.toLp 2 fun b : PositiveBond d N =>
          φ (FinBox.shift b.1 b.2) - φ b.1
      map_add' := fun φ ψ => by
        ext b
        simp only [PiLp.add_apply]
        abel
      map_smul' := fun r φ => by
        ext b
        simp [sub_eq_add_neg, smul_add] }

/-- Full flat exterior derivative from one- to two-cochains. -/
noncomputable def flatD1FullCLM :
    GaugeOneCochain d N 𝔤 →L[ℝ] GaugeTwoCochain d N 𝔤 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        WithLp.toLp 2 fun p : ConcretePlaquette d N =>
          A (p.site, p.dir1)
            + A (FinBox.shift p.site p.dir1, p.dir2)
            - A (FinBox.shift p.site p.dir2, p.dir1)
            - A (p.site, p.dir2)
      map_add' := fun A B => by
        ext p
        simp only [PiLp.add_apply]
        abel
      map_smul' := fun r A => by
        ext p
        simp [sub_eq_add_neg, smul_add] }

/-- On the full periodic lattice, the flat coboundaries square to zero. -/
theorem flatD1FullCLM_comp_flatD0FullCLM :
    (flatD1FullCLM (d := d) (N := N) (𝔤 := 𝔤)).comp
      (flatD0FullCLM (d := d) (N := N) (𝔤 := 𝔤)) = 0 := by
  ext φ p
  have hcomm :
      FinBox.shift (FinBox.shift p.site p.dir1) p.dir2 =
        FinBox.shift (FinBox.shift p.site p.dir2) p.dir1 :=
    FinBox.shift_comm p.site p.dir1 p.dir2 (Fin.ne_of_lt p.hlt)
  simp [flatD0FullCLM, flatD1FullCLM, hcomm]

/-- Active flat `d₀`, implemented by zero-extending, applying the full
periodic operator, and restricting back to active bonds. -/
noncomputable def flatD0CLM (Ω : ActiveGaugeRegion d N) :
    ActiveGaugeZeroCochain Ω 𝔤 →L[ℝ] ActiveGaugeOneCochain Ω 𝔤 :=
  (restrictOneCLM (𝔤 := 𝔤) Ω).comp
    ((flatD0FullCLM (d := d) (N := N) (𝔤 := 𝔤)).comp
      (extendZeroZeroCLM (𝔤 := 𝔤) Ω))

/-- Active flat `d₁`, implemented by zero-extending, applying the full
periodic operator, and restricting back to active plaquettes. -/
noncomputable def flatD1CLM (Ω : ActiveGaugeRegion d N) :
    ActiveGaugeOneCochain Ω 𝔤 →L[ℝ] ActiveGaugeTwoCochain Ω 𝔤 :=
  (restrictTwoCLM (𝔤 := 𝔤) Ω).comp
    ((flatD1FullCLM (d := d) (N := N) (𝔤 := 𝔤)).comp
      (extendZeroOneCLM (𝔤 := 𝔤) Ω))

/-- The flat gauge condition is the adjoint of `d₀`. -/
noncomputable def flatGaugeConstraintCLM (Ω : ActiveGaugeRegion d N) :
    ActiveGaugeOneCochain Ω 𝔤 →L[ℝ] ActiveGaugeZeroCochain Ω 𝔤 :=
  (flatD0CLM (𝔤 := 𝔤) Ω).adjoint

/-- The unweighted flat gauge Laplacian on active one-cochains. -/
noncomputable def flatGaugeLaplacian (Ω : ActiveGaugeRegion d N) :
    ActiveGaugeOneCochain Ω 𝔤 →L[ℝ] ActiveGaugeOneCochain Ω 𝔤 :=
  (flatD1CLM (𝔤 := 𝔤) Ω).adjoint.comp (flatD1CLM (𝔤 := 𝔤) Ω)
    + (flatGaugeConstraintCLM (𝔤 := 𝔤) Ω).adjoint.comp
        (flatGaugeConstraintCLM (𝔤 := 𝔤) Ω)

/-- Weighted flat slice operator: curvature/curl energy plus gauge-fixing
energy. -/
noncomputable def flatKslice (Ω : ActiveGaugeRegion d N)
    (wilsonQuadCoeff ξInv : ℝ) :
    ActiveGaugeOneCochain Ω 𝔤 →L[ℝ] ActiveGaugeOneCochain Ω 𝔤 :=
  wilsonQuadCoeff •
      ((flatD1CLM (𝔤 := 𝔤) Ω).adjoint.comp (flatD1CLM (𝔤 := 𝔤) Ω))
    + ξInv •
      ((flatGaugeConstraintCLM (𝔤 := 𝔤) Ω).adjoint.comp
        (flatGaugeConstraintCLM (𝔤 := 𝔤) Ω))

/-- The flat slice is nonnegative when its two physical weights are
nonnegative. -/
theorem flatKslice_nonnegative (Ω : ActiveGaugeRegion d N)
    {wilsonQuadCoeff ξInv : ℝ}
    (hw : 0 ≤ wilsonQuadCoeff) (hξ : 0 ≤ ξInv) :
    ∀ A : ActiveGaugeOneCochain Ω 𝔤,
      0 ≤ inner ℝ A (flatKslice (𝔤 := 𝔤) Ω wilsonQuadCoeff ξInv A) := by
  intro A
  have hD :
      inner ℝ A
        (((flatD1CLM (𝔤 := 𝔤) Ω).adjoint.comp
          (flatD1CLM (𝔤 := 𝔤) Ω)) A)
        = ‖flatD1CLM (𝔤 := 𝔤) Ω A‖ ^ 2 := by
    rw [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have hG :
      inner ℝ A
        (((flatGaugeConstraintCLM (𝔤 := 𝔤) Ω).adjoint.comp
          (flatGaugeConstraintCLM (𝔤 := 𝔤) Ω)) A)
        = ‖flatGaugeConstraintCLM (𝔤 := 𝔤) Ω A‖ ^ 2 := by
    rw [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [flatKslice, ContinuousLinearMap.add_apply, inner_add_right,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    inner_smul_right, inner_smul_right, hD, hG]
  exact add_nonneg
    (mul_nonneg hw (sq_nonneg _))
    (mul_nonneg hξ (sq_nonneg _))

end FlatDifferentials

section PositiveAveraging

variable {d : ℕ} {𝔤 : Type*}
variable [NormedAddCommGroup 𝔤] [InnerProductSpace ℝ 𝔤]
variable [FiniteDimensional ℝ 𝔤]

/-- Convert a positive-bond additive field into an oriented concrete-edge field
with the linearized reversal convention. -/
def positiveBondFieldToConcrete {N : ℕ} (A : GaugeOneCochain d N 𝔤) :
    ConcreteEdge d N → 𝔤 :=
  fun e => if e.sign then A (e.source, e.dir) else -A (e.source, e.dir)

omit [InnerProductSpace ℝ 𝔤] [FiniteDimensional ℝ 𝔤] in
@[simp]
theorem positiveBondFieldToConcrete_add {N : ℕ}
    (A B : GaugeOneCochain d N 𝔤) :
  positiveBondFieldToConcrete (d := d) (N := N) (A + B)
      = positiveBondFieldToConcrete (d := d) (N := N) A
        + positiveBondFieldToConcrete (d := d) (N := N) B := by
  funext e
  by_cases h : e.sign = true
  · simp [positiveBondFieldToConcrete, h]
  · simp [positiveBondFieldToConcrete, h]
    abel

omit [FiniteDimensional ℝ 𝔤] in
@[simp]
theorem positiveBondFieldToConcrete_smul {N : ℕ}
    (r : ℝ) (A : GaugeOneCochain d N 𝔤) :
    positiveBondFieldToConcrete (d := d) (N := N) (r • A)
      = r • positiveBondFieldToConcrete (d := d) (N := N) A := by
  funext e
  cases e.sign <;> simp [positiveBondFieldToConcrete]

/-- Positive-bond version of the scaled linear RG average.  The underlying
formula is still the already verified `linAvg`; the input field is first
expanded to concrete oriented edges by the linearized reversal convention. -/
noncomputable def positiveScaledLinAvgCLM (s : ℝ) (L N' : ℕ)
    [NeZero L] [NeZero N']
    [Fintype (ConcreteEdge d (L * N'))] [Fintype (ConcreteEdge d N')] :
    GaugeOneCochain d (L * N') 𝔤 →L[ℝ] GaugeOneCochain d N' 𝔤 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        WithLp.toLp 2 fun b : PositiveBond d N' =>
          s • linAvg L N'
            (positiveBondFieldToConcrete (d := d) (N := L * N') A)
            ⟨b.1, b.2, true⟩
      map_add' := fun A B => by
        ext b
        change s • linAvg L N'
            (positiveBondFieldToConcrete (d := d) (N := L * N') (A + B))
            ⟨b.1, b.2, true⟩ =
          (s • linAvg L N'
              (positiveBondFieldToConcrete (d := d) (N := L * N') A)
              ⟨b.1, b.2, true⟩)
            + (s • linAvg L N'
              (positiveBondFieldToConcrete (d := d) (N := L * N') B)
              ⟨b.1, b.2, true⟩)
        rw [positiveBondFieldToConcrete_add, linAvg_add, smul_add]
      map_smul' := fun r A => by
        ext b
        change s • linAvg L N'
            (positiveBondFieldToConcrete (d := d) (N := L * N') (r • A))
            ⟨b.1, b.2, true⟩ =
          r • (s • linAvg L N'
            (positiveBondFieldToConcrete (d := d) (N := L * N') A)
            ⟨b.1, b.2, true⟩)
        rw [positiveBondFieldToConcrete_smul, linAvg_smul]
        rw [smul_comm] }

@[simp]
theorem positiveScaledLinAvgCLM_apply (s : ℝ) (L N' : ℕ)
    [NeZero L] [NeZero N']
    [Fintype (ConcreteEdge d (L * N'))] [Fintype (ConcreteEdge d N')]
    (A : GaugeOneCochain d (L * N') 𝔤) (b : PositiveBond d N') :
    positiveScaledLinAvgCLM (d := d) (𝔤 := 𝔤) s L N' A b =
      s • linAvg L N'
        (positiveBondFieldToConcrete (d := d) (N := L * N') A)
        ⟨b.1, b.2, true⟩ := by
  rfl

/-- The active-region block constraint `Q`, using Dirichlet zero extension
before applying the positive-bond averaging operator. -/
noncomputable def blockConstraintCLM {L N' : ℕ} [NeZero L] [NeZero N']
    [Fintype (ConcreteEdge d (L * N'))] [Fintype (ConcreteEdge d N')]
    (Ω : ActiveGaugeRegion d (L * N')) (s : ℝ) :
    ActiveGaugeOneCochain Ω 𝔤 →L[ℝ] GaugeOneCochain d N' 𝔤 :=
  (positiveScaledLinAvgCLM (d := d) (𝔤 := 𝔤) s L N').comp
    (extendZeroOneCLM (𝔤 := 𝔤) Ω)

end PositiveAveraging

section PhysicalPrecisionShell

variable {E GaugeF BlockF : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup GaugeF] [InnerProductSpace ℝ GaugeF] [CompleteSpace GaugeF]
variable [NormedAddCommGroup BlockF] [InnerProductSpace ℝ BlockF] [CompleteSpace BlockF]

/-- A physical slice operator is the Wilson Hessian candidate plus a
gauge-constraint adjoint mass.  The Hessian and gauge constraint are supplied
as explicit operators; source work must identify them with Balaban/Dimock's
objects. -/
noncomputable def physicalKslice
    (physicalGaugeHessian : E →L[ℝ] E)
    (gaugeConstraintCLM : E →L[ℝ] GaugeF)
    (ξInv : ℝ) :
    E →L[ℝ] E :=
  physicalGaugeHessian
    + ξInv • (gaugeConstraintCLM.adjoint.comp gaugeConstraintCLM)

/-- The soft full-space physical precision shell
`physicalKslice + a Q†Q`.  Here `blockConstraintCLM` is the RG block derivative
`Q`, not the gauge condition. -/
noncomputable def gaugeFixedPhysicalPrecision
    (physicalGaugeHessian : E →L[ℝ] E)
    (gaugeConstraintCLM : E →L[ℝ] GaugeF)
    (blockConstraintCLM : E →L[ℝ] BlockF)
    (ξInv a : ℝ) :
    E →L[ℝ] E :=
  gaugeFixedBasePrecisionCLM
    (physicalKslice physicalGaugeHessian gaugeConstraintCLM ξInv)
    blockConstraintCLM
    a

/-- Exact algebraic defect between a flat soft precision and the supplied
physical soft precision.  This is a definition, not a source estimate. -/
noncomputable def physicalPrecisionDefect
    (flatSlice physicalPrecision : E →L[ℝ] E)
    (blockConstraintCLM : E →L[ℝ] BlockF)
    (a : ℝ) :
    E →L[ℝ] E :=
  gaugeFixedBasePrecisionCLM flatSlice blockConstraintCLM a
    - physicalPrecision

/-- A named operator-norm small-background hypothesis.  The source theorem
proving this from a paper small-field condition remains external to this
definition. -/
def SmallBackgroundPerturbation
    (flatSlice physicalPrecision : E →L[ℝ] E)
    (blockConstraintCLM : E →L[ℝ] BlockF)
    (a δ : ℝ) : Prop :=
  ‖physicalPrecisionDefect flatSlice physicalPrecision blockConstraintCLM a‖ ≤ δ

/-- The defect definition gives an exact decomposition of the physical
precision as flat precision minus defect. -/
theorem physicalPrecision_eq_flat_sub_defect
    (flatSlice physicalPrecision : E →L[ℝ] E)
    (blockConstraintCLM : E →L[ℝ] BlockF)
    (a : ℝ) :
    physicalPrecision =
      gaugeFixedBasePrecisionCLM flatSlice blockConstraintCLM a
        - physicalPrecisionDefect flatSlice physicalPrecision blockConstraintCLM a := by
  ext x
  simp [physicalPrecisionDefect]

/-- Coercivity of a supplied physical precision from a single Catalan-controlled
physical precision defect.  The theorem instantiates the finite
block-Poincare/Catalan consumer with the concrete algebraic defect
`physicalPrecisionDefect`; the source estimate that this defect obeys the
Catalan partial bound remains the explicit hypothesis `hdefect`. -/
theorem isCoerciveCLM_physicalPrecision_of_catalanMajorantPartial_defect
    (flatSlice physicalPrecision : E →L[ℝ] E)
    (blockConstraintCLM : E →L[ℝ] BlockF)
    {M epsilon : ℝ} (N : ℕ) {a CP : ℝ}
    (ha : 0 ≤ a)
    (hCP : 0 < CP)
    (hflat_nonneg :
      ∀ x : E, 0 ≤ inner ℝ x (flatSlice x))
    (hPoincare :
      ∀ x : E,
        ‖x‖ ^ 2 ≤
          CP * (inner ℝ x (flatSlice x) + ‖blockConstraintCLM x‖ ^ 2))
    (hM : 0 < M)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 4 * M ^ 2 * epsilon ≤ 1)
    (hdefect :
      ∀ x : E,
        inner ℝ x
            (physicalPrecisionDefect flatSlice physicalPrecision blockConstraintCLM a x) ≤
          YangMills.KP.catalanMajorantPartial M epsilon N * ‖x‖ ^ 2) :
    IsCoerciveCLM physicalPrecision
      (min 1 a / CP - schurCatalanBudget M epsilon) := by
  have hcoercive :
      IsCoerciveCLM
        (gaugeFixedBasePrecisionCLM flatSlice blockConstraintCLM a -
          ∑ i ∈ (Finset.univ : Finset Unit),
            (fun _ : Unit =>
              physicalPrecisionDefect flatSlice physicalPrecision blockConstraintCLM a) i)
        (min 1 a / CP -
          ∑ i ∈ (Finset.univ : Finset Unit),
            (fun _ : Unit => schurCatalanBudget M epsilon) i) := by
    refine
      isCoerciveCLM_sub_finset_of_catalanMajorantPartial_blockPoincare
        flatSlice blockConstraintCLM
        (fun _ : Unit =>
          physicalPrecisionDefect flatSlice physicalPrecision blockConstraintCLM a)
        (fun _ : Unit => M)
        (fun _ : Unit => epsilon)
        (fun _ : Unit => N)
        Finset.univ ha hCP hflat_nonneg hPoincare ?_ ?_ ?_ ?_
    · intro i hi
      exact hM
    · intro i hi
      exact hepsilon
    · intro i hi
      exact hsmall
    · intro i hi x
      exact hdefect x
  rw [physicalPrecision_eq_flat_sub_defect flatSlice physicalPrecision blockConstraintCLM a]
  simpa using hcoercive

/-- Strict pointwise positivity of a supplied physical precision from a single
Catalan-controlled physical precision defect and a positive residual
block-Poincare budget. -/
theorem inner_physicalPrecision_pos_of_catalanMajorantPartial_defect
    (flatSlice physicalPrecision : E →L[ℝ] E)
    (blockConstraintCLM : E →L[ℝ] BlockF)
    {M epsilon : ℝ} (N : ℕ) {a CP : ℝ}
    (ha : 0 ≤ a)
    (hCP : 0 < CP)
    (hflat_nonneg :
      ∀ x : E, 0 ≤ inner ℝ x (flatSlice x))
    (hPoincare :
      ∀ x : E,
        ‖x‖ ^ 2 ≤
          CP * (inner ℝ x (flatSlice x) + ‖blockConstraintCLM x‖ ^ 2))
    (hM : 0 < M)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 4 * M ^ 2 * epsilon ≤ 1)
    (hdefect :
      ∀ x : E,
        inner ℝ x
            (physicalPrecisionDefect flatSlice physicalPrecision blockConstraintCLM a x) ≤
          YangMills.KP.catalanMajorantPartial M epsilon N * ‖x‖ ^ 2)
    (hbudget : schurCatalanBudget M epsilon < min 1 a / CP) :
    ∀ x : E, x ≠ 0 → 0 < inner ℝ x (physicalPrecision x) := by
  have hpos :
      ∀ x : E, x ≠ 0 →
        0 <
          inner ℝ x
            ((gaugeFixedBasePrecisionCLM flatSlice blockConstraintCLM a -
              ∑ i ∈ (Finset.univ : Finset Unit),
                (fun _ : Unit =>
                  physicalPrecisionDefect flatSlice physicalPrecision blockConstraintCLM a) i) x) := by
    refine
      inner_sub_finset_pos_of_catalanMajorantPartial_blockPoincare
        flatSlice blockConstraintCLM
        (fun _ : Unit =>
          physicalPrecisionDefect flatSlice physicalPrecision blockConstraintCLM a)
        (fun _ : Unit => M)
        (fun _ : Unit => epsilon)
        (fun _ : Unit => N)
        Finset.univ ha hCP hflat_nonneg hPoincare ?_ ?_ ?_ ?_ ?_
    · intro i hi
      exact hM
    · intro i hi
      exact hepsilon
    · intro i hi
      exact hsmall
    · intro i hi x
      exact hdefect x
    · simpa using hbudget
  intro x hx
  rw [physicalPrecision_eq_flat_sub_defect flatSlice physicalPrecision blockConstraintCLM a]
  simpa using hpos x hx

end PhysicalPrecisionShell

end YangMills.RG
