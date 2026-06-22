import Mathlib
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.RG.LinearAveraging

/-!
# Physical gauge cochains on the full periodic lattice

This module introduces the full-periodic cochain layer used by the P4
gauge-fixed precision/covariance path.  It deliberately works with one
coordinate for each positively oriented physical bond, and evaluates reversed
oriented edges by parallel transport through an explicit adjoint model.

No region, boundary, Hessian, propagator, or source/activity assertion is made
here.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

/-- The compact gauge group used by the physical cochain interface. -/
abbrev SUN (Nc : ℕ) := ↥(Matrix.specialUnitaryGroup (Fin Nc) ℂ)

/-- A finite-dimensional real coordinate model for `su(Nc)`.

The current formalization keeps the coordinate model abstract.  Later files can
connect this to a concrete matrix Lie algebra model without changing the
cochain API below.
-/
abbrev SUNLieCoord (Nc : ℕ) := EuclideanSpace ℝ (Fin (Nc ^ 2 - 1))

/-- Explicit adjoint-action data in the chosen `su(Nc)` coordinates. -/
structure SUNAdjointModel (Nc : ℕ) [NeZero Nc] where
  adCLM : SUN Nc → SUNLieCoord Nc →L[ℝ] SUNLieCoord Nc
  ad_one : adCLM 1 = ContinuousLinearMap.id ℝ (SUNLieCoord Nc)
  ad_mul :
    ∀ g h : SUN Nc, adCLM (g * h) = (adCLM g).comp (adCLM h)
  ad_inner :
    ∀ (g : SUN Nc) (X Y : SUNLieCoord Nc),
      inner ℝ (adCLM g X) (adCLM g Y) = inner ℝ X Y

namespace SUNAdjointModel

variable {Nc : ℕ} [NeZero Nc] (ρ : SUNAdjointModel Nc)

@[simp]
theorem ad_one_apply (X : SUNLieCoord Nc) :
    ρ.adCLM 1 X = X := by
  rw [ρ.ad_one]
  rfl

theorem ad_inv_comp (g : SUN Nc) :
    (ρ.adCLM g⁻¹).comp (ρ.adCLM g)
      = ContinuousLinearMap.id ℝ (SUNLieCoord Nc) := by
  rw [← ρ.ad_mul g⁻¹ g, inv_mul_cancel, ρ.ad_one]

theorem ad_comp_inv (g : SUN Nc) :
    (ρ.adCLM g).comp (ρ.adCLM g⁻¹)
      = ContinuousLinearMap.id ℝ (SUNLieCoord Nc) := by
  rw [← ρ.ad_mul g g⁻¹, mul_inv_cancel, ρ.ad_one]

@[simp]
theorem ad_inv_apply_ad (g : SUN Nc) (X : SUNLieCoord Nc) :
    ρ.adCLM g⁻¹ (ρ.adCLM g X) = X := by
  have h := congrArg (fun T : SUNLieCoord Nc →L[ℝ] SUNLieCoord Nc => T X)
    (ρ.ad_inv_comp g)
  simpa [ContinuousLinearMap.comp_apply] using h

@[simp]
theorem ad_apply_ad_inv (g : SUN Nc) (X : SUNLieCoord Nc) :
    ρ.adCLM g (ρ.adCLM g⁻¹ X) = X := by
  have h := congrArg (fun T : SUNLieCoord Nc →L[ℝ] SUNLieCoord Nc => T X)
    (ρ.ad_comp_inv g)
  simpa [ContinuousLinearMap.comp_apply] using h

theorem norm_ad (g : SUN Nc) (X : SUNLieCoord Nc) :
    ‖ρ.adCLM g X‖ = ‖X‖ := by
  have hsq : ‖ρ.adCLM g X‖ ^ 2 = ‖X‖ ^ 2 := by
    simpa [real_inner_self_eq_norm_sq] using ρ.ad_inner g X X
  have habs := (sq_eq_sq_iff_abs_eq_abs ‖ρ.adCLM g X‖ ‖X‖).mp hsq
  simpa [abs_of_nonneg (norm_nonneg _)] using habs

end SUNAdjointModel

/-- One physical tangent coordinate per positively oriented lattice bond. -/
abbrev PhysicalBond (d N : ℕ) [NeZero N] := FinBox d N × Fin d

/-- Physical plaquettes are the concrete oriented plaquettes of the periodic lattice. -/
abbrev PhysicalPlaquette (d N : ℕ) [NeZero N] := ConcretePlaquette d N

/-- Full-periodic site fields in `su(Nc)` coordinates. -/
abbrev PhysicalGaugeZeroCochain (d N Nc : ℕ) [NeZero N] :=
  PiLp 2 (fun _ : FinBox d N => SUNLieCoord Nc)

/-- Full-periodic one-cochains indexed by positive physical bonds. -/
abbrev PhysicalGaugeOneCochain (d N Nc : ℕ) [NeZero N] :=
  PiLp 2 (fun _ : PhysicalBond d N => SUNLieCoord Nc)

/-- Full-periodic two-cochains indexed by oriented plaquettes. -/
abbrev PhysicalGaugeTwoCochain (d N Nc : ℕ) [NeZero N] :=
  PiLp 2 (fun _ : PhysicalPlaquette d N => SUNLieCoord Nc)

/-- Gauge tangent coordinates use one independent coordinate per positive bond. -/
abbrev PhysicalGaugeTangentField (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc

/-- Forget the orientation bit and keep the physical positive bond coordinate. -/
def physicalBondOfEdge {d N : ℕ} [NeZero N] (e : ConcreteEdge d N) :
    PhysicalBond d N :=
  (e.source, e.dir)

/-- The concrete orientation reversal used by the finite-lattice instance. -/
def edgeFlip {d N : ℕ} (e : ConcreteEdge d N) : ConcreteEdge d N :=
  { e with sign := !e.sign }

@[simp]
theorem physicalBondOfEdge_edgeFlip {d N : ℕ} [NeZero N] (e : ConcreteEdge d N) :
    physicalBondOfEdge (edgeFlip e) = physicalBondOfEdge e := by
  rfl

@[simp]
theorem physicalBondOfEdge_mk_true {d N : ℕ} [NeZero N]
    (x : FinBox d N) (i : Fin d) :
    physicalBondOfEdge (ConcreteEdge.mk x i true) = (x, i) := rfl

@[simp]
theorem physicalBondOfEdge_mk_false {d N : ℕ} [NeZero N]
    (x : FinBox d N) (i : Fin d) :
    physicalBondOfEdge (ConcreteEdge.mk x i false) = (x, i) := rfl

/-- A full periodic background gauge field. -/
abbrev PhysicalGaugeBackground (d N Nc : ℕ) [NeZero d] [NeZero N] :=
  GaugeConfig d N (SUN Nc)

/-- The trivial full-periodic background. -/
def trivialPhysicalGaugeBackground (d N Nc : ℕ) [NeZero d] [NeZero N] :
    PhysicalGaugeBackground d N Nc where
  toFun := fun _ => 1
  map_reverse := by
    intro e
    simp

section OrientedValues

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Evaluate a positive-bond one-cochain on any oriented concrete edge.

For reversed edges this uses the inverse-orientation convention transported by
the background adjoint action.
-/
noncomputable def orientedOneValue (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) (e : ConcreteEdge d N) :
    SUNLieCoord Nc :=
  if e.sign then
    A (physicalBondOfEdge e)
  else
    - ρ.adCLM (U e) (A (physicalBondOfEdge e))

@[simp]
theorem orientedOneValue_pos (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) (A : PhysicalGaugeOneCochain d N Nc)
    (x : FinBox d N) (i : Fin d) :
    orientedOneValue ρ U A (ConcreteEdge.mk x i true) = A (x, i) := by
  simp [orientedOneValue]

@[simp]
theorem orientedOneValue_neg (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) (A : PhysicalGaugeOneCochain d N Nc)
    (x : FinBox d N) (i : Fin d) :
    orientedOneValue ρ U A (ConcreteEdge.mk x i false)
      = - ρ.adCLM (U (ConcreteEdge.mk x i false)) (A (x, i)) := by
  simp [orientedOneValue]

theorem orientedOneValue_reverse (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) (e : ConcreteEdge d N) :
    orientedOneValue ρ U A (edgeFlip e)
      = - ρ.adCLM (U (edgeFlip e))
          (orientedOneValue ρ U A e) := by
  cases e with
  | mk x i s =>
      cases s
      · simp only [orientedOneValue, edgeFlip, physicalBondOfEdge_mk_false,
          Bool.false_eq_true, if_false,
          ContinuousLinearMap.map_neg, neg_neg]
        change A (x, i) =
          ρ.adCLM (U (ConcreteEdge.mk x i true))
            (ρ.adCLM (U (ConcreteEdge.mk x i false)) (A (x, i)))
        have hU :
            U (ConcreteEdge.mk x i true)
              = (U (ConcreteEdge.mk x i false))⁻¹ := by
          simpa [edgeFlip] using
            (U.map_reverse (ConcreteEdge.mk x i false))
        rw [hU]
        exact (ρ.ad_inv_apply_ad
          (U (ConcreteEdge.mk x i false)) (A (x, i))).symm
      · simp [orientedOneValue, edgeFlip]

theorem orientedOneValue_add (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc) (e : ConcreteEdge d N) :
    orientedOneValue ρ U (A + B) e
      = orientedOneValue ρ U A e + orientedOneValue ρ U B e := by
  cases e with
  | mk x i s =>
      cases s
      · simp [orientedOneValue, ContinuousLinearMap.map_add]
        abel
      · simp [orientedOneValue]

theorem orientedOneValue_smul (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) (a : ℝ)
    (A : PhysicalGaugeOneCochain d N Nc) (e : ConcreteEdge d N) :
    orientedOneValue ρ U (a • A) e = a • orientedOneValue ρ U A e := by
  cases e.sign <;>
    simp [orientedOneValue, smul_neg]

end OrientedValues

section Differentials

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- The covariant zero-to-one differential on full periodic cochains. -/
noncomputable def covariantD0CLM (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) :
    PhysicalGaugeZeroCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc :=
  LinearMap.toContinuousLinearMap
    { toFun := fun φ =>
        WithLp.toLp 2 fun b : PhysicalBond d N =>
          φ b.1 - ρ.adCLM (U (ConcreteEdge.mk b.1 b.2 true)) (φ (b.1.shift b.2))
      map_add' := fun φ ψ => by
        apply PiLp.ext
        intro b
        simp only [PiLp.add_apply, ContinuousLinearMap.map_add]
        abel
      map_smul' := fun a φ => by
        apply PiLp.ext
        intro b
        simp only [PiLp.smul_apply, ContinuousLinearMap.map_smul, smul_sub,
          RingHom.id_apply] }

@[simp]
theorem covariantD0CLM_apply (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (φ : PhysicalGaugeZeroCochain d N Nc) (x : FinBox d N) (i : Fin d) :
    covariantD0CLM ρ U φ (x, i)
      = φ x - ρ.adCLM (U (ConcreteEdge.mk x i true)) (φ (x.shift i)) := rfl

/-- Prefix holonomy along the concrete boundary of a plaquette. -/
noncomputable def plaquettePrefixHolonomy (U : PhysicalGaugeBackground d N Nc)
    (p : ConcretePlaquette d N) : Fin 4 → SUN Nc
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => U (p.edges 0)
  | ⟨2, _⟩ => U (p.edges 0) * U (p.edges 1)
  | ⟨3, _⟩ => U (p.edges 0) * U (p.edges 1) * U (p.edges 2)

omit [NeZero Nc] in
@[simp]
theorem plaquettePrefixHolonomy_zero (U : PhysicalGaugeBackground d N Nc)
    (p : ConcretePlaquette d N) :
    plaquettePrefixHolonomy U p 0 = 1 := rfl

/-- The background-covariant one-to-two differential on full periodic cochains. -/
noncomputable def covariantD1CLM (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeTwoCochain d N Nc :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        WithLp.toLp 2 fun p : PhysicalPlaquette d N =>
          ∑ k : Fin 4,
            ρ.adCLM (plaquettePrefixHolonomy U p k)
              (orientedOneValue ρ U A (p.edges k))
      map_add' := fun A B => by
        apply PiLp.ext
        intro p
        simp only [PiLp.add_apply, orientedOneValue_add,
          ContinuousLinearMap.map_add, Finset.sum_add_distrib]
      map_smul' := fun a A => by
        apply PiLp.ext
        intro p
        simp only [PiLp.smul_apply, orientedOneValue_smul,
          ContinuousLinearMap.map_smul, Finset.smul_sum, RingHom.id_apply] }

theorem covariantD1CLM_apply (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) (p : ConcretePlaquette d N) :
    covariantD1CLM ρ U A p
      = ∑ k : Fin 4,
          ρ.adCLM (plaquettePrefixHolonomy U p k)
            (orientedOneValue ρ U A (p.edges k)) := rfl

/-- Full plaquette flatness for a background connection. -/
def IsFlatPhysicalBackground (U : PhysicalGaugeBackground d N Nc) : Prop :=
  ∀ p : ConcretePlaquette d N, GaugeConfig.plaquetteHolonomy U p = 1

omit [NeZero Nc] in
@[simp]
theorem trivialPhysicalGaugeBackground_flat :
    IsFlatPhysicalBackground (trivialPhysicalGaugeBackground d N Nc) := by
  intro p
  simp [GaugeConfig.plaquetteHolonomy, trivialPhysicalGaugeBackground]

/-- The formal covariant divergence, defined as the Hilbert adjoint of `D0`. -/
noncomputable def covariantDivCLM (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeZeroCochain d N Nc :=
  (covariantD0CLM ρ U).adjoint

/-- Gauge constraint used in the soft full-space gauge-fixing term. -/
noncomputable def gaugeConstraintQCLM (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeZeroCochain d N Nc :=
  covariantDivCLM ρ U

/-- The positive gauge-fixing mass operator `Q†Q`. -/
noncomputable def gaugeFixingMassCLM (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc :=
  (gaugeConstraintQCLM ρ U).adjoint.comp (gaugeConstraintQCLM ρ U)

theorem gaugeFixingMass_inner (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    inner ℝ (gaugeFixingMassCLM ρ U A) A = ‖gaugeConstraintQCLM ρ U A‖ ^ 2 := by
  rw [gaugeFixingMassCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

theorem gaugeFixingMass_inner_right (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    inner ℝ A (gaugeFixingMassCLM ρ U A) = ‖gaugeConstraintQCLM ρ U A‖ ^ 2 := by
  rw [real_inner_comm, gaugeFixingMass_inner]

theorem gaugeFixingMass_nonnegative (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    0 ≤ inner ℝ (gaugeFixingMassCLM ρ U A) A := by
  rw [gaugeFixingMass_inner]
  exact sq_nonneg _

theorem gaugeFixingMass_nonnegative_right (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    0 ≤ inner ℝ A (gaugeFixingMassCLM ρ U A) := by
  rw [gaugeFixingMass_inner_right]
  exact sq_nonneg _

/-- The background Hodge operator `D1†D1 + D0D0†` on physical one-cochains. -/
noncomputable def backgroundGaugeHodgeK0CLM (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc :=
  (covariantD1CLM ρ U).adjoint.comp (covariantD1CLM ρ U)
    + gaugeFixingMassCLM ρ U

theorem backgroundGaugeHodgeK0_inner (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    inner ℝ (backgroundGaugeHodgeK0CLM ρ U A) A
      = ‖covariantD1CLM ρ U A‖ ^ 2 + ‖gaugeConstraintQCLM ρ U A‖ ^ 2 := by
  rw [backgroundGaugeHodgeK0CLM, ContinuousLinearMap.add_apply, inner_add_left,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    gaugeFixingMass_inner, real_inner_self_eq_norm_sq]

theorem backgroundGaugeHodgeK0_inner_right (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    inner ℝ A (backgroundGaugeHodgeK0CLM ρ U A)
      = ‖covariantD1CLM ρ U A‖ ^ 2 + ‖gaugeConstraintQCLM ρ U A‖ ^ 2 := by
  rw [real_inner_comm, backgroundGaugeHodgeK0_inner]

theorem backgroundGaugeHodgeK0_nonnegative (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    0 ≤ inner ℝ (backgroundGaugeHodgeK0CLM ρ U A) A := by
  rw [backgroundGaugeHodgeK0_inner]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem backgroundGaugeHodgeK0_nonnegative_right (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    0 ≤ inner ℝ A (backgroundGaugeHodgeK0CLM ρ U A) := by
  rw [backgroundGaugeHodgeK0_inner_right]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The flat Hodge operator at the trivial background. -/
noncomputable def flatGaugeHodgeK0CLM (d N Nc : ℕ) [NeZero d] [NeZero N]
    [NeZero Nc] (ρ : SUNAdjointModel Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc :=
  backgroundGaugeHodgeK0CLM ρ (trivialPhysicalGaugeBackground d N Nc)

theorem flatGaugeHodgeK0_nonnegative (ρ : SUNAdjointModel Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    0 ≤ inner ℝ (flatGaugeHodgeK0CLM d N Nc ρ A) A := by
  simpa [flatGaugeHodgeK0CLM] using
    backgroundGaugeHodgeK0_nonnegative ρ
      (trivialPhysicalGaugeBackground d N Nc) A

theorem flatGaugeHodgeK0_nonnegative_right (ρ : SUNAdjointModel Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    0 ≤ inner ℝ A (flatGaugeHodgeK0CLM d N Nc ρ A) := by
  simpa [flatGaugeHodgeK0CLM] using
    backgroundGaugeHodgeK0_nonnegative_right ρ
      (trivialPhysicalGaugeBackground d N Nc) A

end Differentials

section FlatBlockConstraint

variable {d L N' Nc : ℕ} [NeZero L] [NeZero N']

/-- Fine physical one-cochains used by the flat block constraint. -/
abbrev FinePhysicalOneCochain (d L N' Nc : ℕ) [NeZero L] [NeZero N'] :=
  PhysicalGaugeOneCochain d (L * N') Nc

/-- Coarse physical one-cochains used by the flat block constraint. -/
abbrev CoarsePhysicalOneCochain (d N' Nc : ℕ) [NeZero N'] :=
  PhysicalGaugeOneCochain d N' Nc

/-- The flat block constraint obtained by averaging positive-bond fields. -/
noncomputable def flatBlockConstraintQCLM (L N' : ℕ) [NeZero L] [NeZero N'] :
    FinePhysicalOneCochain d L N' Nc →L[ℝ] CoarsePhysicalOneCochain d N' Nc :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        WithLp.toLp 2 fun b : PhysicalBond d N' =>
          linAvg L N' (fun e : ConcreteEdge d (L * N') => A (physicalBondOfEdge e))
            (ConcreteEdge.mk b.1 b.2 true)
      map_add' := fun A B => by
        apply PiLp.ext
        intro b
        simpa only [PiLp.add_apply] using
          (linAvg_add L N'
            (fun e : ConcreteEdge d (L * N') => A (physicalBondOfEdge e))
            (fun e : ConcreteEdge d (L * N') => B (physicalBondOfEdge e))
            (ConcreteEdge.mk b.1 b.2 true))
      map_smul' := fun a A => by
        apply PiLp.ext
        intro b
        simpa only [PiLp.smul_apply] using
          (linAvg_smul L N' a
            (fun e : ConcreteEdge d (L * N') => A (physicalBondOfEdge e))
            (ConcreteEdge.mk b.1 b.2 true)) }

@[simp]
theorem flatBlockConstraintQCLM_apply
    (A : FinePhysicalOneCochain d L N' Nc) (b : PhysicalBond d N') :
    flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A b
      = linAvg L N'
          (fun e : ConcreteEdge d (L * N') => A (physicalBondOfEdge e))
          (ConcreteEdge.mk b.1 b.2 true) := rfl

end FlatBlockConstraint

end YangMills.RG
