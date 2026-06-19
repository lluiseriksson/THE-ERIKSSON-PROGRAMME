/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix

/-!
# Continuous finite-dimensional unitary matrix representations

Mathlib's `Representation` is algebraic: it does not bundle continuity or
unitarity.  This file supplies the small analytic interface needed by the
Peter-Weyl roadmap without asserting Peter-Weyl itself.

A `ContinuousUnitaryMatrixRep G ι` is a continuous monoid homomorphism from
`G` into the unitary `ι × ι` complex matrices.  Its matrix coefficients and
character are continuous functions; on a compact domain they therefore have
canonical representatives in `L²` for every finite measure.
-/

noncomputable section

open Matrix MeasureTheory

namespace YangMills.ClayCore

/-- A continuous finite-dimensional unitary matrix representation. -/
structure ContinuousUnitaryMatrixRep (G ι : Type*) [Monoid G]
    [TopologicalSpace G] [Fintype ι] [DecidableEq ι] where
  /-- The underlying unitary-valued monoid homomorphism. -/
  toMonoidHom : G →* Matrix.unitaryGroup ι ℂ
  /-- Continuity of the representation map. -/
  continuous_toFun : Continuous toMonoidHom

namespace ContinuousUnitaryMatrixRep

variable {G ι : Type*} [Group G] [TopologicalSpace G]
  [Fintype ι] [DecidableEq ι]

instance : CoeFun (ContinuousUnitaryMatrixRep G ι)
    (fun _ => G → Matrix.unitaryGroup ι ℂ) :=
  ⟨fun ρ => ρ.toMonoidHom⟩

@[simp]
theorem map_one (ρ : ContinuousUnitaryMatrixRep G ι) :
    ρ 1 = 1 :=
  ρ.toMonoidHom.map_one

@[simp]
theorem map_mul (ρ : ContinuousUnitaryMatrixRep G ι) (g h : G) :
    ρ (g * h) = ρ g * ρ h :=
  ρ.toMonoidHom.map_mul g h

/-- The algebraic representation underlying a continuous unitary matrix
representation. This is the bridge to Mathlib's representation-theory API. -/
def toRepresentation (ρ : ContinuousUnitaryMatrixRep G ι) :
    Representation ℂ G (ι → ℂ) where
  toFun g := Matrix.UnitaryGroup.toLin' (ρ g)
  map_one' := by
    rw [map_one, Matrix.UnitaryGroup.toLin'_one]
    ext
    rfl
  map_mul' g h := by
    rw [map_mul, Matrix.UnitaryGroup.toLin'_mul]
    rfl

@[simp]
theorem toRepresentation_apply (ρ : ContinuousUnitaryMatrixRep G ι)
    (g : G) (v : ι → ℂ) :
    ρ.toRepresentation g v = (ρ g : Matrix ι ι ℂ) *ᵥ v :=
  rfl

/-- Irreducibility of the underlying algebraic representation. -/
abbrev IsIrreducible (ρ : ContinuousUnitaryMatrixRep G ι) : Prop :=
  Representation.IsIrreducible ρ.toRepresentation

/-- Intertwining maps between the underlying algebraic representations. -/
abbrev IntertwiningMap {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : ContinuousUnitaryMatrixRep G ι)
    (σ : ContinuousUnitaryMatrixRep G κ) :=
  Representation.IntertwiningMap ρ.toRepresentation σ.toRepresentation

/-- An intertwiner between irreducible continuous unitary matrix
representations is either an isomorphism or zero. -/
theorem intertwiner_bijective_or_eq_zero
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : ContinuousUnitaryMatrixRep G ι)
    (σ : ContinuousUnitaryMatrixRep G κ)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (f : ρ.IntertwiningMap σ) :
    Function.Bijective f ∨ f = 0 :=
  Representation.IsIrreducible.bijective_or_eq_zero f

/-- Schur's scalar-intertwiner conclusion for a finite-dimensional irreducible
continuous unitary matrix representation over `ℂ`. -/
theorem exists_eq_smul_one_of_self_intertwiner
    (ρ : ContinuousUnitaryMatrixRep G ι) [ρ.IsIrreducible]
    (f : ρ.IntertwiningMap ρ) :
    ∃ c : ℂ, f = c • 1 := by
  have hbij :
      Function.Bijective
        (algebraMap ℂ (Representation.IntertwiningMap
          ρ.toRepresentation ρ.toRepresentation)) :=
    Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ.toRepresentation)
  rcases hbij.2 f with ⟨c, hc⟩
  exact ⟨c, by simpa using hc.symm⟩

/-- A matrix coefficient as a continuous complex-valued function. -/
def matrixCoeff (ρ : ContinuousUnitaryMatrixRep G ι) (i j : ι) : C(G, ℂ) :=
  ⟨fun g => (ρ g : Matrix ι ι ℂ) i j,
    (continuous_subtype_val.comp ρ.continuous_toFun).matrix_elem i j⟩

@[simp]
theorem matrixCoeff_apply (ρ : ContinuousUnitaryMatrixRep G ι)
    (i j : ι) (g : G) :
    ρ.matrixCoeff i j g = (ρ g : Matrix ι ι ℂ) i j :=
  rfl

/-- A matrix coefficient as a vector in `L²(G, μ)`. -/
def matrixCoeffL2 [MeasurableSpace G] [BorelSpace G] [CompactSpace G] (μ : Measure G)
    [IsFiniteMeasure μ]
    (ρ : ContinuousUnitaryMatrixRep G ι) (i j : ι) : Lp ℂ 2 μ :=
  ContinuousMap.toLp 2 μ ℂ (ρ.matrixCoeff i j)

/-- The character as a continuous complex-valued function. -/
def character (ρ : ContinuousUnitaryMatrixRep G ι) : C(G, ℂ) :=
  ⟨fun g => trace (ρ g : Matrix ι ι ℂ),
    (continuous_subtype_val.comp ρ.continuous_toFun).matrix_trace⟩

@[simp]
theorem character_apply (ρ : ContinuousUnitaryMatrixRep G ι) (g : G) :
    ρ.character g = trace (ρ g : Matrix ι ι ℂ) :=
  rfl

/-- Characters are invariant under conjugation. -/
theorem character_conj (ρ : ContinuousUnitaryMatrixRep G ι)
    (h g : G) :
    ρ.character (h * g * h⁻¹) = ρ.character g := by
  change trace (ρ (h * g * h⁻¹) : Matrix ι ι ℂ) =
    trace (ρ g : Matrix ι ι ℂ)
  rw [map_mul, map_mul]
  have hinv : ρ.toMonoidHom h⁻¹ = (ρ.toMonoidHom h)⁻¹ :=
    ρ.toMonoidHom.map_inv h
  rw [hinv]
  simpa using
    (Matrix.trace_units_conj (Unitary.toUnits (ρ h))
      (ρ g : Matrix ι ι ℂ))

/-- The character as a vector in `L²(G, μ)`. -/
def characterL2 [MeasurableSpace G] [BorelSpace G] [CompactSpace G] (μ : Measure G)
    [IsFiniteMeasure μ]
    (ρ : ContinuousUnitaryMatrixRep G ι) : Lp ℂ 2 μ :=
  ContinuousMap.toLp 2 μ ℂ ρ.character

end ContinuousUnitaryMatrixRep

end YangMills.ClayCore
