/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.IntegerThermodynamicLimit
import YangMills.Continuum.Scale

/-!
# Scale-indexed embeddings of a deliberately minimal test algebra

The continuum-facing object in this campaign is a type of tests together with
explicit maps into the repository's genuine integer-coordinate local
observables.  No completion or continuum field algebra is postulated.

The operation record intentionally carries operations but no algebraic laws.
The limit-stability theorems need only the explicit compatibility equalities
below.  A later richer test algebra may supply laws without changing the
transport layer.
-/

namespace YangMills.Continuum

open YangMills
open Filter Topology

universe u v

variable {A : Type v}
variable {d : ℕ} [NeZero d]
variable {G : Type u} [Group G] [MeasurableSpace G]

/-- The operations used by the C0 transport theorems. -/
structure MinimalTestAlgebra (A : Type v) (d : ℕ) where
  one : A
  add : A → A → A
  smul : ℝ → A → A
  mul : A → A → A
  translate : (Fin d → ℤ) → A → A

/-- An explicit embedding of each test at each lattice scale. -/
structure ObservableEmbedding
    (A : Type v) (d : ℕ) [NeZero d]
    (G : Type u) [Group G] [MeasurableSpace G] where
  atScale : ℕ → A → IntegerLocalObservable.{u, 0} d G

/-- A one-point cylinder: a fixed integer local observable is anchored at a
declared physical point. -/
structure PointCylinder
    (d : ℕ) [NeZero d]
    (G : Type u) [Group G] [MeasurableSpace G] where
  point : Fin d → ℝ
  observable : IntegerLocalObservable.{u, 0} d G

/-- The canonical integer anchor of a physical point at spacing `aₙ`. -/
noncomputable def latticeAnchor
    (scale : ScaleSequence) (n : ℕ) (x : Fin d → ℝ) :
    Fin d → ℤ :=
  fun j => ⌊x j / scale.spacing n⌋

/-- The canonical point-cylinder embedding by the coordinate map
`x ↦ ⌊x/aₙ⌋`. -/
noncomputable def pointCylinderEmbedding
    (scale : ScaleSequence) :
    ObservableEmbedding (PointCylinder d G) d G where
  atScale := fun n F =>
    latticeAnchor scale n F.point +ᵥ F.observable

/-- The precise anti-collapse obligation for physical anchors.  C0 names it
separately because its proof requires a floor-separation estimate; the
one-point convergence theorem below does not assume it. -/
def EventuallySeparatesAnchors (scale : ScaleSequence) : Prop :=
  ∀ ⦃x y : Fin d → ℝ⦄, x ≠ y →
    ∀ᶠ n in atTop, latticeAnchor scale n x ≠ latticeAnchor scale n y

/-- Exact preservation of the operations needed for limit transport. -/
structure AlgebraCompatibility
    (T : MinimalTestAlgebra A d)
    (E : ObservableEmbedding A d G) : Prop where
  map_one : ∀ n,
    E.atScale n T.one =
      IntegerLocalObservable.const (d := d) (G := G) 1
  map_add : ∀ n F H,
    E.atScale n (T.add F H) =
      IntegerLocalObservable.add (E.atScale n F) (E.atScale n H)
  map_smul : ∀ n c F,
    E.atScale n (T.smul c F) =
      IntegerLocalObservable.smul c (E.atScale n F)
  map_mul : ∀ n F H,
    E.atScale n (T.mul F H) =
      IntegerLocalObservable.mul (E.atScale n F) (E.atScale n H)
  map_translate : ∀ n z F,
    E.atScale n (T.translate z F) = z +ᵥ E.atScale n F

/-- Compatibility of a chosen positive cone of tests with pointwise
nonnegativity of the embedded discrete kernels. -/
structure OrderCompatibility
    (nonnegative : A → Prop)
    (E : ObservableEmbedding A d G) : Prop where
  map_nonnegative : ∀ n F, nonnegative F →
    ∀ x, 0 ≤ (E.atScale n F).kernel x

/-- A typed geometric scaling obligation.  A physical test radius is not
obtained merely by naming a spacing: its discrete support radius must scale
to the declared physical radius.  CONTINUUM-C0 defines this obligation but
does not claim it for the identity example. -/
structure GeometricScalingCompatibility
    (scale : ScaleSequence)
    (E : ObservableEmbedding A d G) where
  latticeRadius : ℕ → A → ℕ
  physicalRadius : A → ℝ
  scaledRadius_tendsto : ∀ F,
    Tendsto
      (fun n => scale.spacing n * (latticeRadius n F : ℝ))
      atTop (𝓝 (physicalRadius F))

/-- A real reflection interface.  It is deliberately separate from the test
algebra because the current repository's complex half-chain reflection
positivity and its real thermodynamic SU(2) state have no proved adapter. -/
structure ReflectionCompatibility
    (E : ObservableEmbedding A d G) where
  reflect : A → A
  positiveHalf : A → Prop
  positiveHalf_nonempty : ∃ F, positiveHalf F
  reflect_involutive : Function.Involutive reflect
  discreteReflect :
    ℕ → IntegerLocalObservable.{u, 0} d G →
      IntegerLocalObservable.{u, 0} d G
  discreteReflect_involutive : ∀ n, Function.Involutive (discreteReflect n)
  map_reflect : ∀ n F,
    E.atScale n (reflect F) = discreteReflect n (E.atScale n F)

/-- The native integer local-observable algebra, useful both as a consumer and
as a nonempty test algebra for the compiled example. -/
noncomputable def integerObservableTestAlgebra :
    MinimalTestAlgebra (IntegerLocalObservable.{u, 0} d G) d where
  one := IntegerLocalObservable.const (d := d) (G := G) 1
  add := IntegerLocalObservable.add
  smul := IntegerLocalObservable.smul
  mul := IntegerLocalObservable.mul
  translate := fun z O => z +ᵥ O

/-- Identity embeddings: the same integer local test is evaluated at every
scale.  This is intentionally minimal and does not claim physical rescaling. -/
def identityObservableEmbedding :
    ObservableEmbedding (IntegerLocalObservable.{u, 0} d G) d G where
  atScale := fun _ O => O

theorem identityObservableEmbedding_compatible :
    AlgebraCompatibility
      (integerObservableTestAlgebra (d := d) (G := G))
      (identityObservableEmbedding (d := d) (G := G)) := by
  constructor <;> intros <;> rfl

end YangMills.Continuum
