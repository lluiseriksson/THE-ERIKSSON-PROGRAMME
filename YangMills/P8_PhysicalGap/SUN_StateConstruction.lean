import Mathlib
import YangMills.P8_PhysicalGap.SUN_Compact
import YangMills.L1_GibbsMeasure.GibbsMeasure
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance

/-!
# M1: Concrete Construction of SUN_State and sunGibbsFamily

Replaces the `opaque` declarations in BalabanToLSI.lean with
concrete constructions based on Mathlib's matrix groups.

## Key results

- `SUN_State_Concrete N_c` := `↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)`
- `sunHaarProb N_c`         := `haarMeasure univ` — a probability measure on SU(N_c)
- `sunGibbsFamily_concrete` := `gibbsMeasure sunHaarProb wilsonAction β`

## Typeclass instances proved

| Instance | Method |
|---|---|
| `MeasurableSpace (Matrix (Fin n) (Fin n) ℂ)` | `change` tactic |
| `BorelSpace (Matrix (Fin n) (Fin n) ℂ)` | `change` tactic |
| `MeasurableSpace ↥(specialUnitaryGroup (Fin n) ℂ)` | subtype |
| `BorelSpace ↥(specialUnitaryGroup (Fin n) ℂ)` | subtype |
| `CompactSpace ↥(specialUnitaryGroup (Fin n) ℂ)` | axiom (M1b) |
| `IsProbabilityMeasure (sunHaarProb N_c)` | `haarMeasure_self` |

## Axioms

- `instCompactSpaceSUN` (M1b): SU(N) is closed+bounded in M_N(ℂ), hence compact by Heine-Borel.
-/

namespace YangMills

open MeasureTheory Matrix TopologicalSpace

noncomputable section

/-! ## Typeclass instances for Matrix over ℂ

`Matrix` is a `def`, not an `abbrev`, so typeclass synthesis does not
unfold it automatically. We use the `change` tactic to reduce to the
Pi type `Fin n → Fin n → ℂ` where instances exist. -/

instance instMeasurableSpaceMatrix (n : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := by
  change MeasurableSpace (Fin n → Fin n → ℂ); infer_instance

instance instBorelSpaceMatrix (n : ℕ) :
    BorelSpace (Matrix (Fin n) (Fin n) ℂ) := by
  change BorelSpace (Fin n → Fin n → ℂ); infer_instance

/-! ## Typeclass instances for SU(N) -/

instance instMeasurableSpaceSUN (n : ℕ) :
    MeasurableSpace ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) := inferInstance

instance instBorelSpaceSUN (n : ℕ) :
    BorelSpace ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) := inferInstance

/-- CompactSpace for SU(N). Proved in SUN_Compact.lean (M1b).
    Strategy: SU(N) ⊆ Pi(closedBall 0 1) [entry_norm_bound_of_unitary]
              SU(N) is closed [isClosed_unitary + continuous det]
              closed ⊆ compact → compact [IsCompact.of_isClosed_subset] -/
-- instCompactSpaceSUN_concrete is provided by SUN_Compact.lean
-- Re-export as the canonical instance name:
alias instCompactSpaceSUN := instCompactSpaceSUN_concrete

/-! ## SUN_State: the concrete gauge group -/

/-- The concrete state space: SU(N_c) matrices. -/
abbrev SUN_State_Concrete (N_c : ℕ) :=
  ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)

/-! ## Haar probability measure on SU(N_c)

`Measure.haar` is not automatically `IsProbabilityMeasure`.
We use `haarMeasure K₀` with `K₀ = univ` (valid since SU(N) is compact),
and `haarMeasure_self` gives `μ(K₀) = 1`, hence `μ(univ) = 1`. -/

/-- The whole group as a `PositiveCompacts` set (valid since SU(N) is compact). -/
def sunPositiveCompacts (N_c : ℕ) [NeZero N_c] :
    PositiveCompacts ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by simp [interior_univ]

/-- The normalized Haar probability measure on SU(N_c).
    `haarMeasure_self` ensures μ(univ) = 1. -/
noncomputable def sunHaarProb (N_c : ℕ) [NeZero N_c] :
    Measure ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) :=
  Measure.haarMeasure (sunPositiveCompacts N_c)

/-- `sunHaarProb` is a probability measure. -/
instance instIsProbabilityMeasureSUN (N_c : ℕ) [NeZero N_c] :
    IsProbabilityMeasure (sunHaarProb N_c) := by
  constructor
  have := @Measure.haarMeasure_self
    ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) _ _ _ _ _
    (sunPositiveCompacts N_c)
  simp [sunHaarProb, sunPositiveCompacts] at this ⊢
  exact this

/-! ## sunGibbsFamily: concrete connection to L1

`finBoxGeometry` (FiniteLatticeGeometryInstance.lean) provides
`FiniteLatticeGeometry d L G` for any `[Group G]`, so it applies
directly to `G = SUN_State_Concrete N_c`.

The concrete Gibbs family is:
  `sunGibbsFamily_concrete d N_c L β plaquetteEnergy`
  = `gibbsMeasure sunHaarProb wilsonAction_SUN β` -/

/-- Concrete Gibbs measure for SU(N_c) Yang-Mills on a d×L^(d-1) lattice.

  Parameters:
  - `d`              : spacetime dimension
  - `N_c`            : gauge group rank (SU(N_c))
  - `L`              : lattice side length
  - `β`              : inverse coupling
  - `plaquetteEnergy`: single-plaquette energy function G → ℝ

  The `finBoxGeometry` instance (L0) provides the lattice combinatorics.
  `sunHaarProb` provides the reference probability measure.

  Note: connecting to the abstract `sunGibbsFamily` in BalabanToLSI.lean
  requires identifying `SUN_State N_c` with `SUN_State_Concrete N_c`
  and matching the volume parameter L. -/
noncomputable def sunGibbsFamily_concrete
    (d N_c L : ℕ) [NeZero d] [NeZero L] [NeZero N_c]
    (β : ℝ) (plaquetteEnergy : SUN_State_Concrete N_c → ℝ) :
    Measure (GaugeConfig d L (SUN_State_Concrete N_c)) :=
  gibbsMeasure (d := d) (N := L) (sunHaarProb N_c) plaquetteEnergy β

/-- `sunGibbsFamily_concrete` is a probability measure (given integrability). -/
theorem sunGibbsFamily_isProbability
    (d N_c L : ℕ) [NeZero d] [NeZero L] [NeZero N_c]
    (β : ℝ) (plaquetteEnergy : SUN_State_Concrete N_c → ℝ)
    (h_int : Integrable
      (fun U : GaugeConfig d L (SUN_State_Concrete N_c) =>
        Real.exp (-β * wilsonAction plaquetteEnergy U))
      (gaugeMeasureFrom (d := d) (N := L) (sunHaarProb N_c))) :
    IsProbabilityMeasure
      (sunGibbsFamily_concrete d N_c L β plaquetteEnergy) :=
  gibbsMeasure_isProbability d L (sunHaarProb N_c) plaquetteEnergy β h_int

end

end YangMills
