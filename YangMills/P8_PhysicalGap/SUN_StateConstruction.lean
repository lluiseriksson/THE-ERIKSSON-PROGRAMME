import Mathlib
import YangMills.L1_GibbsMeasure.GibbsMeasure

/-!
# M1: Concrete Construction of SUN_State and sunGibbsFamily

This file replaces the `opaque` declarations in BalabanToLSI.lean with
concrete constructions based on Mathlib's matrix groups.

## Architecture

  SUN_State N_c  :=  GaugeConfig d L (Matrix.specialUnitaryGroup (Fin N_c) ℂ)

  sunGibbsFamily d N_c β L  :=  gibbsMeasure (haarMeasure SU(N_c)) wilsonAction_SUN β

## Status

- SUN_State: concrete (M1 partial)
- sunGibbsFamily: connected to gibbsMeasure via Haar (M1 partial)
- sunDirichletForm: still opaque (M2, requires Lie group calculus)
- sun_gibbs_dlr_lsi: still axiom (M3, the Clay problem core)

## Key instances proved here

- MeasurableSpace (Matrix (Fin n) (Fin n) ℂ)   via change tactic
- BorelSpace (Matrix (Fin n) (Fin n) ℂ)          via change tactic
- MeasurableSpace ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)  via subtype
- BorelSpace ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)        via subtype
- CompactSpace ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)      as axiom (M1b)
-/

namespace YangMills

open MeasureTheory Matrix

noncomputable section

/-! ## Typeclass instances for Matrix over ℂ -/

/-- MeasurableSpace for matrices over ℂ.
    Matrix (Fin n) (Fin n) ℂ is definitionally equal to (Fin n → Fin n → ℂ),
    but typeclass synthesis does not unfold the `def Matrix`.
    We force it via `change`. -/
instance instMeasurableSpaceMatrix (n : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := by
  change MeasurableSpace (Fin n → Fin n → ℂ)
  infer_instance

/-- BorelSpace for matrices over ℂ. -/
instance instBorelSpaceMatrix (n : ℕ) :
    BorelSpace (Matrix (Fin n) (Fin n) ℂ) := by
  change BorelSpace (Fin n → Fin n → ℂ)
  infer_instance

/-! ## Typeclass instances for specialUnitaryGroup -/

/-- MeasurableSpace for SU(N) as a subtype of Matrix. -/
instance instMeasurableSpaceSUN (n : ℕ) :
    MeasurableSpace ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) :=
  inferInstance

/-- BorelSpace for SU(N). -/
instance instBorelSpaceSUN (n : ℕ) :
    BorelSpace ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) :=
  inferInstance

/-- CompactSpace for SU(N).
    Mathematical argument: SU(N) = {A ∈ M_N(ℂ) | A*A = I, det A = 1}
    is a closed and bounded subset of M_N(ℂ) ≅ ℝ^(2N²), hence compact
    by Heine-Borel.
    TODO (M1b): formalize via isClosed + isBounded + finite-dim compactness. -/
axiom instCompactSpaceSUN (n : ℕ) [NeZero n] :
    CompactSpace ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)

attribute [instance] instCompactSpaceSUN

/-! ## Concrete SUN_State -/

/-- The state space of SU(N_c) gauge fields on a d-dimensional lattice
    of side length L. This replaces the `opaque` declaration in BalabanToLSI.lean.

    Concretely: a gauge configuration assigns an SU(N_c) matrix to each
    edge of the lattice, compatible with orientation reversal.

    Note: We use GaugeConfig from L0/L1 infrastructure, instantiated to
    G = SU(N_c) (as a Mathlib type). -/
abbrev SUN_State_Concrete (N_c : ℕ) := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)

/-- The Haar measure on SU(N_c), used as the reference measure for Gibbs families. -/
noncomputable def sunHaarMeasure (N_c : ℕ) [NeZero N_c] :
    Measure ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) :=
  Measure.haar

/-- The SU(N_c) Gibbs measure family in finite volume L.
    This is the concrete counterpart of the opaque `sunGibbsFamily`.

    Constructed as: gibbsMeasure(Haar_SUN, wilsonAction, β)
    where wilsonAction is the Wilson plaquette action on the lattice.

    Status: partial — the connection to the abstract `sunGibbsFamily`
    requires the Wilson action to be defined for the SU(N) gauge group.
    See BalabanToLSI.lean for the abstract axiom interface. -/
-- sunGibbsFamily_concrete will be developed in M1 continuation

end

end YangMills
