/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.RG.MarginalUVMassGap
import YangMills.L1_GibbsMeasure.TwoPlaquetteCorrelator

/-!
# The correlator bridge (C6 phase B-1): anchoring the M3 assembly to the
# Wilson measure

`docs/C6-BRIDGE-CHARTER.md`, `docs/M3-BRIDGE-AUDIT-20260713.md`.  The
2026-07-13 bridge audit found the weakest link of the M3 lane: the assembly
theorems quantify over FREE abstract sequences `covIR, Rsc`, and the
identification of `covIR + covUV_concrete` with the two-point function of the
actual SU(N) Wilson Gibbs measure was UNFORMULATED — instantiation freedom,
not a named hypothesis.  This module formulates it:

* **`CorrelatorBridge covPhys`** — the multiscale decomposition of a GIVEN
  correlator function as a structure whose field `decomposition` is the exact
  identity `covPhys t = covIR t + covUV_concrete Rsc nsc t`.  What used to be
  silent instantiation freedom is now a typed object.
* **`physical_mass_gap_of_bridge`** — the consumer: a bridge + IR bound +
  marginal flow + the `hRpoly`-shaped UV bound yields exponential decay OF
  `covPhys` ITSELF — the first statement in this development whose conclusion
  is about the (arbitrary, then physical) correlator function rather than
  about a scaffolded sum.
* **`wilsonTruncatedPlaquetteCorrelator` / `wilsonRayCorrelator`** — the
  physical anchor: the normalized truncated two-plaquette correlator of the
  genuine SU(N_c) Wilson theory (the exact expression of
  `sun_two_plaquette_correlator_bound`), and its distance-indexed form (value
  at a chosen pair of plaquettes at touch-distance `≥ 2t`; `0` beyond the
  torus diameter — on a fixed finite lattice only finitely many separations
  are realized, and the honest anchor says so in its definition rather than
  hiding it).
* **`wilsonRayCorrelator_strong_coupling_decay`** — the proved IR input in
  bridge shape: in the certified non-empty strong-coupling window, the ray
  correlator decays like `C·e^{−t}`, unconditionally.
* **`wilson_correlator_mass_gap_strong_coupling`** — NON-VACUITY OF THE WHOLE
  PIPE: the trivial bridge (`covIR := covPhys`, `Rsc := 0`) discharges every
  hypothesis of the consumer at strong coupling, so the physical ray
  correlator's mass-gap-shaped decay is obtained THROUGH the bridge, end to
  end, for the actual Wilson measure.  HONESTY: the trivial bridge carries no
  UV content — this witness shows the pipeline is inhabited and the consumer
  fires at the physical measure; it does NOT advance the weak-coupling
  problem, and the strong-coupling decay was already available directly.
* **`RegimeCoherentWilsonBridge`** — a NECESSARY INTERFACE, NOT the open
  question (docstring corrected per C6 Charter Amendment 1, external audit
  2026-07-13): the proposition is satisfiable by re-labeling the proved
  strong-coupling decay (`Rsc t 0 := a·e^{−t}`, rest `0`,
  `covIR := covPhys − a·e^{−t}`, `nsc := 1`) with ZERO renormalization-group
  content — its "nontrivial UV part" clause certifies nonvanishing, not UV
  provenance.  The honest, provenance-carrying gate is
  `RGProvenantWilsonBridge` in `YangMills/RG/CorrelatorBridgeProvenance.lean`,
  where `Rsc` is PRODUCED by a step-generated family of effective measures.
* **`wilson_mass_gap_of_regimeCoherentBridge`** — the gate's consumer: if the
  gate is ever proved, the physical mass-gap decay follows with nontrivial UV
  content.

**Honest scope.**  No new analytic estimate is proved here.  The module
converts the audit's "unformulated" verdict into named, typed hypotheses and
proves the assembly around them; the mathematics that would satisfy
`RegimeCoherentWilsonBridge` (phases B-2/B-3 of the charter) remains open.
Clay distance ~0% (<0.1%), unchanged.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open scoped BigOperators

namespace YangMills.RG

open YangMills MeasureTheory GaugeConfig

/-- **THE CORRELATOR BRIDGE.**  A multiscale decomposition of a given
correlator function `covPhys` into an IR part and the concrete UV remainder
sum of the M3 assembly.  The field `decomposition` is the identity that the
2026-07-13 audit found to be unformulated: it ties the abstract assembly data
`(covIR, Rsc, nsc)` to `covPhys` exactly. -/
structure CorrelatorBridge (covPhys : ℕ → ℝ) where
  /-- the infrared part of the decomposition -/
  covIR : ℕ → ℝ
  /-- the per-scale ultraviolet remainders -/
  Rsc : ℕ → ℕ → ℝ
  /-- the scale count consumed at separation `t` -/
  nsc : ℕ → ℕ
  /-- the exact multiscale decomposition identity -/
  decomposition : ∀ t : ℕ, covPhys t = covIR t + covUV_concrete Rsc nsc t

/-- **Bridge consumer.**  A bridge plus the marginal-coupling M3 hypothesis
package yields exponential decay of `covPhys` ITSELF: the conclusion of
`lattice_mass_gap_of_cluster_and_marginal_coupling` transported through the
decomposition identity.  This is the honest-form M3 statement: when `covPhys`
is instantiated at a physical correlator, the only remaining freedom is the
bridge structure, whose fields are named hypotheses. -/
theorem physical_mass_gap_of_bridge (covPhys : ℕ → ℝ)
    (B : CorrelatorBridge covPhys) (g : ℕ → ℝ)
    {C1 C2 ε c0 β κ₀ : ℝ}
    (hε : 0 < ε) (hc0 : 0 < c0) (hC2 : 0 ≤ C2) (hκ : 1 < κ₀)
    (hβ : 0 < β) (hpos : ∀ k, 0 < g k) (hsmall : ∀ k, β * g k < 1)
    (hrec : ∀ k, g (k + 1) = g k * (1 - β * g k))
    (hIRbound : ∀ k : ℕ, |B.covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ))))
    (hRpoly : ∀ t k : ℕ,
      |B.Rsc t k| ≤ (C2 * Real.exp (-(c0 * (t : ℝ)))) * g k ^ κ₀) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covPhys t|
        ≤ (C1 + C2 * ∑' k, g k ^ κ₀) * Real.exp (-(gap * (t : ℝ))) := by
  obtain ⟨gap, hgap, hbound⟩ :=
    lattice_mass_gap_of_cluster_and_marginal_coupling
      B.covIR B.Rsc B.nsc g hε hc0 hC2 hκ hβ hpos hsmall hrec hIRbound hRpoly
  refine ⟨gap, hgap, fun t => ?_⟩
  rw [B.decomposition t]
  exact hbound t

/-- The trivial bridge: all of `covPhys` is declared infrared, the UV part is
zero.  It witnesses that `CorrelatorBridge covPhys` is inhabited for every
`covPhys`; it carries NO ultraviolet content (the honest remark of the module
docstring). -/
noncomputable def trivialBridge (covPhys : ℕ → ℝ) : CorrelatorBridge covPhys where
  covIR := covPhys
  Rsc := fun _ _ => 0
  nsc := fun _ => 0
  decomposition := by
    intro t
    simp [covUV_concrete]

/-- Every correlator function admits a bridge (the trivial one). -/
theorem correlatorBridge_nonempty (covPhys : ℕ → ℝ) :
    Nonempty (CorrelatorBridge covPhys) :=
  ⟨trivialBridge covPhys⟩

section WilsonAnchor

variable {d N : ℕ} [NeZero d] [NeZero N]

/-- **The physical anchor object:** the normalized truncated two-plaquette
correlator of the genuine SU(N_c) Wilson theory — the exact expression bounded
by `sun_two_plaquette_correlator_bound` / `sun_lattice_exponential_clustering`,
here given a name so that bridge statements can quantify over it. -/
noncomputable def wilsonTruncatedPlaquetteCorrelator (N_c : ℕ) [NeZero N_c]
    (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) (β : ℝ)
    (p q : ConcretePlaquette d N) : ℝ :=
  (∫ A, f (plaquetteHolonomy A p) * f (plaquetteHolonomy A q) *
      Real.exp (-β * wilsonAction (fundamentalObservable N_c) A)
      ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))) /
    partitionFunction (d := d) (N := N) (sunHaarProb N_c)
      (fundamentalObservable N_c) β
  - ((∫ A, f (plaquetteHolonomy A p) *
      Real.exp (-β * wilsonAction (fundamentalObservable N_c) A)
      ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))) /
    partitionFunction (d := d) (N := N) (sunHaarProb N_c)
      (fundamentalObservable N_c) β) *
    ((∫ A, f (plaquetteHolonomy A q) *
      Real.exp (-β * wilsonAction (fundamentalObservable N_c) A)
      ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))) /
    partitionFunction (d := d) (N := N) (sunHaarProb N_c)
      (fundamentalObservable N_c) β)

/-- **The distance-indexed Wilson correlator** (`covPhys` shape): at
separation index `t`, the truncated correlator at a chosen pair of distinct
plaquettes of touch-distance `≥ 2t` if one exists, and `0` otherwise.  On a
fixed finite lattice only finitely many separations are realized; the default
`0` states this honestly inside the definition instead of hiding it in a
hypothesis. -/
noncomputable def wilsonRayCorrelator (N_c : ℕ) [NeZero N_c]
    (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) (β : ℝ) (t : ℕ) : ℝ :=
  if h : ∃ pq : ConcretePlaquette d N × ConcretePlaquette d N,
      pq.1 ≠ pq.2 ∧ 2 * t ≤ (touchGraph d N).dist pq.1 pq.2 then
    wilsonTruncatedPlaquetteCorrelator N_c f β h.choose.1 h.choose.2
  else 0

/-- **The proved IR input, in bridge shape.**  In the certified non-empty
strong-coupling window of `sun_lattice_exponential_clustering`, the Wilson ray
correlator decays exponentially in the separation index: `|covPhys t| ≤
C·e^{−1·t}`, with `C ≥ 0` uniform over all bounded measurable plaquette
observables.  (Rate `1` from the source's `e^{−dist/2}` at `dist ≥ 2t`.) -/
theorem wilsonRayCorrelator_strong_coupling_decay (N_c : ℕ) [NeZero N_c] :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, |β| ≤ β₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ),
        Measurable f → (∀ x, |f x| ≤ 1) →
      ∀ t : ℕ,
        |wilsonRayCorrelator (d := d) (N := N) N_c f β t|
          ≤ C * Real.exp (-((1 : ℝ) * (t : ℝ))) := by
  obtain ⟨β₀, hβ₀, hwin⟩ := sun_lattice_exponential_clustering (d := d) (N := N) N_c
  refine ⟨β₀, hβ₀, fun β hβ => ?_⟩
  obtain ⟨C, hC0, hbound⟩ := hwin β hβ
  refine ⟨C, hC0, fun f hfm hf t => ?_⟩
  unfold wilsonRayCorrelator
  split_ifs with h
  · obtain ⟨hpq, hdist⟩ := h.choose_spec
    have hdecay := hbound f hfm hf h.choose.1 h.choose.2 hpq
    have hfold :
        |wilsonTruncatedPlaquetteCorrelator (d := d) (N := N) N_c f β
            h.choose.1 h.choose.2|
          ≤ C * Real.exp
              (-((1 : ℝ)/2 * (((touchGraph d N).dist h.choose.1 h.choose.2 : ℕ) : ℝ))) := by
      simpa [wilsonTruncatedPlaquetteCorrelator] using hdecay
    refine hfold.trans ?_
    have hcast : (2 : ℝ) * (t : ℝ)
        ≤ (((touchGraph d N).dist h.choose.1 h.choose.2 : ℕ) : ℝ) := by
      exact_mod_cast hdist
    have hexp : Real.exp
        (-((1 : ℝ)/2 * (((touchGraph d N).dist h.choose.1 h.choose.2 : ℕ) : ℝ)))
        ≤ Real.exp (-((1 : ℝ) * (t : ℝ))) := by
      apply Real.exp_le_exp.mpr
      linarith
    exact mul_le_mul_of_nonneg_left hexp hC0
  · simpa using mul_nonneg hC0 (Real.exp_pos _).le

/-- **NON-VACUITY OF THE WHOLE PIPELINE AT THE PHYSICAL MEASURE.**  In the
certified strong-coupling window, the trivial bridge discharges EVERY
hypothesis of `physical_mass_gap_of_bridge` for the actual SU(N_c) Wilson ray
correlator, and the mass-gap-shaped conclusion follows for the physical
object, end to end through the bridge.  HONESTY (module docstring): the
trivial bridge carries no UV content; this is an inhabitation witness for the
bridge pipeline, not progress on the weak-coupling problem. -/
theorem wilson_correlator_mass_gap_strong_coupling (N_c : ℕ) [NeZero N_c] :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, |β| ≤ β₀ →
      ∀ (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ),
        Measurable f → (∀ x, |f x| ≤ 1) →
      ∃ C gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
        |wilsonRayCorrelator (d := d) (N := N) N_c f β t|
          ≤ C * Real.exp (-(gap * (t : ℝ))) := by
  obtain ⟨β₀, hβ₀, hwin⟩ :=
    wilsonRayCorrelator_strong_coupling_decay (d := d) (N := N) N_c
  refine ⟨β₀, hβ₀, fun β hβ f hfm hf => ?_⟩
  obtain ⟨C, hC0, hIR⟩ := hwin β hβ
  obtain ⟨g, βc, hβc, hpos, hsmall, hrec⟩ := exists_marginal_coupling_flow
  obtain ⟨gap, hgap, hbound⟩ :=
    physical_mass_gap_of_bridge
      (wilsonRayCorrelator (d := d) (N := N) N_c f β)
      (trivialBridge _) g
      (C1 := C) (C2 := 0) (ε := 1) (c0 := 1) (κ₀ := 2)
      one_pos one_pos le_rfl one_lt_two hβc hpos hsmall hrec
      (by
        intro k
        simpa [trivialBridge] using hIR f hfm hf k)
      (by
        intro t k
        simp [trivialBridge])
  exact ⟨C + 0 * ∑' k, g k ^ (2 : ℝ), gap, hgap, hbound⟩

/-- **A NECESSARY INTERFACE — NOT the open question** (docstring corrected
per C6 Charter Amendment 1; the statement is unchanged, retained for its
consumers).  The external audit of 2026-07-13 produced a gameability
counterexample: from the already-proved strong-coupling decay one can set
`Rsc t 0 := a·e^{−t}`, `Rsc t k := 0` for `k > 0`,
`covIR t := covPhys t − a·e^{−t}`, `nsc := 1`, and every clause below is
satisfied with ZERO renormalization-group content — the nontriviality clause
`∃ t k, Rsc t k ≠ 0` certifies nonvanishing, NOT ultraviolet provenance.  Any
honest multiscale decomposition must still factor through this shape, which
is why the interface is kept; but satisfying it proves nothing about RG
structure.  The provenance-carrying replacement gate is
`RGProvenantWilsonBridge` (`YangMills/RG/CorrelatorBridgeProvenance.lean`),
whose `Rsc` is PRODUCED by a step-generated family of effective measures
anchored at the Wilson Gibbs measure. -/
def RegimeCoherentWilsonBridge (N_c : ℕ) [NeZero N_c]
    (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) (β : ℝ) : Prop :=
  ∃ (Br : CorrelatorBridge (wilsonRayCorrelator (d := d) (N := N) N_c f β))
    (g : ℕ → ℝ) (C1 C2 ε c0 βc κ₀ : ℝ),
    0 < ε ∧ 0 < c0 ∧ 0 ≤ C2 ∧ 1 < κ₀ ∧ 0 < βc ∧
    (∀ k, 0 < g k) ∧ (∀ k, βc * g k < 1) ∧
    (∀ k, g (k + 1) = g k * (1 - βc * g k)) ∧
    (∀ k : ℕ, |Br.covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ)))) ∧
    SingleScaleUVDecay Br.Rsc g C2 c0 κ₀ ∧
    (∃ t k : ℕ, Br.Rsc t k ≠ 0)

/-- **Gate consumer.**  If a regime-coherent Wilson bridge exists, the
physical ray correlator has the mass-gap-shaped exponential decay — with
nontrivial ultraviolet content, unlike the strong-coupling witness. -/
theorem wilson_mass_gap_of_regimeCoherentBridge (N_c : ℕ) [NeZero N_c]
    (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) (β : ℝ)
    (hgate : RegimeCoherentWilsonBridge (d := d) (N := N) N_c f β) :
    ∃ C gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |wilsonRayCorrelator (d := d) (N := N) N_c f β t|
        ≤ C * Real.exp (-(gap * (t : ℝ))) := by
  obtain ⟨Br, g, C1, C2, ε, c0, βc, κ₀, hε, hc0, hC2, hκ, hβc,
    hpos, hsmall, hrec, hIR, hUV, -⟩ := hgate
  obtain ⟨gap, hgap, hbound⟩ :=
    physical_mass_gap_of_bridge
      (wilsonRayCorrelator (d := d) (N := N) N_c f β) Br g
      hε hc0 hC2 hκ hβc hpos hsmall hrec hIR
      (by simpa [SingleScaleUVDecay] using hUV)
  exact ⟨C1 + C2 * ∑' k, g k ^ κ₀, gap, hgap, hbound⟩

end WilsonAnchor

end YangMills.RG
