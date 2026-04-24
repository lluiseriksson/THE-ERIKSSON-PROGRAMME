import YangMills.L8_Terminal.ClayPhysical
import YangMills.ClayCore.ConnectedCorrDecay
import YangMills.ClayCore.ClusterCorrelatorBound
import YangMills.L2_Balaban.Measurability
namespace YangMills
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
         {d : ℕ} [NeZero d]
open MeasureTheory

/-- **C116-BUNDLE**: Minimal certificate for `ClayYangMillsPhysicalStrong`
    via the constant-profile CCD path
    (`connectedCorrDecay_implies_physicalStrong_via_gen`).
    Fields:
    * `ccd`          : ConnectedCorrDecay certificate
    * `distP_nonneg` : non-negativity of plaquette distance -/
structure ConnectedCorrDecayBundle
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (Nn : ℕ) → ConcretePlaquette d Nn → ConcretePlaquette d Nn → ℝ) where
  ccd          : ConnectedCorrDecay μ plaquetteEnergy β F distP
  distP_nonneg : ∀ (Nn : ℕ) [NeZero Nn] (p q : ConcretePlaquette d Nn), 0 ≤ distP Nn p q

theorem physicalStrong_of_connectedCorrDecayBundle
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (Nn : ℕ) → ConcretePlaquette d Nn → ConcretePlaquette d Nn → ℝ}
    (h : ConnectedCorrDecayBundle μ plaquetteEnergy β F distP) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  connectedCorrDecay_implies_physicalStrong_via_gen
    μ plaquetteEnergy β F distP h.ccd h.distP_nonneg

/-- Canonical-distance bridge from the ClayCore separated connected-correlator
decay witness to the L8 physical bundle.

`ClayConnectedCorrDecay` controls pairs with `1 ≤ siteLatticeDist`.  The local
finite-distance regime is supplied by
`wilsonConnectedCorr_abs_le_two_of_unitBound`, with probability and
integrability kept explicit.  The resulting `ConnectedCorrDecayBundle` can be
sent directly to `physicalStrong_of_connectedCorrDecayBundle`. -/
noncomputable def connectedCorrDecayBundle_of_clayConnectedCorrDecay_siteDist
    {N_c d : ℕ} [NeZero N_c] [NeZero d]
    (w : ClayConnectedCorrDecay N_c)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hprob : ∀ (L : ℕ) [NeZero L],
      IsProbabilityMeasure
        (gibbsMeasure (d := d) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β))
    (hp_int : ∀ (L : ℕ) [NeZero L] (p : ConcretePlaquette d L),
      Integrable (plaquetteWilsonObs F p)
        (gibbsMeasure (d := d) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β))
    (hpq_int : ∀ (L : ℕ) [NeZero L] (p q : ConcretePlaquette d L),
      Integrable
        (fun A : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
          plaquetteWilsonObs F p A * plaquetteWilsonObs F q A)
        (gibbsMeasure (d := d) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)) :
    ConnectedCorrDecayBundle
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette d L) =>
        siteLatticeDist p.site q.site) where
  ccd := by
    refine
      { C := w.C + 2 * Real.exp w.m
        m := w.m
        hC := by nlinarith [w.hC.le, Real.exp_pos w.m]
        hm := w.hm
        bound := ?_ }
    intro L inst p q
    letI : NeZero L := inst
    haveI : IsProbabilityMeasure
        (gibbsMeasure (d := d) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β) :=
      hprob L
    by_cases hsep : (1 : ℝ) ≤ siteLatticeDist p.site q.site
    · have hw := w.hbound β hβ F hF p q hsep
      exact hw.trans (by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        nlinarith [w.hC.le, Real.exp_nonneg w.m])
    · have hlocal := wilsonConnectedCorr_abs_le_two_of_unitBound
        β F hF p q (hp_int L p) (hp_int L q) (hpq_int L p q)
      have hdist_nonneg : 0 ≤ siteLatticeDist p.site q.site :=
        siteLatticeDist_nonneg p.site q.site
      have hdist_le_one : siteLatticeDist p.site q.site ≤ 1 :=
        le_of_not_ge hsep
      have hexp_ge_one :
          1 ≤ Real.exp (w.m * (1 - siteLatticeDist p.site q.site)) := by
        rw [Real.one_le_exp_iff]
        nlinarith [w.hm.le, hdist_le_one]
      have htwo :
          2 ≤ 2 * Real.exp w.m *
              Real.exp (-w.m * siteLatticeDist p.site q.site) := by
        calc
          2 = 2 * 1 := by ring
          _ ≤ 2 * Real.exp (w.m * (1 - siteLatticeDist p.site q.site)) := by
            nlinarith
          _ = 2 * Real.exp w.m *
              Real.exp (-w.m * siteLatticeDist p.site q.site) := by
            rw [show w.m * (1 - siteLatticeDist p.site q.site) =
                w.m + (-w.m * siteLatticeDist p.site q.site) by ring,
              Real.exp_add]
            ring
      exact hlocal.trans (by
        calc
          2 ≤ 2 * Real.exp w.m *
              Real.exp (-w.m * siteLatticeDist p.site q.site) := htwo
          _ ≤ (w.C + 2 * Real.exp w.m) *
              Real.exp (-w.m * siteLatticeDist p.site q.site) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            nlinarith [w.hC.le, Real.exp_nonneg w.m])
  distP_nonneg := fun L _ p q => siteLatticeDist_nonneg p.site q.site

#print axioms connectedCorrDecayBundle_of_clayConnectedCorrDecay_siteDist

/-- Direct physical endpoint from a ClayCore separated connected-correlator
decay witness plus the explicit local probability/integrability inputs. -/
theorem physicalStrong_of_clayConnectedCorrDecay_siteDist
    {N_c d : ℕ} [NeZero N_c] [NeZero d]
    (w : ClayConnectedCorrDecay N_c)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hprob : ∀ (L : ℕ) [NeZero L],
      IsProbabilityMeasure
        (gibbsMeasure (d := d) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β))
    (hp_int : ∀ (L : ℕ) [NeZero L] (p : ConcretePlaquette d L),
      Integrable (plaquetteWilsonObs F p)
        (gibbsMeasure (d := d) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β))
    (hpq_int : ∀ (L : ℕ) [NeZero L] (p q : ConcretePlaquette d L),
      Integrable
        (fun A : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
          plaquetteWilsonObs F p A * plaquetteWilsonObs F q A)
        (gibbsMeasure (d := d) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette d L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_connectedCorrDecayBundle
    (connectedCorrDecayBundle_of_clayConnectedCorrDecay_siteDist
      w β F hβ hF hprob hp_int hpq_int)

#print axioms physicalStrong_of_clayConnectedCorrDecay_siteDist

/-- Same physical endpoint as
`physicalStrong_of_clayConnectedCorrDecay_siteDist`, with the Gibbs probability
input discharged from the standard Boltzmann-weight integrability hypothesis. -/
theorem physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable
    {N_c d : ℕ} [NeZero N_c] [NeZero d]
    (w : ClayConnectedCorrDecay N_c)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hboltz_int : ∀ (L : ℕ) [NeZero L],
      Integrable
        (fun U : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
          Real.exp (-β * wilsonAction (wilsonPlaquetteEnergy N_c) U))
        (gaugeMeasureFrom (d := d) (N := L) (sunHaarProb N_c)))
    (hp_int : ∀ (L : ℕ) [NeZero L] (p : ConcretePlaquette d L),
      Integrable (plaquetteWilsonObs F p)
        (gibbsMeasure (d := d) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β))
    (hpq_int : ∀ (L : ℕ) [NeZero L] (p q : ConcretePlaquette d L),
      Integrable
        (fun A : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
          plaquetteWilsonObs F p A * plaquetteWilsonObs F q A)
        (gibbsMeasure (d := d) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette d L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_clayConnectedCorrDecay_siteDist
    w β F hβ hF
    (fun L => gibbsMeasure_isProbability d L
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β (hboltz_int L))
    hp_int hpq_int

#print axioms physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable

/-- Same physical endpoint, with the local Wilson-observable integrability
side-conditions discharged from unit boundedness plus measurability under the
Gibbs measure.  The remaining local regularity input is now
`AEStronglyMeasurable (plaquetteWilsonObs F p)` rather than integrability of
each one- and two-point observable. -/
theorem physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_measurable
    {N_c d : ℕ} [NeZero N_c] [NeZero d]
    (w : ClayConnectedCorrDecay N_c)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hboltz_int : ∀ (L : ℕ) [NeZero L],
      Integrable
        (fun U : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
          Real.exp (-β * wilsonAction (wilsonPlaquetteEnergy N_c) U))
        (gaugeMeasureFrom (d := d) (N := L) (sunHaarProb N_c)))
    (hmeas : ∀ (L : ℕ) [NeZero L] (p : ConcretePlaquette d L),
      AEStronglyMeasurable (plaquetteWilsonObs F p)
        (gibbsMeasure (d := d) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette d L) =>
        siteLatticeDist p.site q.site) := by
  refine physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable
    w β F hβ hF hboltz_int ?_ ?_
  · intro L instL p
    letI : NeZero L := instL
    haveI : IsProbabilityMeasure
        (gibbsMeasure (d := d) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β) :=
      gibbsMeasure_isProbability d L
        (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β (hboltz_int L)
    exact plaquetteWilsonObs_integrable_of_unitBound F hF p
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)
      (hmeas L p)
  · intro L instL p q
    letI : NeZero L := instL
    haveI : IsProbabilityMeasure
        (gibbsMeasure (d := d) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β) :=
      gibbsMeasure_isProbability d L
        (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β (hboltz_int L)
    exact plaquetteWilsonObs_mul_integrable_of_unitBound F hF p q
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)
      (hmeas L p) (hmeas L q)

#print axioms physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_measurable

/-- Same physical endpoint, with local Wilson measurability derived from
measurability of the class function `F` and measurable plaquette holonomy. -/
theorem physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_observableMeasurable
    {N_c d : ℕ} [NeZero N_c] [NeZero d]
    [MeasurableInv ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)]
    [MeasurableMul₂ ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)]
    (w : ClayConnectedCorrDecay N_c)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F)
    (hboltz_int : ∀ (L : ℕ) [NeZero L],
      Integrable
        (fun U : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
          Real.exp (-β * wilsonAction (wilsonPlaquetteEnergy N_c) U))
        (gaugeMeasureFrom (d := d) (N := L) (sunHaarProb N_c))) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette d L) =>
        siteLatticeDist p.site q.site) := by
  refine
    physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_measurable
      w β F hβ hF hboltz_int ?_
  intro L instL p
  letI : NeZero L := instL
  have hobs : Measurable (plaquetteWilsonObs F p) := by
    simpa [plaquetteWilsonObs, Function.comp_def] using
      hF_meas.comp (measurable_plaquetteHolonomy (G :=
        ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)
  exact hobs.aestronglyMeasurable

#print axioms physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_observableMeasurable

/-- Concrete SU(N) form of
`physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_observableMeasurable`.

The measurable inversion/multiplication instances are now supplied by the
repository's concrete SU(N) infrastructure, so callers only provide
`Measurable F` and the Boltzmann-weight integrability input. -/
theorem physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_measurableF
    {N_c d : ℕ} [NeZero N_c] [NeZero d]
    (w : ClayConnectedCorrDecay N_c)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F)
    (hboltz_int : ∀ (L : ℕ) [NeZero L],
      Integrable
        (fun U : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
          Real.exp (-β * wilsonAction (wilsonPlaquetteEnergy N_c) U))
        (gaugeMeasureFrom (d := d) (N := L) (sunHaarProb N_c))) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette d L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_observableMeasurable
    w β F hβ hF hF_meas hboltz_int

#print axioms physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_measurableF

end YangMills
