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

/-- Boltzmann-weight integrability for the concrete Wilson plaquette energy on
finite SU(N) gauge lattices.

The proof uses the existing uniform bound on `wilsonPlaquetteEnergy N_c` and
the finiteness of the plaquette set to bound `exp (-β * wilsonAction ...)` on
the probability gauge measure. -/
theorem wilsonPlaquetteEnergy_boltzmann_integrable
    {N_c d L : ℕ} [NeZero N_c] [NeZero d] [NeZero L]
    (β : ℝ) (hβ : 0 ≤ β) :
    Integrable
      (fun U : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
        Real.exp (-β * wilsonAction (wilsonPlaquetteEnergy N_c) U))
      (gaugeMeasureFrom (d := d) (N := L) (sunHaarProb N_c)) := by
  obtain ⟨M, hM⟩ := wilsonPlaquetteEnergy_bounded N_c
  let B : ℝ := (Fintype.card (ConcretePlaquette d L) : ℝ) * max M 0
  have h_lower :
      ∀ U : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
        -B ≤ wilsonAction (wilsonPlaquetteEnergy N_c) U := by
    intro U
    unfold wilsonAction
    dsimp [B]
    calc
      -((Fintype.card (ConcretePlaquette d L) : ℝ) * max M 0)
          = ∑ _p : ConcretePlaquette d L, -(max M 0) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ p : ConcretePlaquette d L,
            wilsonPlaquetteEnergy N_c (GaugeConfig.plaquetteHolonomy U p) := by
            apply Finset.sum_le_sum
            intro p _
            have hp_abs := hM (GaugeConfig.plaquetteHolonomy U p)
            have hp_abs' :
                |wilsonPlaquetteEnergy N_c (GaugeConfig.plaquetteHolonomy U p)|
                  ≤ max M 0 :=
              le_trans hp_abs (le_max_left M 0)
            exact (abs_le.mp hp_abs').1
  have hbound :
      ∀ U : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
        Real.exp (-β * wilsonAction (wilsonPlaquetteEnergy N_c) U)
          ≤ Real.exp (β * B) := by
    intro U
    apply Real.exp_le_exp.mpr
    have hm := h_lower U
    have hmul : β * (-B) ≤ β * wilsonAction (wilsonPlaquetteEnergy N_c) U :=
      mul_le_mul_of_nonneg_left hm hβ
    nlinarith
  have haction_meas : Measurable
      (fun U : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
        wilsonAction (wilsonPlaquetteEnergy N_c) U) :=
    measurable_wilsonAction (wilsonPlaquetteEnergy N_c)
      (wilsonPlaquetteEnergy_continuous N_c).measurable
  have hmeas : AEStronglyMeasurable
      (fun U : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
        Real.exp (-β * wilsonAction (wilsonPlaquetteEnergy N_c) U))
      (gaugeMeasureFrom (d := d) (N := L) (sunHaarProb N_c)) := by
    have hm : Measurable
        (fun U : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
          Real.exp (-β * wilsonAction (wilsonPlaquetteEnergy N_c) U)) := by
      exact Real.measurable_exp.comp (haction_meas.const_mul (-β))
    exact hm.aestronglyMeasurable
  refine Integrable.of_bound hmeas (Real.exp (β * B)) ?_
  exact ae_of_all _ fun U => by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact hbound U

#print axioms wilsonPlaquetteEnergy_boltzmann_integrable

/-- Concrete SU(N) physical bridge with the Boltzmann integrability side-condition
discharged from the bounded Wilson plaquette energy. -/
theorem physicalStrong_of_clayConnectedCorrDecay_siteDist_measurableF
    {N_c d : ℕ} [NeZero N_c] [NeZero d]
    (w : ClayConnectedCorrDecay N_c)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette d L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_measurableF
    w β F hβ hF hF_meas
    (fun _L => wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le)

#print axioms physicalStrong_of_clayConnectedCorrDecay_siteDist_measurableF

end YangMills
