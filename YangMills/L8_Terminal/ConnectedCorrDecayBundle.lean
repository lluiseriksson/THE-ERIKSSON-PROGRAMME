import YangMills.L8_Terminal.ClayPhysical
import YangMills.ClayCore.ConnectedCorrDecay
import YangMills.ClayCore.ClusterCorrelatorBound
import YangMills.ClayCore.ClusterRpowBridge
import YangMills.ClayCore.LatticeAnimalF3Bridge
import YangMills.ClayCore.WilsonHaarBaseCase
import YangMills.ClayCore.ZeroMeanCancellation
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

/-- Direct bridge from the analytic `ClusterCorrelatorBound` front to the
concrete SU(N) physical endpoint at fixed `β` and observable `F`.

This composes the existing `ClusterCorrelatorBound → ClayYangMillsMassGap`
constructor with the cleaned-up L8 bridge.  Once F1/F2/F3 supply
`ClusterCorrelatorBound`, the remaining finite-volume regularity needed for the
physical endpoint is just `Measurable F` and `|F| ≤ 1`. -/
theorem physicalStrong_of_clusterCorrelatorBound_siteDist_measurableF
    {N_c d : ℕ} [NeZero N_c] [NeZero d]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_clust : ℝ) (hC : 0 < C_clust)
    (hccb : ClusterCorrelatorBound N_c r C_clust)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette d L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_clayConnectedCorrDecay_siteDist_measurableF
    (ClayConnectedCorrDecay.ofClayMassGap
      (clay_massGap_large_beta N_c r hr_pos hr_lt1 C_clust hC hccb))
    β F hβ hF hF_meas

#print axioms physicalStrong_of_clusterCorrelatorBound_siteDist_measurableF

/-- Physical-dimension specialization of the direct
`ClusterCorrelatorBound → PhysicalStrong` endpoint.

This keeps the analytic input global, but fixes the terminal physical distance
profile to `physicalClayDimension = 4`, the Clay spacetime dimension recorded
in `ConnectingClusterCount.lean`. -/
theorem physicalStrong_of_clusterCorrelatorBound_physicalClayDimension_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_clust : ℝ) (hC : 0 < C_clust)
    (hccb : ClusterCorrelatorBound N_c r C_clust)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_clusterCorrelatorBound_siteDist_measurableF
    (d := physicalClayDimension) r hr_pos hr_lt1 C_clust hC hccb
    β F hβ hF hF_meas

#print axioms physicalStrong_of_clusterCorrelatorBound_physicalClayDimension_siteDist_measurableF

/-- Physical `d = 4` separated correlator bound packaged as a full
`ConnectedCorrDecayBundle`.

The separated regime is supplied by `PhysicalClusterCorrelatorBound`; the local
short-distance regime is supplied by the standard unit-bound estimate. -/
noncomputable def connectedCorrDecayBundle_of_physicalClusterCorrelatorBound_siteDist
    {N_c : ℕ} [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_clust : ℝ) (hC : 0 < C_clust)
    (hpcb : PhysicalClusterCorrelatorBound N_c r C_clust)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hprob : ∀ (L : ℕ) [NeZero L],
      IsProbabilityMeasure
        (gibbsMeasure (d := physicalClayDimension) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β))
    (hp_int : ∀ (L : ℕ) [NeZero L]
      (p : ConcretePlaquette physicalClayDimension L),
      Integrable (plaquetteWilsonObs F p)
        (gibbsMeasure (d := physicalClayDimension) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β))
    (hpq_int : ∀ (L : ℕ) [NeZero L]
      (p q : ConcretePlaquette physicalClayDimension L),
      Integrable
        (fun A : GaugeConfig physicalClayDimension L
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
          plaquetteWilsonObs F p A * plaquetteWilsonObs F q A)
        (gibbsMeasure (d := physicalClayDimension) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)) :
    ConnectedCorrDecayBundle
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) where
  ccd := by
    let m := kpParameter r
    refine
      { C := C_clust + 2 * Real.exp m
        m := m
        hC := by nlinarith [hC.le, Real.exp_pos m]
        hm := kpParameter_pos hr_pos hr_lt1
        bound := ?_ }
    intro L inst p q
    letI : NeZero L := inst
    haveI : IsProbabilityMeasure
        (gibbsMeasure (d := physicalClayDimension) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β) :=
      hprob L
    by_cases hsep : (1 : ℝ) ≤ siteLatticeDist p.site q.site
    · have hw := hpcb β hβ F hF p q hsep
      exact hw.trans (by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        nlinarith [hC.le, Real.exp_nonneg m])
    · have hlocal := wilsonConnectedCorr_abs_le_two_of_unitBound
        β F hF p q (hp_int L p) (hp_int L q) (hpq_int L p q)
      have hdist_le_one : siteLatticeDist p.site q.site ≤ 1 :=
        le_of_not_ge hsep
      have hexp_ge_one :
          1 ≤ Real.exp (m * (1 - siteLatticeDist p.site q.site)) := by
        rw [Real.one_le_exp_iff]
        nlinarith [(kpParameter_pos hr_pos hr_lt1).le, hdist_le_one]
      have htwo :
          2 ≤ 2 * Real.exp m *
              Real.exp (-m * siteLatticeDist p.site q.site) := by
        calc
          2 = 2 * 1 := by ring
          _ ≤ 2 * Real.exp (m * (1 - siteLatticeDist p.site q.site)) := by
            nlinarith
          _ = 2 * Real.exp m *
              Real.exp (-m * siteLatticeDist p.site q.site) := by
            rw [show m * (1 - siteLatticeDist p.site q.site) =
                m + (-m * siteLatticeDist p.site q.site) by ring,
              Real.exp_add]
            ring
      exact hlocal.trans (by
        calc
          2 ≤ 2 * Real.exp m *
              Real.exp (-m * siteLatticeDist p.site q.site) := htwo
          _ ≤ (C_clust + 2 * Real.exp m) *
              Real.exp (-m * siteLatticeDist p.site q.site) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            nlinarith [hC.le, Real.exp_nonneg m])
  distP_nonneg := fun L _ p q => siteLatticeDist_nonneg p.site q.site

#print axioms connectedCorrDecayBundle_of_physicalClusterCorrelatorBound_siteDist

/-- Direct physical endpoint from the four-dimensional physical correlator
bound. -/
theorem physicalStrong_of_physicalClusterCorrelatorBound_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_clust : ℝ) (hC : 0 < C_clust)
    (hpcb : PhysicalClusterCorrelatorBound N_c r C_clust)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_connectedCorrDecayBundle
    (connectedCorrDecayBundle_of_physicalClusterCorrelatorBound_siteDist
      r hr_pos hr_lt1 C_clust hC hpcb β F hβ hF
      (fun L => gibbsMeasure_isProbability physicalClayDimension L
        (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
        (wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le))
      (fun L instL p => by
        letI : NeZero L := instL
        haveI : IsProbabilityMeasure
            (gibbsMeasure (d := physicalClayDimension) (N := L)
              (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β) :=
          gibbsMeasure_isProbability physicalClayDimension L
            (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
            (wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le)
        have hobs : Measurable (plaquetteWilsonObs F p) := by
          simpa [plaquetteWilsonObs, Function.comp_def] using
            hF_meas.comp (measurable_plaquetteHolonomy (G :=
              ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)
        exact plaquetteWilsonObs_integrable_of_unitBound F hF p
          (gibbsMeasure (d := physicalClayDimension) (N := L)
            (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)
          hobs.aestronglyMeasurable)
      (fun L instL p q => by
        letI : NeZero L := instL
        haveI : IsProbabilityMeasure
            (gibbsMeasure (d := physicalClayDimension) (N := L)
              (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β) :=
          gibbsMeasure_isProbability physicalClayDimension L
            (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
            (wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le)
        have hpobs : Measurable (plaquetteWilsonObs F p) := by
          simpa [plaquetteWilsonObs, Function.comp_def] using
            hF_meas.comp (measurable_plaquetteHolonomy (G :=
              ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)
        have hqobs : Measurable (plaquetteWilsonObs F q) := by
          simpa [plaquetteWilsonObs, Function.comp_def] using
            hF_meas.comp (measurable_plaquetteHolonomy (G :=
              ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) q)
        exact plaquetteWilsonObs_mul_integrable_of_unitBound F hF p q
          (gibbsMeasure (d := physicalClayDimension) (N := L)
            (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)
          hpobs.aestronglyMeasurable hqobs.aestronglyMeasurable))

#print axioms physicalStrong_of_physicalClusterCorrelatorBound_siteDist_measurableF

/-- Bundle-level physical endpoint from all-dimensions Mayer/activity data and
the physical exponential count frontier. -/
noncomputable def connectedCorrDecayBundle_of_expCountBound_mayerData_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (r K : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (hK_pos : 0 < K) (hKr_lt1 : K * r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (data : ConnectedCardDecayMayerData N_c r A₀ hr_pos.le hA.le)
    (h_count : PhysicalShiftedConnectingClusterCountBoundExp C_conn K)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ConnectedCorrDecayBundle
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  connectedCorrDecayBundle_of_physicalClusterCorrelatorBound_siteDist
    r hr_pos hr_lt1
    (clusterPrefactorExp r K C_conn A₀)
    (clusterPrefactorExp_pos r K hr_pos hK_pos hKr_lt1 C_conn A₀ hC hA)
    (physicalClusterCorrelatorBound_of_expCountBound_mayerData_ceil
      N_c r K hr_pos hr_lt1 hK_pos hKr_lt1 C_conn A₀ hC hA data h_count)
    β F hβ hF
    (fun L => gibbsMeasure_isProbability physicalClayDimension L
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
      (wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le))
    (fun L instL p => by
      letI : NeZero L := instL
      haveI : IsProbabilityMeasure
          (gibbsMeasure (d := physicalClayDimension) (N := L)
            (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β) :=
        gibbsMeasure_isProbability physicalClayDimension L
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
          (wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le)
      have hobs : Measurable (plaquetteWilsonObs F p) := by
        simpa [plaquetteWilsonObs, Function.comp_def] using
          hF_meas.comp (measurable_plaquetteHolonomy (G :=
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)
      exact plaquetteWilsonObs_integrable_of_unitBound F hF p
        (gibbsMeasure (d := physicalClayDimension) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)
        hobs.aestronglyMeasurable)
    (fun L instL p q => by
      letI : NeZero L := instL
      haveI : IsProbabilityMeasure
          (gibbsMeasure (d := physicalClayDimension) (N := L)
            (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β) :=
        gibbsMeasure_isProbability physicalClayDimension L
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
          (wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le)
      have hpobs : Measurable (plaquetteWilsonObs F p) := by
        simpa [plaquetteWilsonObs, Function.comp_def] using
          hF_meas.comp (measurable_plaquetteHolonomy (G :=
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)
      have hqobs : Measurable (plaquetteWilsonObs F q) := by
        simpa [plaquetteWilsonObs, Function.comp_def] using
          hF_meas.comp (measurable_plaquetteHolonomy (G :=
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) q)
      exact plaquetteWilsonObs_mul_integrable_of_unitBound F hF p q
        (gibbsMeasure (d := physicalClayDimension) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)
        hpobs.aestronglyMeasurable hqobs.aestronglyMeasurable)

/-- Bundle-level physical endpoint from physical Mayer/activity data and the
physical exponential count frontier. -/
noncomputable def connectedCorrDecayBundle_of_physicalMayerData_expCount_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (r K : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (hK_pos : 0 < K) (hKr_lt1 : K * r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (data : PhysicalConnectedCardDecayMayerData N_c r A₀ hr_pos.le hA.le)
    (h_count : PhysicalShiftedConnectingClusterCountBoundExp C_conn K)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ConnectedCorrDecayBundle
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  connectedCorrDecayBundle_of_physicalClusterCorrelatorBound_siteDist
    r hr_pos hr_lt1
    (clusterPrefactorExp r K C_conn A₀)
    (clusterPrefactorExp_pos r K hr_pos hK_pos hKr_lt1 C_conn A₀ hC hA)
    (physicalClusterCorrelatorBound_of_physicalMayerData_expCount_ceil
      N_c r K hr_pos hr_lt1 hK_pos hKr_lt1 C_conn A₀ hC hA data h_count)
    β F hβ hF
    (fun L => gibbsMeasure_isProbability physicalClayDimension L
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
      (wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le))
    (fun L instL p => by
      letI : NeZero L := instL
      haveI : IsProbabilityMeasure
          (gibbsMeasure (d := physicalClayDimension) (N := L)
            (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β) :=
        gibbsMeasure_isProbability physicalClayDimension L
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
          (wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le)
      have hobs : Measurable (plaquetteWilsonObs F p) := by
        simpa [plaquetteWilsonObs, Function.comp_def] using
          hF_meas.comp (measurable_plaquetteHolonomy (G :=
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)
      exact plaquetteWilsonObs_integrable_of_unitBound F hF p
        (gibbsMeasure (d := physicalClayDimension) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)
        hobs.aestronglyMeasurable)
    (fun L instL p q => by
      letI : NeZero L := instL
      haveI : IsProbabilityMeasure
          (gibbsMeasure (d := physicalClayDimension) (N := L)
            (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β) :=
        gibbsMeasure_isProbability physicalClayDimension L
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
          (wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le)
      have hpobs : Measurable (plaquetteWilsonObs F p) := by
        simpa [plaquetteWilsonObs, Function.comp_def] using
          hF_meas.comp (measurable_plaquetteHolonomy (G :=
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)
      have hqobs : Measurable (plaquetteWilsonObs F q) := by
        simpa [plaquetteWilsonObs, Function.comp_def] using
          hF_meas.comp (measurable_plaquetteHolonomy (G :=
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) q)
      exact plaquetteWilsonObs_mul_integrable_of_unitBound F hF p q
        (gibbsMeasure (d := physicalClayDimension) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)
        hpobs.aestronglyMeasurable hqobs.aestronglyMeasurable)

/-- Direct physical endpoint from all-dimensions Mayer/activity data and the
physical exponential count frontier. -/
theorem physicalStrong_of_expCountBound_mayerData_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (r K : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (hK_pos : 0 < K) (hKr_lt1 : K * r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (data : ConnectedCardDecayMayerData N_c r A₀ hr_pos.le hA.le)
    (h_count : PhysicalShiftedConnectingClusterCountBoundExp C_conn K)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_connectedCorrDecayBundle
    (connectedCorrDecayBundle_of_expCountBound_mayerData_siteDist_measurableF
      r K hr_pos hr_lt1 hK_pos hKr_lt1 C_conn A₀ hC hA data h_count
      β F hβ hF hF_meas)

/-- Direct physical endpoint from physical Mayer/activity data and the
physical exponential count frontier. -/
theorem physicalStrong_of_physicalMayerData_expCount_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (r K : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (hK_pos : 0 < K) (hKr_lt1 : K * r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (data : PhysicalConnectedCardDecayMayerData N_c r A₀ hr_pos.le hA.le)
    (h_count : PhysicalShiftedConnectingClusterCountBoundExp C_conn K)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_connectedCorrDecayBundle
    (connectedCorrDecayBundle_of_physicalMayerData_expCount_siteDist_measurableF
      r K hr_pos hr_lt1 hK_pos hKr_lt1 C_conn A₀ hC hA data h_count
      β F hβ hF hF_meas)

#print axioms connectedCorrDecayBundle_of_expCountBound_mayerData_siteDist_measurableF
#print axioms connectedCorrDecayBundle_of_physicalMayerData_expCount_siteDist_measurableF
#print axioms physicalStrong_of_expCountBound_mayerData_siteDist_measurableF
#print axioms physicalStrong_of_physicalMayerData_expCount_siteDist_measurableF

/-- Bundle-level physical endpoint from the single-package physical shifted F3
frontier.

This exposes the intermediate `ConnectedCorrDecayBundle` certificate before it
is sent to `ClayYangMillsPhysicalStrong`, with the Gibbs probability and local
Wilson-observable integrability side conditions discharged from the concrete
Wilson plaquette energy and `Measurable F`. -/
noncomputable def connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalShiftedF3MayerCountPackage N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ConnectedCorrDecayBundle
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  connectedCorrDecayBundle_of_physicalClusterCorrelatorBound_siteDist
    wab.r wab.hr_pos wab.hr_lt1
    (clusterPrefactorShifted wab.r pkg.count.C_conn pkg.mayer.A₀
      pkg.count.dim)
    (clusterPrefactorShifted_pos wab.r wab.hr_pos wab.hr_lt1
      pkg.count.C_conn pkg.mayer.A₀ pkg.count.hC pkg.mayer.hA
      pkg.count.dim)
    (physicalClusterCorrelatorBound_of_physicalShiftedF3MayerCountPackage
      wab pkg)
    β F hβ hF
    (fun L => gibbsMeasure_isProbability physicalClayDimension L
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
      (wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le))
    (fun L instL p => by
      letI : NeZero L := instL
      haveI : IsProbabilityMeasure
          (gibbsMeasure (d := physicalClayDimension) (N := L)
            (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β) :=
        gibbsMeasure_isProbability physicalClayDimension L
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
          (wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le)
      have hobs : Measurable (plaquetteWilsonObs F p) := by
        simpa [plaquetteWilsonObs, Function.comp_def] using
          hF_meas.comp (measurable_plaquetteHolonomy (G :=
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)
      exact plaquetteWilsonObs_integrable_of_unitBound F hF p
        (gibbsMeasure (d := physicalClayDimension) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)
        hobs.aestronglyMeasurable)
    (fun L instL p q => by
      letI : NeZero L := instL
      haveI : IsProbabilityMeasure
          (gibbsMeasure (d := physicalClayDimension) (N := L)
            (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β) :=
        gibbsMeasure_isProbability physicalClayDimension L
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
          (wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le)
      have hpobs : Measurable (plaquetteWilsonObs F p) := by
        simpa [plaquetteWilsonObs, Function.comp_def] using
          hF_meas.comp (measurable_plaquetteHolonomy (G :=
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)
      have hqobs : Measurable (plaquetteWilsonObs F q) := by
        simpa [plaquetteWilsonObs, Function.comp_def] using
          hF_meas.comp (measurable_plaquetteHolonomy (G :=
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) q)
      exact plaquetteWilsonObs_mul_integrable_of_unitBound F hF p q
        (gibbsMeasure (d := physicalClayDimension) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)
        hpobs.aestronglyMeasurable hqobs.aestronglyMeasurable)

#print axioms connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_siteDist_measurableF

/-- The bundle-level physical F3 endpoint has decay rate
`kpParameter wab.r`. -/
theorem connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalShiftedF3MayerCountPackage N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_siteDist_measurableF
      wab pkg β F hβ hF hF_meas).ccd.m = kpParameter wab.r := rfl

/-- The bundle-level physical F3 endpoint has the shifted cluster prefactor,
inflated by the standard local-distance constant. -/
theorem connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalShiftedF3MayerCountPackage N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_siteDist_measurableF
      wab pkg β F hβ hF hF_meas).ccd.C =
      clusterPrefactorShifted wab.r pkg.count.C_conn pkg.mayer.A₀
        pkg.count.dim + 2 * Real.exp (kpParameter wab.r) := rfl

#print axioms connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_mass_eq
#print axioms connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_prefactor_eq

/-- After increasing the count polynomial dimension in a physical shifted F3
package, the bundle-level endpoint still has decay rate `kpParameter wab.r`. -/
theorem connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_mono_count_dim_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalShiftedF3MayerCountPackage N_c wab)
    (k : ℕ)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_siteDist_measurableF
      wab (pkg.mono_count_dim k) β F hβ hF hF_meas).ccd.m =
      kpParameter wab.r := rfl

/-- After increasing the count polynomial dimension in a physical shifted F3
package, the bundle-level endpoint exposes the enlarged shifted prefactor. -/
theorem connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_mono_count_dim_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalShiftedF3MayerCountPackage N_c wab)
    (k : ℕ)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_siteDist_measurableF
      wab (pkg.mono_count_dim k) β F hβ hF hF_meas).ccd.C =
      clusterPrefactorShifted wab.r pkg.count.C_conn pkg.mayer.A₀
        (pkg.count.dim + k) + 2 * Real.exp (kpParameter wab.r) := rfl

#print axioms connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_mono_count_dim_mass_eq
#print axioms connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_mono_count_dim_prefactor_eq

/-- Bundle-level physical endpoint from independently-produced shifted F3 Mayer
and physical `d = 4` count subpackages. -/
noncomputable def connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ConnectedCorrDecayBundle
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_siteDist_measurableF
    wab (PhysicalShiftedF3MayerCountPackage.ofSubpackages mayer count)
    β F hβ hF hF_meas

/-- The subpackage bundle-level physical F3 endpoint has decay rate
`kpParameter wab.r`. -/
theorem connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_siteDist_measurableF
      wab mayer count β F hβ hF hF_meas).ccd.m = kpParameter wab.r := rfl

/-- The subpackage bundle-level physical F3 endpoint has the shifted cluster
prefactor, inflated by the standard local-distance constant. -/
theorem connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_siteDist_measurableF
      wab mayer count β F hβ hF hF_meas).ccd.C =
      clusterPrefactorShifted wab.r count.C_conn mayer.A₀ count.dim +
        2 * Real.exp (kpParameter wab.r) := rfl

/-- After increasing the count polynomial dimension in the physical shifted F3
subpackage route, the bundle-level endpoint still has decay rate
`kpParameter wab.r`. -/
theorem connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_mono_count_dim_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (k : ℕ)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_siteDist_measurableF
      wab mayer (count.mono_dim k) β F hβ hF hF_meas).ccd.m =
      kpParameter wab.r := rfl

/-- After increasing the count polynomial dimension in the physical shifted F3
subpackage route, the bundle-level endpoint exposes the enlarged shifted
prefactor. -/
theorem connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_mono_count_dim_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (k : ℕ)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_siteDist_measurableF
      wab mayer (count.mono_dim k) β F hβ hF hF_meas).ccd.C =
      clusterPrefactorShifted wab.r count.C_conn mayer.A₀ (count.dim + k) +
        2 * Real.exp (kpParameter wab.r) := rfl

#print axioms connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_siteDist_measurableF
#print axioms connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_mass_eq
#print axioms connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_prefactor_eq
#print axioms connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_mono_count_dim_mass_eq
#print axioms connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_mono_count_dim_prefactor_eq

/-- Direct physical endpoint from the single-package physical shifted F3
frontier. -/
theorem physicalStrong_of_physicalShiftedF3MayerCountPackage_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalShiftedF3MayerCountPackage N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_connectedCorrDecayBundle
    (connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_siteDist_measurableF
      wab pkg β F hβ hF hF_meas)

#print axioms physicalStrong_of_physicalShiftedF3MayerCountPackage_siteDist_measurableF

/-- Direct physical endpoint from independently-produced shifted F3 Mayer and
physical `d = 4` count subpackages.

Unlike the dimension-polymorphic shifted F3 endpoint below, this consumes only
the physical counting package `PhysicalShiftedF3CountPackage`.  This is the
shortest current API path from the active F3 obligations to the non-vacuous
`ClayYangMillsPhysicalStrong` endpoint in Clay dimension four. -/
theorem physicalStrong_of_physicalShiftedF3Subpackages_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_physicalShiftedF3MayerCountPackage_siteDist_measurableF
    wab (PhysicalShiftedF3MayerCountPackage.ofSubpackages mayer count)
    β F hβ hF hF_meas

#print axioms physicalStrong_of_physicalShiftedF3Subpackages_siteDist_measurableF

/-- Bundle-level physical endpoint from the fully physical single F3 package.

This consumes physical `d = 4` Mayer data and the physical volume-uniform count
package, without requiring all-dimensions Mayer data. -/
noncomputable def connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalOnlyShiftedF3MayerCountPackage N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ConnectedCorrDecayBundle
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  connectedCorrDecayBundle_of_physicalClusterCorrelatorBound_siteDist
    wab.r wab.hr_pos wab.hr_lt1
    (clusterPrefactorShifted wab.r pkg.count.C_conn pkg.mayer.A₀
      pkg.count.dim)
    (clusterPrefactorShifted_pos wab.r wab.hr_pos wab.hr_lt1
      pkg.count.C_conn pkg.mayer.A₀ pkg.count.hC pkg.mayer.hA
      pkg.count.dim)
    (physicalClusterCorrelatorBound_of_physicalOnlyShiftedF3MayerCountPackage
      wab pkg)
    β F hβ hF
    (fun L => gibbsMeasure_isProbability physicalClayDimension L
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
      (wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le))
    (fun L instL p => by
      letI : NeZero L := instL
      haveI : IsProbabilityMeasure
          (gibbsMeasure (d := physicalClayDimension) (N := L)
            (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β) :=
        gibbsMeasure_isProbability physicalClayDimension L
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
          (wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le)
      have hobs : Measurable (plaquetteWilsonObs F p) := by
        simpa [plaquetteWilsonObs, Function.comp_def] using
          hF_meas.comp (measurable_plaquetteHolonomy (G :=
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)
      exact plaquetteWilsonObs_integrable_of_unitBound F hF p
        (gibbsMeasure (d := physicalClayDimension) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)
        hobs.aestronglyMeasurable)
    (fun L instL p q => by
      letI : NeZero L := instL
      haveI : IsProbabilityMeasure
          (gibbsMeasure (d := physicalClayDimension) (N := L)
            (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β) :=
        gibbsMeasure_isProbability physicalClayDimension L
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
          (wilsonPlaquetteEnergy_boltzmann_integrable β hβ.le)
      have hpobs : Measurable (plaquetteWilsonObs F p) := by
        simpa [plaquetteWilsonObs, Function.comp_def] using
          hF_meas.comp (measurable_plaquetteHolonomy (G :=
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)
      have hqobs : Measurable (plaquetteWilsonObs F q) := by
        simpa [plaquetteWilsonObs, Function.comp_def] using
          hF_meas.comp (measurable_plaquetteHolonomy (G :=
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) q)
      exact plaquetteWilsonObs_mul_integrable_of_unitBound F hF p q
        (gibbsMeasure (d := physicalClayDimension) (N := L)
          (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)
        hpobs.aestronglyMeasurable hqobs.aestronglyMeasurable)

theorem connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalOnlyShiftedF3MayerCountPackage N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
      wab pkg β F hβ hF hF_meas).ccd.m = kpParameter wab.r := rfl

theorem connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalOnlyShiftedF3MayerCountPackage N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
      wab pkg β F hβ hF hF_meas).ccd.C =
      clusterPrefactorShifted wab.r pkg.count.C_conn pkg.mayer.A₀
        pkg.count.dim + 2 * Real.exp (kpParameter wab.r) := rfl

/-- After increasing the count polynomial dimension in a fully physical F3
package, the bundle-level endpoint still has decay rate `kpParameter wab.r`. -/
theorem connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_mono_count_dim_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalOnlyShiftedF3MayerCountPackage N_c wab)
    (k : ℕ)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
      wab (pkg.mono_count_dim k) β F hβ hF hF_meas).ccd.m =
      kpParameter wab.r := rfl

/-- After increasing the count polynomial dimension in a fully physical F3
package, the bundle-level endpoint exposes the enlarged shifted prefactor. -/
theorem connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_mono_count_dim_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalOnlyShiftedF3MayerCountPackage N_c wab)
    (k : ℕ)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
      wab (pkg.mono_count_dim k) β F hβ hF hF_meas).ccd.C =
      clusterPrefactorShifted wab.r pkg.count.C_conn pkg.mayer.A₀
        (pkg.count.dim + k) + 2 * Real.exp (kpParameter wab.r) := rfl

/-- Bundle-level physical endpoint from fully physical Mayer/count subpackages. -/
noncomputable def connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ConnectedCorrDecayBundle
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
    wab (PhysicalOnlyShiftedF3MayerCountPackage.ofSubpackages mayer count)
    β F hβ hF hF_meas

theorem connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_siteDist_measurableF
      wab mayer count β F hβ hF hF_meas).ccd.m = kpParameter wab.r := rfl

theorem connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_siteDist_measurableF
      wab mayer count β F hβ hF hF_meas).ccd.C =
      clusterPrefactorShifted wab.r count.C_conn mayer.A₀ count.dim +
        2 * Real.exp (kpParameter wab.r) := rfl

/-- After increasing the count polynomial dimension in the fully physical F3
subpackage route, the bundle-level endpoint still has decay rate
`kpParameter wab.r`. -/
theorem connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_mono_count_dim_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (k : ℕ)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_siteDist_measurableF
      wab mayer (count.mono_dim k) β F hβ hF hF_meas).ccd.m =
      kpParameter wab.r := rfl

/-- After increasing the count polynomial dimension in the fully physical F3
subpackage route, the bundle-level endpoint exposes the enlarged shifted
prefactor. -/
theorem connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_mono_count_dim_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (k : ℕ)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_siteDist_measurableF
      wab mayer (count.mono_dim k) β F hβ hF hF_meas).ccd.C =
      clusterPrefactorShifted wab.r count.C_conn mayer.A₀ (count.dim + k) +
        2 * Real.exp (kpParameter wab.r) := rfl

/-- Bundle-level physical endpoint from an all-dimensions Mayer package and
the physical count package, via the preferred physical-only F3 package. -/
noncomputable def connectedCorrDecayBundle_of_globalMayer_physicalCount_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ConnectedCorrDecayBundle
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
    wab (PhysicalOnlyShiftedF3MayerCountPackage.ofGlobalMayer mayer count)
    β F hβ hF hF_meas

theorem connectedCorrDecayBundle_of_globalMayer_physicalCount_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_globalMayer_physicalCount_siteDist_measurableF
      wab mayer count β F hβ hF hF_meas).ccd.m = kpParameter wab.r := rfl

theorem connectedCorrDecayBundle_of_globalMayer_physicalCount_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_globalMayer_physicalCount_siteDist_measurableF
      wab mayer count β F hβ hF hF_meas).ccd.C =
      clusterPrefactorShifted wab.r count.C_conn mayer.A₀ count.dim +
        2 * Real.exp (kpParameter wab.r) := rfl

/-- After increasing the count polynomial dimension in the global-Mayer /
physical-count route, the bundle-level endpoint still has decay rate
`kpParameter wab.r`. -/
theorem connectedCorrDecayBundle_of_globalMayer_physicalCount_mono_count_dim_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (k : ℕ)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_globalMayer_physicalCount_siteDist_measurableF
      wab mayer (count.mono_dim k) β F hβ hF hF_meas).ccd.m =
      kpParameter wab.r := rfl

/-- After increasing the count polynomial dimension in the global-Mayer /
physical-count route, the bundle-level endpoint exposes the enlarged shifted
prefactor. -/
theorem connectedCorrDecayBundle_of_globalMayer_physicalCount_mono_count_dim_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (k : ℕ)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_globalMayer_physicalCount_siteDist_measurableF
      wab mayer (count.mono_dim k) β F hβ hF hF_meas).ccd.C =
      clusterPrefactorShifted wab.r count.C_conn mayer.A₀ (count.dim + k) +
        2 * Real.exp (kpParameter wab.r) := rfl

/-- Bundle-level physical endpoint from the global single F3 package, routed
through its preferred physical restriction. -/
noncomputable def connectedCorrDecayBundle_of_shiftedF3MayerCountPackage_toPhysicalOnly_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ConnectedCorrDecayBundle
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
    wab pkg.toPhysicalOnly β F hβ hF hF_meas

theorem connectedCorrDecayBundle_of_shiftedF3MayerCountPackage_toPhysicalOnly_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_shiftedF3MayerCountPackage_toPhysicalOnly_siteDist_measurableF
      wab pkg β F hβ hF hF_meas).ccd.m = kpParameter wab.r := rfl

theorem connectedCorrDecayBundle_of_shiftedF3MayerCountPackage_toPhysicalOnly_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_shiftedF3MayerCountPackage_toPhysicalOnly_siteDist_measurableF
      wab pkg β F hβ hF hF_meas).ccd.C =
      clusterPrefactorShifted wab.r pkg.C_conn pkg.A₀ pkg.dim +
        2 * Real.exp (kpParameter wab.r) := rfl

/-- After increasing the count polynomial dimension in a global F3 package and
then restricting physically, the bundle-level endpoint still has decay rate
`kpParameter wab.r`. -/
theorem connectedCorrDecayBundle_of_shiftedF3MayerCountPackage_toPhysicalOnly_mono_count_dim_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab)
    (k : ℕ)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_shiftedF3MayerCountPackage_toPhysicalOnly_siteDist_measurableF
      wab (pkg.mono_count_dim k) β F hβ hF hF_meas).ccd.m =
      kpParameter wab.r := rfl

/-- After increasing the count polynomial dimension in a global F3 package and
then restricting physically, the bundle-level endpoint exposes the enlarged
shifted prefactor. -/
theorem connectedCorrDecayBundle_of_shiftedF3MayerCountPackage_toPhysicalOnly_mono_count_dim_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab)
    (k : ℕ)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_shiftedF3MayerCountPackage_toPhysicalOnly_siteDist_measurableF
      wab (pkg.mono_count_dim k) β F hβ hF hF_meas).ccd.C =
      clusterPrefactorShifted wab.r pkg.C_conn pkg.A₀ (pkg.dim + k) +
        2 * Real.exp (kpParameter wab.r) := rfl

/-- Direct physical endpoint from the fully physical single F3 package. -/
theorem physicalStrong_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalOnlyShiftedF3MayerCountPackage N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_connectedCorrDecayBundle
    (connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
      wab pkg β F hβ hF hF_meas)

/-- Direct physical endpoint from fully physical Mayer/count subpackages. -/
theorem physicalStrong_of_physicalOnlyShiftedF3Subpackages_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
    wab (PhysicalOnlyShiftedF3MayerCountPackage.ofSubpackages mayer count)
    β F hβ hF hF_meas

/-- Direct physical endpoint from an all-dimensions Mayer package and the
physical count package, via the preferred physical-only F3 package. -/
theorem physicalStrong_of_globalMayer_physicalCount_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackage)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
    wab (PhysicalOnlyShiftedF3MayerCountPackage.ofGlobalMayer mayer count)
    β F hβ hF hF_meas

/-- Bundle-level physical endpoint from the fully physical exponential F3
package. -/
noncomputable def connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackageExp_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalOnlyShiftedF3MayerCountPackageExp N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ConnectedCorrDecayBundle
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  connectedCorrDecayBundle_of_physicalMayerData_expCount_siteDist_measurableF
    wab.r pkg.count.K wab.hr_pos wab.hr_lt1 pkg.count.hK pkg.hKr_lt1
    pkg.count.C_conn pkg.mayer.A₀ pkg.count.hC pkg.mayer.hA
    pkg.mayer.data pkg.count.h_count β F hβ hF hF_meas

theorem connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackageExp_mass_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalOnlyShiftedF3MayerCountPackageExp N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackageExp_siteDist_measurableF
      wab pkg β F hβ hF hF_meas).ccd.m = kpParameter wab.r := rfl

theorem connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackageExp_prefactor_eq
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalOnlyShiftedF3MayerCountPackageExp N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    (connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackageExp_siteDist_measurableF
      wab pkg β F hβ hF hF_meas).ccd.C =
      clusterPrefactorExp wab.r pkg.count.K pkg.count.C_conn pkg.mayer.A₀ +
        2 * Real.exp (kpParameter wab.r) := rfl

/-- Direct physical endpoint from the fully physical exponential F3 package. -/
theorem physicalStrong_of_physicalOnlyShiftedF3MayerCountPackageExp_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : PhysicalOnlyShiftedF3MayerCountPackageExp N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_connectedCorrDecayBundle
    (connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackageExp_siteDist_measurableF
      wab pkg β F hβ hF hF_meas)

/-- Direct physical endpoint from fully physical exponential Mayer/count
subpackages. -/
theorem physicalStrong_of_physicalOnlyShiftedF3SubpackagesExp_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (count : PhysicalShiftedF3CountPackageExp)
    (hKr_lt1 : count.K * wab.r < 1)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_physicalOnlyShiftedF3MayerCountPackageExp_siteDist_measurableF
    wab
    (PhysicalOnlyShiftedF3MayerCountPackageExp.ofSubpackages
      mayer count hKr_lt1)
    β F hβ hF hF_meas

/-- Direct physical endpoint from the graph-animal `1296` F3-count target,
the physical Mayer package, and the KP smallness input. -/
theorem physicalStrong_of_graphAnimalShiftedCount1296_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hgraph : PhysicalConnectingClusterGraphAnimalShiftedCountBound1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_physicalOnlyShiftedF3MayerCountPackageExp_siteDist_measurableF
    wab
    (physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalShiftedCount1296
      wab mayer hgraph hKr_lt1)
    β F hβ hF hF_meas

/-- Direct physical endpoint from the graph-animal `1296` word-decoder target,
the physical Mayer package, and the KP smallness input. -/
theorem physicalStrong_of_graphAnimalWordDecoder1296_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hdecode : PhysicalConnectingClusterGraphAnimalShiftedWordDecoderBound1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_physicalOnlyShiftedF3MayerCountPackageExp_siteDist_measurableF
    wab
    (physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalWordDecoder1296
      wab mayer hdecode hKr_lt1)
    β F hβ hF hF_meas

/-- Direct physical endpoint from the corrected total-size graph-animal `1296`
word-decoder target, the physical Mayer package, and the KP smallness input.

The mass parameter in the final decay bundle is `kpParameter (1296 * wab.r)`,
matching the effective total-size route. -/
theorem physicalStrong_of_graphAnimalTotalWordDecoder1296_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hdecode : PhysicalConnectingClusterGraphAnimalTotalWordDecoderBound1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_physicalClusterCorrelatorBound_siteDist_measurableF
    ((1296 : ℝ) * wab.r)
    (mul_pos (by norm_num) wab.hr_pos)
    hKr_lt1
    (clusterPrefactorExp wab.r 1296 1 mayer.A₀)
    (clusterPrefactorExp_pos wab.r 1296 wab.hr_pos (by norm_num) hKr_lt1
      1 mayer.A₀ one_pos mayer.hA)
    (physicalClusterCorrelatorBound_of_graphAnimalTotalWordDecoder1296
      wab mayer hdecode hKr_lt1)
    β F hβ hF hF_meas

/-- Small-β terminal form of the corrected total-size graph-animal route.

For the concrete clipped Wilson activity producer
`wilsonActivityBound_from_expansion`, the decay rate is definitionally
`wab.r = β`, so the KP smallness condition becomes the explicit inequality
`1296 * β < 1`. -/
theorem physicalStrong_of_graphAnimalTotalWordDecoder1296_smallBeta_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt1 : β < 1)
    (hβ_small : (1296 : ℝ) * β < 1)
    (mayer : PhysicalShiftedF3MayerPackage N_c
      (wilsonActivityBound_from_expansion N_c hβ_pos hβ_lt1))
    (hdecode : PhysicalConnectingClusterGraphAnimalTotalWordDecoderBound1296)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_graphAnimalTotalWordDecoder1296_siteDist_measurableF
    (wilsonActivityBound_from_expansion N_c hβ_pos hβ_lt1)
    mayer hdecode
    (by simpa [wilsonActivityBound_from_expansion] using hβ_small)
    β F hβ_pos hF hF_meas

/-- Single terminal package for the corrected total-size small-β F3 route.

For the concrete clipped Wilson activity `wilsonActivityBound_from_expansion`,
the remaining nontrivial F3 obligations are exactly:
the KP smallness inequality `1296 * β < 1`, the physical shifted Mayer package,
and the physical total graph-animal decoder. -/
structure PhysicalTotalF3SmallBetaPackage
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    (hβ_pos : 0 < β) (hβ_lt1 : β < 1) where
  hβ_small : (1296 : ℝ) * β < 1
  mayer : PhysicalShiftedF3MayerPackage N_c
    (wilsonActivityBound_from_expansion N_c hβ_pos hβ_lt1)
  decode : PhysicalConnectingClusterGraphAnimalTotalWordDecoderBound1296

/-- Terminal small-β physical endpoint from the single F3 package.

This is the current narrowest Wilson-facing F3 statement: once the concrete
small-β Mayer identity/decay package and the total graph-animal decoder are
provided, the Clay-grade physical strong endpoint follows. -/
theorem physicalStrong_of_totalF3SmallBetaPackage_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt1 : β < 1)
    (pkg : PhysicalTotalF3SmallBetaPackage N_c β hβ_pos hβ_lt1)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_graphAnimalTotalWordDecoder1296_smallBeta_siteDist_measurableF
    hβ_pos hβ_lt1 pkg.hβ_small pkg.mayer pkg.decode F hF hF_meas

#print axioms connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
#print axioms connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_mass_eq
#print axioms connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_prefactor_eq
#print axioms connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_mono_count_dim_mass_eq
#print axioms connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_mono_count_dim_prefactor_eq
#print axioms connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_siteDist_measurableF
#print axioms connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_mass_eq
#print axioms connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_prefactor_eq
#print axioms connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_mono_count_dim_mass_eq
#print axioms connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_mono_count_dim_prefactor_eq
#print axioms connectedCorrDecayBundle_of_globalMayer_physicalCount_siteDist_measurableF
#print axioms connectedCorrDecayBundle_of_globalMayer_physicalCount_mass_eq
#print axioms connectedCorrDecayBundle_of_globalMayer_physicalCount_prefactor_eq
#print axioms connectedCorrDecayBundle_of_globalMayer_physicalCount_mono_count_dim_mass_eq
#print axioms connectedCorrDecayBundle_of_globalMayer_physicalCount_mono_count_dim_prefactor_eq
#print axioms connectedCorrDecayBundle_of_shiftedF3MayerCountPackage_toPhysicalOnly_siteDist_measurableF
#print axioms connectedCorrDecayBundle_of_shiftedF3MayerCountPackage_toPhysicalOnly_mass_eq
#print axioms connectedCorrDecayBundle_of_shiftedF3MayerCountPackage_toPhysicalOnly_prefactor_eq
#print axioms connectedCorrDecayBundle_of_shiftedF3MayerCountPackage_toPhysicalOnly_mono_count_dim_mass_eq
#print axioms connectedCorrDecayBundle_of_shiftedF3MayerCountPackage_toPhysicalOnly_mono_count_dim_prefactor_eq
#print axioms physicalStrong_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
#print axioms physicalStrong_of_physicalOnlyShiftedF3Subpackages_siteDist_measurableF
#print axioms physicalStrong_of_globalMayer_physicalCount_siteDist_measurableF
#print axioms connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackageExp_siteDist_measurableF
#print axioms connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackageExp_mass_eq
#print axioms connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackageExp_prefactor_eq
#print axioms physicalStrong_of_physicalOnlyShiftedF3MayerCountPackageExp_siteDist_measurableF
#print axioms physicalStrong_of_physicalOnlyShiftedF3SubpackagesExp_siteDist_measurableF
#print axioms physicalStrong_of_graphAnimalShiftedCount1296_siteDist_measurableF
#print axioms physicalStrong_of_graphAnimalWordDecoder1296_siteDist_measurableF
#print axioms physicalStrong_of_graphAnimalTotalWordDecoder1296_siteDist_measurableF
#print axioms physicalStrong_of_graphAnimalTotalWordDecoder1296_smallBeta_siteDist_measurableF
#print axioms physicalStrong_of_totalF3SmallBetaPackage_siteDist_measurableF

/-- Direct physical endpoint from the preferred single-package shifted F3 route.

This is the Wilson-facing F3 package composed with the direct
`ClusterCorrelatorBound → PhysicalStrong` bridge. -/
theorem physicalStrong_of_shiftedF3MayerCountPackage_siteDist_measurableF
    {N_c d : ℕ} [NeZero N_c] [NeZero d]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette d L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_clusterCorrelatorBound_siteDist_measurableF
    wab.r wab.hr_pos wab.hr_lt1
    (clusterPrefactorShifted wab.r pkg.C_conn pkg.A₀ pkg.dim)
    (clusterPrefactorShifted_pos wab.r wab.hr_pos wab.hr_lt1
      pkg.C_conn pkg.A₀ pkg.hC pkg.hA pkg.dim)
    (clusterCorrelatorBound_of_shiftedF3MayerCountPackage N_c wab pkg)
    β F hβ hF hF_meas

/-- Direct physical endpoint from independently-produced shifted F3 Mayer and
count subpackages. -/
theorem physicalStrong_of_shiftedF3Subpackages_siteDist_measurableF
    {N_c d : ℕ} [NeZero N_c] [NeZero d]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : ShiftedF3CountPackage)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette d L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_shiftedF3MayerCountPackage_siteDist_measurableF
    wab (ShiftedF3MayerCountPackage.ofSubpackages mayer count)
    β F hβ hF hF_meas

#print axioms physicalStrong_of_shiftedF3MayerCountPackage_siteDist_measurableF
#print axioms physicalStrong_of_shiftedF3Subpackages_siteDist_measurableF

/-- Physical-dimension specialization of the preferred single-package shifted
F3 endpoint. -/
theorem physicalStrong_of_shiftedF3MayerCountPackage_physicalClayDimension_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_shiftedF3MayerCountPackage_siteDist_measurableF
    (d := physicalClayDimension) wab pkg β F hβ hF hF_meas

/-- Physical-dimension specialization of the independently-produced shifted
F3 subpackage endpoint. -/
theorem physicalStrong_of_shiftedF3Subpackages_physicalClayDimension_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : ShiftedF3CountPackage)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_shiftedF3Subpackages_siteDist_measurableF
    (d := physicalClayDimension) wab mayer count β F hβ hF hF_meas

#print axioms physicalStrong_of_shiftedF3MayerCountPackage_physicalClayDimension_siteDist_measurableF
#print axioms physicalStrong_of_shiftedF3Subpackages_physicalClayDimension_siteDist_measurableF

/-- Direct physical endpoint from the named small-β uniform-rpow frontier.

This is the small-β route exposed in `ZeroMeanCancellation.lean`, composed with
the cleaned-up L8 physical bridge.  The analytic input remains exactly the
uniform `WilsonUniformRpowBound`; finite-volume regularity is discharged from
`Measurable F` and `|F| ≤ 1`. -/
theorem physicalStrong_of_uniformRpow_small_beta_siteDist_measurableF
    {N_c d : ℕ} [NeZero N_c] [NeZero d]
    {β₀ C : ℝ}
    (hβ₀_pos : 0 < β₀)
    (hβ₀_lt1 : β₀ < 1)
    (hC : 0 < C)
    (h_rpow : WilsonUniformRpowBound N_c β₀ C)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette d L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_clayConnectedCorrDecay_siteDist_measurableF
    (clayConnectedCorrDecay_small_beta_of_uniformRpow
      N_c hβ₀_pos hβ₀_lt1 C hC h_rpow)
    β F hβ hF hF_meas

#print axioms physicalStrong_of_uniformRpow_small_beta_siteDist_measurableF

/-- Physical-dimension specialization of the named small-β uniform-rpow
endpoint. -/
theorem physicalStrong_of_uniformRpow_small_beta_physicalClayDimension_siteDist_measurableF
    {N_c : ℕ} [NeZero N_c]
    {β₀ C : ℝ}
    (hβ₀_pos : 0 < β₀)
    (hβ₀_lt1 : β₀ < 1)
    (hC : 0 < C)
    (h_rpow : WilsonUniformRpowBound N_c β₀ C)
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hβ : 0 < β)
    (hF : ∀ U, |F U| ≤ 1)
    (hF_meas : Measurable F) :
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
        siteLatticeDist p.site q.site) :=
  physicalStrong_of_uniformRpow_small_beta_siteDist_measurableF
    (d := physicalClayDimension) (C := C)
    hβ₀_pos hβ₀_lt1 hC h_rpow β F hβ hF hF_meas

#print axioms physicalStrong_of_uniformRpow_small_beta_physicalClayDimension_siteDist_measurableF

end YangMills
