import Mathlib
import YangMills.ClayCore.CharacterExpansion
import YangMills.ClayCore.ClayWitness

/-!
# Cluster Correlator Bound (Phase 15h, Layer B1)

Formalises Theorem 7.1 of Bloque4: the connected Wilson
correlator is controlled by the sum over connecting clusters,
yielding an exponential decay bound.

We package the full cluster-expansion theorem as an explicit
named hypothesis `ClusterCorrelatorBound`.  The provable part
of the story — the triangle decomposition of the connected
correlator — is exposed as
`wilsonConnectedCorr_eq_sub` and
`wilsonConnectedCorr_abs_le_triangle`.

Given the cluster bound as input, we construct a concrete
`CharacterExpansionData` and derive the Clay Yang-Mills
mass-gap structure and theorem via the A1 bridge.

Source: Bloque4 Theorem 7.1, Paper Eriksson 2602.0069 Sec 7.2.
-/

namespace YangMills
open Real
open MeasureTheory

/-- Definitional expansion of the connected correlator. -/
theorem wilsonConnectedCorr_eq_sub
    {N_c d L : ℕ} [NeZero N_c] [NeZero d] [NeZero L]
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (p q : ConcretePlaquette d L) :
    wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
    wilsonCorrelation (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q -
    wilsonExpectation (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p *
    wilsonExpectation (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F q := rfl

/-- Triangle bound on the connected correlator:
    `|corr| ≤ |⟨FG⟩| + |⟨F⟩|·|⟨G⟩|`. -/
theorem wilsonConnectedCorr_abs_le_triangle
    {N_c d L : ℕ} [NeZero N_c] [NeZero d] [NeZero L]
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (p q : ConcretePlaquette d L) :
    |wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q| ≤
    |wilsonCorrelation (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q| +
    |wilsonExpectation (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p| *
    |wilsonExpectation (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F q| := by
  rw [wilsonConnectedCorr_eq_sub, ← abs_mul]
  exact abs_sub _ _

private theorem wilsonExpectation_abs_le_one_of_unitBound
    {N_c d L : ℕ} [NeZero N_c] [NeZero d] [NeZero L]
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hF : ∀ U, |F U| ≤ 1)
    (p : ConcretePlaquette d L)
    [IsProbabilityMeasure
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)]
    (hp_int : Integrable (plaquetteWilsonObs F p)
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)) :
    |wilsonExpectation (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p| ≤ 1 := by
  let μG :=
    gibbsMeasure (d := d) (N := L)
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
  have h_upper :
      wilsonExpectation (sunHaarProb N_c)
          (wilsonPlaquetteEnergy N_c) β F p ≤ 1 := by
    have hmono := expectation_mono d L
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
      (O₁ := plaquetteWilsonObs F p) (O₂ := fun _ => (1 : ℝ))
      hp_int (integrable_const (c := (1 : ℝ)))
      (fun A => (abs_le.mp (hF (GaugeConfig.plaquetteHolonomy A p))).2)
    have hconst :
        expectation d L (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
          (fun _ : GaugeConfig d L
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) => (1 : ℝ)) = 1 := by
      simp [expectation]
    simpa [wilsonExpectation, hconst] using hmono
  have h_lower :
      -1 ≤ wilsonExpectation (sunHaarProb N_c)
          (wilsonPlaquetteEnergy N_c) β F p := by
    have hmono := expectation_mono d L
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
      (O₁ := fun _ : GaugeConfig d L
        ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) => (-1 : ℝ))
      (O₂ := plaquetteWilsonObs F p)
      (integrable_const (c := (-1 : ℝ))) hp_int
      (fun A => (abs_le.mp (hF (GaugeConfig.plaquetteHolonomy A p))).1)
    have hconst :
        expectation d L (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
          (fun _ : GaugeConfig d L
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) => (-1 : ℝ)) = -1 := by
      simp [expectation]
    simpa [wilsonExpectation, hconst] using hmono
  exact abs_le.mpr ⟨h_lower, h_upper⟩

private theorem wilsonCorrelation_abs_le_one_of_unitBound
    {N_c d L : ℕ} [NeZero N_c] [NeZero d] [NeZero L]
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hF : ∀ U, |F U| ≤ 1)
    (p q : ConcretePlaquette d L)
    [IsProbabilityMeasure
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)]
    (hpq_int : Integrable
      (fun A : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
        plaquetteWilsonObs F p A * plaquetteWilsonObs F q A)
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)) :
    |wilsonCorrelation (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q| ≤ 1 := by
  let μG :=
    gibbsMeasure (d := d) (N := L)
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
  have h_abs_point :
      ∀ A : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
        |plaquetteWilsonObs F p A * plaquetteWilsonObs F q A| ≤ 1 := by
    intro A
    have hp := hF (GaugeConfig.plaquetteHolonomy A p)
    have hq := hF (GaugeConfig.plaquetteHolonomy A q)
    rw [abs_mul]
    exact mul_le_one₀ hp (abs_nonneg _) hq
  have h_upper :
      wilsonCorrelation (sunHaarProb N_c)
          (wilsonPlaquetteEnergy N_c) β F p q ≤ 1 := by
    have hmono := expectation_mono d L
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
      (O₁ := fun A : GaugeConfig d L
        ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
          plaquetteWilsonObs F p A * plaquetteWilsonObs F q A)
      (O₂ := fun _ => (1 : ℝ))
      hpq_int (integrable_const (c := (1 : ℝ)))
      (fun A => (abs_le.mp (h_abs_point A)).2)
    have hconst :
        expectation d L (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
          (fun _ : GaugeConfig d L
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) => (1 : ℝ)) = 1 := by
      simp [expectation]
    simpa [wilsonCorrelation, correlation, hconst] using hmono
  have h_lower :
      -1 ≤ wilsonCorrelation (sunHaarProb N_c)
          (wilsonPlaquetteEnergy N_c) β F p q := by
    have hmono := expectation_mono d L
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
      (O₁ := fun _ : GaugeConfig d L
        ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) => (-1 : ℝ))
      (O₂ := fun A : GaugeConfig d L
        ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
          plaquetteWilsonObs F p A * plaquetteWilsonObs F q A)
      (integrable_const (c := (-1 : ℝ))) hpq_int
      (fun A => (abs_le.mp (h_abs_point A)).1)
    have hconst :
        expectation d L (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β
          (fun _ : GaugeConfig d L
            ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) => (-1 : ℝ)) = -1 := by
      simp [expectation]
    simpa [wilsonCorrelation, correlation, hconst] using hmono
  exact abs_le.mpr ⟨h_lower, h_upper⟩

/-- Local bounded-observable estimate for the Wilson connected correlator.

This is the finite-distance companion to the separated-cluster estimates: it
does not prove exponential decay, but it records that unit-bounded observables
give a uniform `2` bound once the relevant Gibbs measure is a probability
measure and the three integrability side-conditions are supplied. -/
theorem wilsonConnectedCorr_abs_le_two_of_unitBound
    {N_c d L : ℕ} [NeZero N_c] [NeZero d] [NeZero L]
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hF : ∀ U, |F U| ≤ 1)
    (p q : ConcretePlaquette d L)
    [IsProbabilityMeasure
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)]
    (hp_int : Integrable (plaquetteWilsonObs F p)
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β))
    (hq_int : Integrable (plaquetteWilsonObs F q)
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β))
    (hpq_int : Integrable
      (fun A : GaugeConfig d L ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
        plaquetteWilsonObs F p A * plaquetteWilsonObs F q A)
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β)) :
    |wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q| ≤ 2 := by
  have htri := wilsonConnectedCorr_abs_le_triangle β F p q
  have hcorr := wilsonCorrelation_abs_le_one_of_unitBound
    β F hF p q hpq_int
  have hp := wilsonExpectation_abs_le_one_of_unitBound
    β F hF p hp_int
  have hq := wilsonExpectation_abs_le_one_of_unitBound
    β F hF q hq_int
  calc
    |wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q|
        ≤ |wilsonCorrelation (sunHaarProb N_c)
            (wilsonPlaquetteEnergy N_c) β F p q| +
          |wilsonExpectation (sunHaarProb N_c)
            (wilsonPlaquetteEnergy N_c) β F p| *
          |wilsonExpectation (sunHaarProb N_c)
            (wilsonPlaquetteEnergy N_c) β F q| := htri
    _ ≤ 1 + 1 * 1 := by
      gcongr
    _ = 2 := by norm_num

/-- **Cluster correlator bound (B1).**
    The content of Theorem 7.1 of Bloque4 in the form consumed
    by `CharacterExpansionData`: the connected Wilson correlator
    decays exponentially in the site distance, with the KP
    parameter `kpParameter r` as the rate and `C_clust` as
    prefactor, uniformly in the inverse coupling β > 0 and
    the unit-bounded test function `F`. -/
def ClusterCorrelatorBound
    (N_c : ℕ) [NeZero N_c] (r C_clust : ℝ) : Prop :=
  ∀ {d L : ℕ} [NeZero d] [NeZero L]
    (β : ℝ) (_hβ : 0 < β)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (_hF : ∀ U, |F U| ≤ 1)
    (p q : ConcretePlaquette d L),
    (1 : ℝ) ≤ siteLatticeDist p.site q.site →
    |wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q| ≤
    C_clust * Real.exp (-(kpParameter r) *
        siteLatticeDist p.site q.site)

/-- Inhabit `CharacterExpansionData` from a cluster correlator
    bound.  The `Rep`, `character`, and `coeff` slots are
    filled with trivial Peter-Weyl metadata; the geometric
    decay (r, C_clust) and the exponential correlator bound
    are carried directly from the hypothesis. -/
noncomputable def wilsonCharExpansion
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_clust : ℝ) (hC : 0 < C_clust)
    (h : ClusterCorrelatorBound N_c r C_clust) :
    CharacterExpansionData N_c where
  Rep := PUnit
  character := fun _ _ => (0 : ℂ)
  coeff := fun _ _ => (0 : ℝ)
  r := r
  hr_pos := hr_pos
  hr_lt1 := hr_lt1
  C_clust := C_clust
  hC := hC
  h_correlator := h

/-- Repackage a `ClusterCorrelatorBound` as the analytic witness bundle used by
    the older Clay witness route.  This is field-for-field: the KP parameter,
    prefactor, and connected-correlator bound are exactly the supplied data. -/
noncomputable def clayWitnessHyp_of_clusterCorrelatorBound
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_clust : ℝ) (hC : 0 < C_clust)
    (h : ClusterCorrelatorBound N_c r C_clust) :
    ClayWitnessHyp N_c where
  r := r
  hr_pos := hr_pos
  hr_lt_one := hr_lt1
  C_clust := C_clust
  hC_clust := hC
  hbound_hyp := h

/-- **FINAL CHAIN.** Given the cluster correlator bound (B1),
    produce the full Clay Yang-Mills mass-gap structure for
    `SU(N_c)` via the A1 Peter-Weyl bridge. -/
noncomputable def clay_massGap_large_beta
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_clust : ℝ) (hC : 0 < C_clust)
    (h : ClusterCorrelatorBound N_c r C_clust) :
    ClayYangMillsMassGap N_c :=
  clay_from_charExpansion
    (wilsonCharExpansion N_c r hr_pos hr_lt1 C_clust hC h)

/-- **THE CLAY THEOREM (from B1).** Given the cluster
    correlator bound, the Clay Yang-Mills mass-gap theorem
    statement follows. -/
theorem clay_yangMills_large_beta
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_clust : ℝ) (hC : 0 < C_clust)
    (h : ClusterCorrelatorBound N_c r C_clust) :
    ClayYangMillsTheorem :=
  clay_theorem_from_charExpansion
    (wilsonCharExpansion N_c r hr_pos hr_lt1 C_clust hC h)

#print axioms clayWitnessHyp_of_clusterCorrelatorBound
#print axioms wilsonConnectedCorr_abs_le_two_of_unitBound

end YangMills
