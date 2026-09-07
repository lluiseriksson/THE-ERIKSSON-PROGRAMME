/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FTCConnectedDomainTotal
import YangMills.RG.BalabanCMP102Eq80SourcePi4FTCIntegralLocalization

/-!
# Individual connected-domain activities in the complete FTC tree

The complete FTC total previously retained the finite connected-domain sum
inside every recursive integral.  Here we define one recursive contribution
for each physical connected-domain label.  We first prove continuity and
interval integrability of every such contribution, and only then commute the
finite sum with the literal FTC integrals.

Thus the terminal decomposition does not use linearity of a nonintegrable
Bochner integral and introduces no activity or integrability premise.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- The contribution of one physical connected-domain label to the complete
recursive FTC expansion. -/
noncomputable def cmp102Eq80SourcePi4FTCConnectedDomainActivity
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (W : Finset (FinBox 4 (2 * Q)))
    (n : ℕ) (coordinates : Fin n → FinBox 4 (2 * Q))
    (sigma : FinBox 4 (2 * Q) → ℝ) :
    List (FinBox 4 (2 * Q)) → ℝ
  | [] =>
      if n = 0 then 0 else
        cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase sigma vertexCoordinates coordinates W
  | d :: tail =>
      cmp102Eq80SourcePi4FTCConnectedDomainActivity
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase vertexCoordinates W n coordinates
          (Function.update sigma d 0) tail +
        ∫ t in (0 : ℝ)..1,
          cmp102Eq80SourcePi4FTCConnectedDomainActivity
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
            vertexBase vertexCoordinates W (n + 1)
            (Fin.cons d coordinates) (Function.update sigma d t) tail

/-- Source-level activity of one connected physical domain in the complete
nondecoupled FTC remainder. -/
noncomputable def cmp102Eq80SourcePi4ConnectedDomainActivity
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (W : Finset (FinBox 4 (2 * Q))) : ℝ :=
  cmp102Eq80SourcePi4FTCConnectedDomainActivity
    (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
    vertexBase vertexCoordinates W 0 Fin.elim0 s L

set_option maxHeartbeats 64000000 in
/-- Every individual recursive connected-domain activity is continuous under
a coordinatewise continuous family of physical contour points. -/
theorem continuous_cmp102Eq80SourcePi4FTCConnectedDomainActivity_comp
    {M Q Nc R Δ : ℕ} {T : Type*}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [TopologicalSpace T] [FirstCountableTopology T] [LocallyCompactSpace T]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (W : Finset (FinBox 4 (2 * Q)))
    (n : ℕ) (coordinates : Fin n → FinBox 4 (2 * Q))
    (sigma : T → FinBox 4 (2 * Q) → ℝ)
    (remaining : List (FinBox 4 (2 * Q)))
    (hsigma : ∀ d, Continuous fun x => sigma x d)
    (hRweak : 1 ≤ Rweak)
    (hsigmaRegion :
      ∀ x, CMP116RealPhysicalContourRegion Rweak (sigma x))
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hV₀ : ContDiff ℝ (n + remaining.length) V₀) :
    Continuous fun x =>
      cmp102Eq80SourcePi4FTCConnectedDomainActivity
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase vertexCoordinates W n coordinates (sigma x) remaining := by
  classical
  induction remaining generalizing T n sigma with
  | nil =>
      by_cases hn : n = 0
      · simpa [cmp102Eq80SourcePi4FTCConnectedDomainActivity, hn] using
          (continuous_const :
            Continuous (fun _ : T => (0 : ℝ)))
      · simpa [cmp102Eq80SourcePi4FTCConnectedDomainActivity, hn] using
          continuous_cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt_comp
            anchor K hc hmass hK D D₃ V₀ Δπ J A
            hAhead hrho hrate Cert htri hrange hΔ hΔ1
            vertexBase sigma hsigma vertexCoordinates
            coordinates W hRweak
            (fun x e => (hsigmaRegion x).2 e) hsmall hV₀
  | cons d tail ih =>
      let sigmaZero : T → FinBox 4 (2 * Q) → ℝ :=
        fun x => Function.update (sigma x) d 0
      have hsigmaZero (e : FinBox 4 (2 * Q)) :
          Continuous fun x => sigmaZero x e := by
        by_cases hed : e = d
        · subst e
          simpa [sigmaZero] using
            (continuous_const : Continuous (fun _ : T => (0 : ℝ)))
        · simpa [sigmaZero, Function.update_of_ne hed] using hsigma e
      have hsigmaZeroRegion (x : T) :
          CMP116RealPhysicalContourRegion Rweak (sigmaZero x) := by
        exact cmp116RealPhysicalContourRegion_update_uIcc
          Rweak hRweak (sigma x) d 0 (hsigmaRegion x) (by simp)
      have hVbase :
          ContDiff ℝ (n + tail.length) V₀ :=
        hV₀.of_le
          (WithTop.coe_le_coe.mpr
            (ENat.coe_le_coe.mpr (by simp [List.length_cons])))
      have hbase :
          Continuous fun x =>
            cmp102Eq80SourcePi4FTCConnectedDomainActivity
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
              vertexBase vertexCoordinates W n coordinates
              (sigmaZero x) tail :=
        ih n coordinates sigmaZero hsigmaZero hsigmaZeroRegion hVbase
      let sigmaFiber :
          (T × ℝ) → FinBox 4 (2 * Q) → ℝ :=
        fun p =>
          cmp116ClampedRealWeakeningCoordinatePath (sigma p.1) d p.2
      have hsigmaFiber (e : FinBox 4 (2 * Q)) :
          Continuous fun p : T × ℝ => sigmaFiber p e := by
        by_cases hed : e = d
        · subst e
          simpa [sigmaFiber,
            cmp116ClampedRealWeakeningCoordinatePath] using
            continuous_cmp116ClampUnit.comp continuous_snd
        · have hde : d ≠ e := Ne.symm hed
          simpa [sigmaFiber,
            cmp116ClampedRealWeakeningCoordinatePath,
            Function.update, hed, hde] using
            (hsigma e).comp continuous_fst
      have hsigmaFiberRegion (p : T × ℝ) :
          CMP116RealPhysicalContourRegion Rweak (sigmaFiber p) :=
        cmp116ClampedRealWeakeningCoordinatePath_mem_contourRegion
          Rweak hRweak (sigma p.1) (hsigmaRegion p.1) d p.2
      have hVfiber :
          ContDiff ℝ ((n + 1) + tail.length) V₀ := by
        simpa [add_assoc, add_comm,
          add_left_comm] using hV₀
      have hfiber :
          Continuous fun p : T × ℝ =>
            cmp102Eq80SourcePi4FTCConnectedDomainActivity
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
              vertexBase vertexCoordinates W (n + 1)
              (Fin.cons d coordinates)
              (sigmaFiber p) tail :=
        ih (T := T × ℝ) (n + 1) (Fin.cons d coordinates)
          sigmaFiber hsigmaFiber
          hsigmaFiberRegion hVfiber
      have hintegralClamped :
          Continuous fun x =>
            ∫ t in Set.uIcc (0 : ℝ) 1,
              cmp102Eq80SourcePi4FTCConnectedDomainActivity
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates)
                (sigmaFiber (x, t)) tail :=
        continuous_parametric_integral_of_continuous
          hfiber isCompact_uIcc
      have hintegralEq (x : T) :
          (∫ t in (0 : ℝ)..1,
              cmp102Eq80SourcePi4FTCConnectedDomainActivity
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates)
                (Function.update (sigma x) d t) tail) =
            ∫ t in Set.uIcc (0 : ℝ) 1,
              cmp102Eq80SourcePi4FTCConnectedDomainActivity
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates)
                (sigmaFiber (x, t)) tail := by
        rw [intervalIntegral.integral_of_le zero_le_one]
        rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
        simp only [Set.uIcc_of_le zero_le_one]
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro t ht
        have heq :
            sigmaFiber (x, t) = Function.update (sigma x) d t := by
          exact cmp116ClampedRealWeakeningCoordinatePath_eq_update
            (sigma x) d ht
        exact congrArg
          (fun u =>
            cmp102Eq80SourcePi4FTCConnectedDomainActivity
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
              vertexBase vertexCoordinates W (n + 1)
              (Fin.cons d coordinates) u tail)
          heq.symm
      have hintegral :
          Continuous fun x =>
            ∫ t in (0 : ℝ)..1,
              cmp102Eq80SourcePi4FTCConnectedDomainActivity
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase vertexCoordinates W (n + 1)
                (Fin.cons d coordinates)
                (Function.update (sigma x) d t) tail := by
        apply hintegralClamped.congr
        intro x
        exact (hintegralEq x).symm
      simpa [cmp102Eq80SourcePi4FTCConnectedDomainActivity, sigmaZero] using
        hbase.add hintegral

set_option maxHeartbeats 64000000 in
/-- Each recursive connected-domain contribution along one literal FTC
coordinate segment is interval integrable. -/
theorem intervalIntegrable_cmp102Eq80SourcePi4FTCConnectedDomainActivity_update
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (W : Finset (FinBox 4 (2 * Q)))
    (n : ℕ) (coordinates : Fin n → FinBox 4 (2 * Q))
    (endpointS : FinBox 4 (2 * Q) → ℝ)
    (d : FinBox 4 (2 * Q))
    (remaining : List (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hendpointS : CMP116RealPhysicalContourRegion Rweak endpointS)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hV₀ : ContDiff ℝ (n + remaining.length) V₀) :
    IntervalIntegrable
      (fun t =>
        cmp102Eq80SourcePi4FTCConnectedDomainActivity
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase vertexCoordinates W n coordinates
          (Function.update endpointS d t) remaining)
      MeasureTheory.volume 0 1 := by
  let sigma : ℝ → FinBox 4 (2 * Q) → ℝ :=
    cmp116ClampedRealWeakeningCoordinatePath endpointS d
  have hsigma (e : FinBox 4 (2 * Q)) :
      Continuous fun t => sigma t e :=
    continuous_cmp116ClampedRealWeakeningCoordinatePath_apply
      endpointS d e
  have hsigmaRegion (t : ℝ) :
      CMP116RealPhysicalContourRegion Rweak (sigma t) :=
    cmp116ClampedRealWeakeningCoordinatePath_mem_contourRegion
      Rweak hRweak endpointS hendpointS d t
  have hclamped :
      IntervalIntegrable
        (fun t =>
          cmp102Eq80SourcePi4FTCConnectedDomainActivity
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
            vertexBase vertexCoordinates W n coordinates
            (sigma t) remaining)
        MeasureTheory.volume 0 1 :=
    (continuous_cmp102Eq80SourcePi4FTCConnectedDomainActivity_comp
      anchor K hc hmass hK D D₃ V₀ Δπ J A
      hAhead hrho hrate Cert htri hrange hΔ hΔ1
      vertexBase vertexCoordinates W n coordinates sigma remaining
      hsigma hRweak hsigmaRegion hsmall hV₀).intervalIntegrable 0 1
  apply hclamped.congr
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le zero_le_one] using
      Set.uIoc_subset_uIcc ht
  have heq : sigma t = Function.update endpointS d t :=
    cmp116ClampedRealWeakeningCoordinatePath_eq_update
      endpointS d ht'
  exact congrArg
    (fun u =>
      cmp102Eq80SourcePi4FTCConnectedDomainActivity
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase vertexCoordinates W n coordinates u remaining)
    heq

set_option maxHeartbeats 64000000 in
/-- The complete recursive FTC total is the finite sum of the individually
integrable connected-domain activities. -/
theorem cmp102Eq80SourcePi4FTCConnectedDomainTotal_eq_sum_activity
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (history : List (FinBox 4 (2 * Q) × ℝ))
    (sigma : FinBox 4 (2 * Q) → ℝ)
    (remaining : List (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hsigma : CMP116RealPhysicalContourRegion Rweak sigma)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hV₀ : ContDiff ℝ (history.length + remaining.length) V₀) :
    cmp102Eq80SourcePi4FTCConnectedDomainTotal
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase vertexCoordinates history sigma remaining =
      ∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
        cmp102Eq80SourcePi4FTCConnectedDomainActivity
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase vertexCoordinates W history.length
          (cmp116FixedWeakeningCoordinateNames history) sigma remaining := by
  classical
  induction remaining generalizing history sigma with
  | nil =>
      cases history with
      | nil =>
          simp [cmp102Eq80SourcePi4FTCConnectedDomainTotal,
            cmp102Eq80SourcePi4FTCConnectedDomainActivity]
      | cons p history =>
          simp [cmp102Eq80SourcePi4FTCConnectedDomainTotal,
            cmp102Eq80SourcePi4FTCConnectedDomainActivity]
  | cons d tail ih =>
      have hbaseRegion :
          CMP116RealPhysicalContourRegion Rweak
            (Function.update sigma d 0) :=
        cmp116RealPhysicalContourRegion_update_uIcc
          Rweak hRweak sigma d 0 hsigma (by simp)
      have hVbase :
          ContDiff ℝ (history.length + tail.length) V₀ :=
        hV₀.of_le
          (WithTop.coe_le_coe.mpr
            (ENat.coe_le_coe.mpr (by simp [List.length_cons])))
      have hVfiber :
          ContDiff ℝ (((d, (0 : ℝ)) :: history).length + tail.length) V₀ := by
        simpa [List.length_cons, add_assoc, add_comm,
          add_left_comm] using hV₀
      rw [cmp102Eq80SourcePi4FTCConnectedDomainTotal,
        ih history (Function.update sigma d 0) hbaseRegion hVbase]
      have hfiber (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
          cmp102Eq80SourcePi4FTCConnectedDomainTotal
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
              vertexBase vertexCoordinates ((d, t) :: history)
              (Function.update sigma d t) tail =
            ∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
              cmp102Eq80SourcePi4FTCConnectedDomainActivity
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase vertexCoordinates W
                ((d, t) :: history).length
                (cmp116FixedWeakeningCoordinateNames ((d, t) :: history))
                (Function.update sigma d t) tail := by
        apply ih ((d, t) :: history) (Function.update sigma d t)
        · exact cmp116RealPhysicalContourRegion_update_uIcc
            Rweak hRweak sigma d t hsigma ht
        · simpa only [List.length_cons] using hVfiber
      calc
        (∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
            cmp102Eq80SourcePi4FTCConnectedDomainActivity
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
              vertexBase vertexCoordinates W history.length
              (cmp116FixedWeakeningCoordinateNames history)
              (Function.update sigma d 0) tail) +
            ∫ t in (0 : ℝ)..1,
              cmp102Eq80SourcePi4FTCConnectedDomainTotal
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase vertexCoordinates ((d, t) :: history)
                (Function.update sigma d t) tail =
          (∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
            cmp102Eq80SourcePi4FTCConnectedDomainActivity
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
              vertexBase vertexCoordinates W history.length
              (cmp116FixedWeakeningCoordinateNames history)
              (Function.update sigma d 0) tail) +
            ∫ t in (0 : ℝ)..1,
              ∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
                cmp102Eq80SourcePi4FTCConnectedDomainActivity
                  (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                  vertexBase vertexCoordinates W
                  ((d, t) :: history).length
                  (cmp116FixedWeakeningCoordinateNames ((d, t) :: history))
                  (Function.update sigma d t) tail := by
            apply congrArg
            apply intervalIntegral.integral_congr
            intro t ht
            exact hfiber t ht
        _ =
          (∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
            cmp102Eq80SourcePi4FTCConnectedDomainActivity
              (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
              vertexBase vertexCoordinates W history.length
              (cmp116FixedWeakeningCoordinateNames history)
              (Function.update sigma d 0) tail) +
            ∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
              ∫ t in (0 : ℝ)..1,
                cmp102Eq80SourcePi4FTCConnectedDomainActivity
                  (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                  vertexBase vertexCoordinates W
                  ((d, t) :: history).length
                  (cmp116FixedWeakeningCoordinateNames ((d, t) :: history))
                  (Function.update sigma d t) tail := by
            congr 1
            apply intervalIntegral.integral_finset_sum
            intro W _hW
            exact
              intervalIntegrable_cmp102Eq80SourcePi4FTCConnectedDomainActivity_update
                anchor K hc hmass hK D D₃ V₀ Δπ J A
                hAhead hrho hrate Cert htri hrange hΔ hΔ1
                vertexBase vertexCoordinates W
                ((d, (0 : ℝ)) :: history).length
                (cmp116FixedWeakeningCoordinateNames
                  ((d, (0 : ℝ)) :: history))
                sigma d tail hRweak hsigma hsmall hVfiber
        _ = ∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
              cmp102Eq80SourcePi4FTCConnectedDomainActivity
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase vertexCoordinates W history.length
                (cmp116FixedWeakeningCoordinateNames history)
                sigma (d :: tail) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro W _hW
            rw [cmp102Eq80SourcePi4FTCConnectedDomainActivity]
            congr 1

set_option maxHeartbeats 64000000 in
/-- The literal nondecoupled equation-(80) FTC remainder is exactly the
finite sum of the source-level connected-domain activities. -/
theorem
    cmp102Eq80SourcePi4FTCNondecoupledRemainder_eq_sum_connectedDomainActivity
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (vertexBase s : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates L : List (FinBox 4 (2 * Q)))
    (hvertexCoordinates : vertexCoordinates.Nodup)
    (hcover :
      ∀ d : FinBox 4 (2 * Q), d ∈ vertexCoordinates)
    (hL : L.Nodup)
    (hRweak : 1 ≤ Rweak)
    (hvertexBase :
      CMP116RealPhysicalContourRegion Rweak vertexBase)
    (hs : CMP116RealPhysicalContourRegion Rweak s)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hV₀ : ContDiff ℝ L.length V₀) :
    cmp102Eq80SourcePi4FTCNondecoupledRemainder
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        vertexBase vertexCoordinates s L A =
      ∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
        cmp102Eq80SourcePi4ConnectedDomainActivity
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase vertexCoordinates s L W := by
  calc
    _ = cmp102Eq80SourcePi4FTCConnectedDomainTotal
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase vertexCoordinates [] s L :=
      cmp102Eq80SourcePi4FTCNondecoupledRemainder_eq_connectedDomainTotal
        anchor K hc hmass hK D D₃ V₀ Δπ J A
        hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
        vertexBase s vertexCoordinates L hvertexCoordinates hcover hL
        hRweak hvertexBase hs hsmall hV₀
    _ = ∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
          cmp102Eq80SourcePi4FTCConnectedDomainActivity
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
            vertexBase vertexCoordinates W 0 Fin.elim0 s L :=
      cmp102Eq80SourcePi4FTCConnectedDomainTotal_eq_sum_activity
        anchor K hc hmass hK D D₃ V₀ Δπ J A
        hAhead hrho hrate Cert htri hrange hΔ hΔ1
        vertexBase vertexCoordinates [] s L hRweak hs hsmall
        (by simpa using hV₀)
    _ = _ := rfl

end

end YangMills.RG
