/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FTCFixedHistoryRecursion

/-!
# The complete FTC remainder with connected-domain leaves

The total below preserves the literal recursive FTC integrals.  At every
active leaf it inserts the already proved finite sum over physical connected
domains.  The terminal theorem identifies this object with the complete
nondecoupled remainder of the equation-(80) weakening tree.

The finite sum deliberately remains inside the recursive integrals here.
Moving it outside to define individual activities requires interval
integrability of every recursive domain contribution and is proved
separately; no linearity of a potentially nonintegrable Bochner integral is
used silently.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- Complete recursive FTC total whose active leaves are localized over the
proved physical connected-domain labels. -/
noncomputable def cmp102Eq80SourcePi4FTCConnectedDomainTotal
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
    (vertexCoordinates : List (FinBox 4 (2 * Q))) :
    List (FinBox 4 (2 * Q) × ℝ) →
      (FinBox 4 (2 * Q) → ℝ) →
      List (FinBox 4 (2 * Q)) → ℝ
  | [], _sigma, [] => 0
  | history@(_ :: _), sigma, [] =>
      ∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
        cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase sigma vertexCoordinates
          (cmp116FixedWeakeningCoordinateNames history) W
  | history, sigma, d :: tail =>
      cmp102Eq80SourcePi4FTCConnectedDomainTotal
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase vertexCoordinates history
          (Function.update sigma d 0) tail +
        ∫ t in (0 : ℝ)..1,
          cmp102Eq80SourcePi4FTCConnectedDomainTotal
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
            vertexBase vertexCoordinates ((d, t) :: history)
            (Function.update sigma d t) tail

/-- Updating a physical real contour coordinate inside the unit interval
preserves the certified contour region. -/
theorem cmp116RealPhysicalContourRegion_update_uIcc
    {D : Type*} [DecidableEq D]
    (Rweak : ℝ) (hRweak : 1 ≤ Rweak)
    (sigma : D → ℝ) (d : D) (t : ℝ)
    (hsigma : CMP116RealPhysicalContourRegion Rweak sigma)
    (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
    CMP116RealPhysicalContourRegion Rweak
      (Function.update sigma d t) :=
  ⟨cmp116UpdateRealWeakening_unitShifted sigma d t ht hsigma.1,
    cmp116UpdateRealWeakening_cap sigma d t Rweak ht hRweak hsigma.2⟩

set_option maxHeartbeats 64000000 in
/-- Source-specific induction replacing every active literal FTC leaf by its
proved connected-domain expansion. -/
theorem cmp116FixedHistoryFTCRecursion_eq_connectedDomainTotal
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
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (hvertexCoordinates : vertexCoordinates.Nodup)
    (hcover :
      ∀ d : FinBox 4 (2 * Q), d ∈ vertexCoordinates)
    (history : List (FinBox 4 (2 * Q) × ℝ))
    (sigma : FinBox 4 (2 * Q) → ℝ)
    (remaining : List (FinBox 4 (2 * Q)))
    (hcombined :
      ((history.map Prod.fst) ++ remaining).Nodup)
    (hvalues : ∀ p ∈ history, sigma p.1 = p.2)
    (hRweak : 1 ≤ Rweak)
    (hvertexBase :
      CMP116RealPhysicalContourRegion Rweak vertexBase)
    (hsigma : CMP116RealPhysicalContourRegion Rweak sigma)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hV₀ : ContDiff ℝ (history.length + remaining.length) V₀) :
    cmp116FixedHistoryFTCRecursion
        (fun tau =>
          cmp102Eq80SourcePi4RealPotentialVertexPolynomial
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            vertexBase vertexCoordinates tau A)
        history sigma remaining =
      cmp102Eq80SourcePi4FTCConnectedDomainTotal
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase vertexCoordinates history sigma remaining := by
  induction remaining generalizing history sigma with
  | nil =>
      cases history with
      | nil =>
          simp [cmp116FixedHistoryFTCRecursion,
            cmp102Eq80SourcePi4FTCConnectedDomainTotal]
      | cons p history =>
          have hhistory :
              (List.map Prod.fst (p :: history)).Nodup := by
            simpa using hcombined
          have hVleaf :
              ContDiff ℝ (p :: history).length V₀ := by
            simpa using hV₀
          simpa [cmp116FixedHistoryFTCRecursion,
            cmp102Eq80SourcePi4FTCConnectedDomainTotal] using
            cmp116FixedWeakeningCoordinateDerivatives_eq_sum_connectedPhysicalDomains
              anchor K hc hmass hK D D₃ V₀ Δπ J A
              hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
              vertexBase sigma vertexCoordinates hvertexCoordinates hcover
              (p :: history) (by simp) hhistory hvalues hRweak
              hvertexBase hsigma hsmall hVleaf
  | cons d tail ih =>
      have hparts := List.nodup_append.mp hcombined
      have hhistory : (history.map Prod.fst).Nodup := hparts.1
      have hremaining : (d :: tail).Nodup := hparts.2.1
      have hcross := hparts.2.2
      have hdTail : d ∉ tail := (List.nodup_cons.mp hremaining).1
      have htail : tail.Nodup := (List.nodup_cons.mp hremaining).2
      have hdHistory : d ∉ history.map Prod.fst := by
        intro hd
        exact hcross d hd d (by simp) rfl
      have hbaseCombined :
          ((history.map Prod.fst) ++ tail).Nodup :=
        List.nodup_append.mpr
          ⟨hhistory, htail, fun a ha b hb => hcross a ha b (by simp [hb])⟩
      have hfiberCombined :
          ((((d, (0 : ℝ)) :: history).map Prod.fst) ++ tail).Nodup := by
        rw [List.nodup_append]
        refine ⟨?_, htail, ?_⟩
        · simpa using hhistory.cons hdHistory
        · intro a ha b hb
          rcases (by simpa using ha : a = d ∨ a ∈ history.map Prod.fst) with
            rfl | ha'
          · exact fun hab => hdTail (hab ▸ hb)
          · exact hcross a ha' b (by simp [hb])
      have hbaseValues :
          ∀ p ∈ history,
            (Function.update sigma d 0) p.1 = p.2 := by
        intro p hp
        rw [Function.update_of_ne]
        · exact hvalues p hp
        · intro h
          subst d
          exact hdHistory
            (List.mem_map.mpr ⟨p, hp, rfl⟩)
      have hbaseRegion :
          CMP116RealPhysicalContourRegion Rweak
            (Function.update sigma d 0) :=
        cmp116RealPhysicalContourRegion_update_uIcc
          Rweak hRweak sigma d 0 hsigma (by simp)
      have hbaseV :
          ContDiff ℝ (history.length + tail.length) V₀ :=
        hV₀.of_le (by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          gcongr
          exact le_add_of_nonneg_right (by norm_num))
      rw [cmp116FixedHistoryFTCRecursion,
        cmp102Eq80SourcePi4FTCConnectedDomainTotal,
        ih history (Function.update sigma d 0) hbaseCombined
          hbaseValues hbaseRegion hbaseV]
      apply congrArg
      apply intervalIntegral.integral_congr
      intro t ht
      have hfiberValues :
          ∀ p ∈ (d, t) :: history,
            (Function.update sigma d t) p.1 = p.2 := by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hp | hp
        · subst p
          simp
        · rw [Function.update_of_ne]
          · exact hvalues p hp
          · intro h
            subst d
            exact hdHistory
              (List.mem_map.mpr ⟨p, hp, rfl⟩)
      have hfiberRegion :
          CMP116RealPhysicalContourRegion Rweak
            (Function.update sigma d t) :=
        cmp116RealPhysicalContourRegion_update_uIcc
          Rweak hRweak sigma d t hsigma ht
      have hfiberV :
          ContDiff ℝ (((d, t) :: history).length + tail.length) V₀ := by
        simpa [add_assoc, add_comm, add_left_comm] using hV₀
      exact ih ((d, t) :: history) (Function.update sigma d t)
        (by simpa using hfiberCombined) hfiberValues hfiberRegion hfiberV

set_option maxHeartbeats 64000000 in
/-- Terminal connected-domain dictionary for the complete physical
nondecoupled FTC remainder.  All recursive interval integrals are retained. -/
theorem
    cmp102Eq80SourcePi4FTCNondecoupledRemainder_eq_connectedDomainTotal
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
      cmp102Eq80SourcePi4FTCConnectedDomainTotal
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase vertexCoordinates [] s L := by
  let f := fun tau =>
    cmp102Eq80SourcePi4RealPotentialVertexPolynomial
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      vertexBase vertexCoordinates tau A
  unfold cmp102Eq80SourcePi4FTCNondecoupledRemainder
  unfold cmp102Eq80SourcePi4VertexPolynomialFTCExpansionTree
  rw [← cmp116FixedHistoryFTCRecursion_nil f s L]
  exact
    cmp116FixedHistoryFTCRecursion_eq_connectedDomainTotal
      anchor K hc hmass hK D D₃ V₀ Δπ J A
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      vertexBase vertexCoordinates hvertexCoordinates hcover
      [] s L (by simpa using hL) (by simp) hRweak
      hvertexBase hs hsmall (by simpa using hV₀)

end

end YangMills.RG
