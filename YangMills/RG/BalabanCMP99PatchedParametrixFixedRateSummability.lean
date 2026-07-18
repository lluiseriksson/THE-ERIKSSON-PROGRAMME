/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixGeometricWeightedDecay
import YangMills.RG.BalabanCMP99LabeledPhysicalChartDictionary

/-!
# Pointwise summability of the fixed-rate CMP99 patched walk

The operator-norm walk series and the fixed-rate kernel series use genuinely
different continuation ratios.  This file sums the latter without identifying
them: after fixing source, target, and a source Lie vector, the weighted-row
certificate gives a vector-valued walk term bounded by

`Ahead * exp (-mu * distance) * norm(v) * rho_mu^n`.

The existing source branching and active-carrier count then prove summability
under the visible condition `K * rho_mu * Rweak^B < 1`.  No bilateral Schur
conversion to an operator norm is used or claimed.
-/

open scoped BigOperators

namespace YangMills.RG

noncomputable section

universe u v w z

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Radial walk summability for an arbitrary vector-valued term.  This is the
nonmultiplicative form needed after evaluating an ordered physical operator at
fixed source and target bonds. -/
theorem summable_cmp99AnchoredWalk_radialMajorant_of_term
    {Label : Type u} {Domain : Type v} {Cube : Type w} {E : Type z}
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Cube]
    [NormedAddCommGroup E]
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (X0 : Domain) (domainActive : Domain → Finset Cube)
    (term : CMP99AnchoredWalk successors X0 → E)
    (K B : ℕ) (A rho Rweak : ℝ)
    (hK : ∀ X, (successors X).card ≤ K)
    (hB : ∀ X, (domainActive X).card ≤ B)
    (hA : 0 ≤ A) (hrho : 0 ≤ rho) (hRweak : 1 ≤ Rweak)
    (hsmall : (K : ℝ) * rho * Rweak ^ B < 1)
    (hterm : ∀ walk, ‖term walk‖ ≤ A * rho ^ walk.1) :
    Summable fun walk : CMP99AnchoredWalk successors X0 =>
      Rweak ^ (walk.active domainActive).card * ‖term walk‖ := by
  let q : ℝ := (K : ℝ) * rho * Rweak ^ B
  have hq : 0 ≤ q := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg K) hrho)
    (pow_nonneg (by linarith) B)
  have hgeom : Summable fun n : ℕ => A * Rweak ^ B * q ^ n := by
    have hs : Summable fun n : ℕ => q ^ n :=
      summable_geometric_of_norm_lt_one (by
        rw [Real.norm_eq_abs, abs_of_nonneg hq]
        exact hsmall)
    exact hs.mul_left (A * Rweak ^ B)
  rw [summable_sigma_of_nonneg (fun walk =>
    mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _))]
  constructor
  · intro n
    exact Summable.of_finite
  · refine Summable.of_nonneg_of_le
      (fun n => tsum_nonneg fun _ =>
        mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _)) ?_ hgeom
    intro n
    rw [tsum_fintype]
    calc
      ∑ walk : ↥(cmp99AdmissibleTails successors X0 n),
          Rweak ^ (CMP99AnchoredWalk.active domainActive
            (⟨n, walk⟩ : CMP99AnchoredWalk successors X0)).card *
            ‖term (⟨n, walk⟩ : CMP99AnchoredWalk successors X0)‖
          ≤ ∑ _walk : ↥(cmp99AdmissibleTails successors X0 n),
            Rweak ^ (B * (n + 1)) * (A * rho ^ n) := by
        apply Finset.sum_le_sum
        intro walk _
        exact mul_le_mul
          (pow_le_pow_right₀ hRweak
            (CMP99AnchoredWalk.card_active_le_mul_length_add_one
              domainActive B hB
              (⟨n, walk⟩ : CMP99AnchoredWalk successors X0)))
          (hterm ⟨n, walk⟩) (norm_nonneg _)
          (pow_nonneg (by linarith) _)
      _ = ((cmp99AdmissibleTails successors X0 n).card : ℝ) *
          (Rweak ^ (B * (n + 1)) * (A * rho ^ n)) := by simp
      _ ≤ ((K ^ n : ℕ) : ℝ) *
          (Rweak ^ (B * (n + 1)) * (A * rho ^ n)) := by
        gcongr
        exact_mod_cast
          card_cmp99AdmissibleTails_le_pow successors K hK n X0
      _ = A * Rweak ^ B * q ^ n := by
        dsimp [q]
        push_cast
        rw [pow_mul, pow_succ]
        ring

/-- Value of the literal physical patched-walk operator at one source impulse
and one target bond. -/
noncomputable def cmp99PhysicalAnchoredPatchWalkValue
    {Label ι : Type*} [DecidableEq Label] [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι) (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {successors : ↥charts → Finset (CMP99WalkStep Label ↥charts)}
    {left : ↥charts}
    (source target : PhysicalBond d N) (v : SUNLieCoord Nc)
    (walk : CMP99AnchoredWalk successors left) : SUNLieCoord Nc :=
  walk.term
      (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
      (fun _ => cmp99PhysicalPatchContinuation
        charts K enlarged core hc hmass hK)
    (singlePhysicalBondCochain source v) target

/-- The factorwise weighted certificate gives the exact fixed-rate term
majorant after evaluation at one source and target. -/
theorem norm_cmp99PhysicalAnchoredPatchWalkValue_le_fixedRate
    {Label ι : Type*} [DecidableEq Label] [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    {charts : Finset ι} {K : PhysicalEndomorphism d N Nc}
    {enlarged core : ι → Finset (PhysicalBond d N)}
    {c mass : ℝ} {hc : 0 < c} {hmass : 0 < mass}
    {hK : IsCoerciveCLM K c}
    {Ahead rho rate : ℝ}
    (Cert : CMP99PhysicalPatchWeightedCertificate charts K enlarged core
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrate : 0 < rate)
    {successors : ↥charts → Finset (CMP99WalkStep Label ↥charts)}
    {left : ↥charts}
    (source target : PhysicalBond d N) (v : SUNLieCoord Nc)
    (walk : CMP99AnchoredWalk successors left) :
    ‖cmp99PhysicalAnchoredPatchWalkValue charts K enlarged core
        hc hmass hK source target v walk‖ ≤
      (Ahead * Real.exp (-(rate *
        (physicalBondDist target source : ℝ))) * ‖v‖) *
        rho ^ walk.1 := by
  have hdecay :=
    Cert.orderedProduct_exponentialKernelBound_toward_eq3108
      (fun x y z => physicalBondDist_triangle x z y)
      hrate left (walk.toGeneralizedWalk.tail.map CMP99WalkStep.domain)
  have hpoint := hdecay.2.2 source target v
  rw [List.length_map] at hpoint
  have hlen : walk.toGeneralizedWalk.tail.length = walk.1 := by
    simpa [CMP99GeneralizedWalk.length] using
      walk.toGeneralizedWalk_length
  rw [hlen] at hpoint
  have htermEq := cmp99PhysicalWalkTerm_eq_orderedProduct
    charts K enlarged core hc hmass hK walk.toGeneralizedWalk
  unfold cmp99PhysicalAnchoredPatchWalkValue
  rw [CMP99AnchoredWalk.term, htermEq]
  calc
    _ ≤ (Ahead * rho ^ walk.1) *
        Real.exp (-(rate *
          (physicalBondDist target source : ℝ))) * ‖v‖ := by
      simpa [List.map_map] using hpoint
    _ = (Ahead * Real.exp (-(rate *
          (physicalBondDist target source : ℝ))) * ‖v‖) *
        rho ^ walk.1 := by ring

/-- Source-branching summability of the fixed-rate physical kernel series.

The continuation ratio is the weighted spatial ratio from `Cert`; no
operator-norm smallness is substituted for it. -/
theorem CMP99LabeledPhysicalChartDictionary.summable_fixedRatePatchWalkValues
    {V : Type u} [Fintype V] [DecidableEq V]
    {Cube : Type v} [DecidableEq Cube]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type w} [DecidableEq ι]
    {Label : Type z} [Fintype Label] [DecidableEq Label]
    {d N Nc S B Rrange : ℕ} [NeZero N]
    (Dict : CMP99LabeledPhysicalChartDictionary
      (ι := ι) (Label := Label) (V := V) (Cube := Cube)
      (d := d) (N := N) G S B physicalBondDist Rrange)
    (K : PhysicalEndomorphism d N Nc)
    {c mass : ℝ} {hc : 0 < c} {hmass : 0 < mass}
    {hK : IsCoerciveCLM K c}
    {Ahead rho rate : ℝ}
    (Cert : CMP99PhysicalPatchWeightedCertificate
      Dict.charts K Dict.enlarged Dict.core hc hmass hK
      physicalBondDist Ahead rho rate)
    (hrate : 0 < rate)
    (Delta : ℕ) (hDelta : ∀ x, G.degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (left : ↥Dict.charts)
    (source target : PhysicalBond d N) (v : SUNLieCoord Nc)
    (s : Cube → ℝ) (Rweak : ℝ) (hRweak : 1 ≤ Rweak)
    (hsmall :
      ((Fintype.card Label *
          (S * (S + 1) * Delta ^ (2 * S)) : ℕ) : ℝ) *
        rho * Rweak ^ B < 1)
    (hs : s ∈ cmp116WeakeningPolydisc Rweak) :
    Summable fun walk : CMP99AnchoredWalk
        (cmp99PhysicalPatchSuccessorSteps
          Dict.charts Dict.core Dict.enlarged physicalBondDist Rrange) left =>
      cmp116WeakeningMonomial (walk.active Dict.domainActive) s •
        cmp99PhysicalAnchoredPatchWalkValue
          Dict.charts K Dict.enlarged Dict.core hc hmass hK
          source target v walk := by
  let A : ℝ := Ahead * Real.exp (-(rate *
    (physicalBondDist target source : ℝ))) * ‖v‖
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (Cert.head left).1 (Real.exp_pos _).le)
      (norm_nonneg v)
  have hrho : 0 ≤ rho := (Cert.continuation left).1
  have hmajor := summable_cmp99AnchoredWalk_radialMajorant_of_term
    (cmp99PhysicalPatchSuccessorSteps
      Dict.charts Dict.core Dict.enlarged physicalBondDist Rrange)
    left Dict.domainActive
    (cmp99PhysicalAnchoredPatchWalkValue
      Dict.charts K Dict.enlarged Dict.core hc hmass hK source target v)
    (Fintype.card Label *
      (S * (S + 1) * Delta ^ (2 * S))) B A rho Rweak
    (fun current =>
      CMP99LabeledPhysicalChartDictionary.card_physicalSuccessorSteps_le_labeledSimpleDomainBound
        Dict Delta hDelta hDelta1 current)
    Dict.active_card_le hA hrho hRweak hsmall
    (fun walk => by
      dsimp [A]
      exact norm_cmp99PhysicalAnchoredPatchWalkValue_le_fixedRate
        Cert hrate source target v walk)
  exact summable_cmp116WeakenedRandomWalkSeries
    (CMP99AnchoredWalk.active Dict.domainActive)
    (cmp99PhysicalAnchoredPatchWalkValue
      Dict.charts K Dict.enlarged Dict.core hc hmass hK source target v)
    s Rweak (zero_le_one.trans hRweak) hs hmajor

end

end YangMills.RG
