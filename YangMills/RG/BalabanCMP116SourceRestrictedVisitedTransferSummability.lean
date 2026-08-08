/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RestrictedVisitedTransferAbsoluteSummability
import YangMills.RG.BalabanCMP116SourceRestrictedVisitedTransferPower
import YangMills.RG.BalabanCMP99PatchedParametrixWeightedWalk
import YangMills.RG.BalabanCMP116SourcePi4TerminalGroupedPhysicalWeightedRow
import YangMills.RG.BalabanCMP116SourceSigmaZeroActiveCarrier
import YangMills.RG.PhysicalWeightedRowKernelMatrix

/-!
# Physical source criterion for restricted transfer summability

The visited weakening weight is bounded once, on the union of coordinates
first activated by a physical tail.  The ordered continuation product is
then transported as a whole from its fixed-rate physical weighted-row
estimate to the canonical complex matrix.  Consequently no coordinate
matrix conversion constant is raised to the walk length.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

set_option maxHeartbeats 3000000

/-- A visited-state weakening product charges at most `B` new coordinates
per tail step. -/
theorem norm_cmp116ComplexVisitedWeakeningProduct_tail_le
    {Label Domain Delta : Type*} [DecidableEq Delta]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (sigma : Delta → ℂ)
    (B : ℕ) (Rweak : ℝ)
    (hB : ∀ X, (domainActive X).card ≤ B)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d ∈ carrier, ‖sigma d‖ ≤ Rweak)
    (visited : CMP116RestrictedVisitedState carrier) :
    ∀ tail : List (CMP99WalkStep Label Domain),
      ‖cmp116ComplexVisitedWeakeningProduct sigma visited.1
          (tail.map fun step => domainActive step.domain ∩ carrier)‖ ≤
        Rweak ^ (B * tail.length) := by
  intro tail
  induction tail generalizing visited with
  | nil =>
      simp [cmp116ComplexVisitedWeakeningProduct]
  | cons step rest ih =>
      let newly :=
        (domainActive step.domain ∩ carrier) \ visited.1
      have hnewCarrier : newly ⊆ carrier :=
        Finset.sdiff_subset.trans Finset.inter_subset_right
      have hnewActive : newly ⊆ domainActive step.domain :=
        Finset.sdiff_subset.trans Finset.inter_subset_left
      have hcard : newly.card ≤ B :=
        (Finset.card_le_card hnewActive).trans (hB step.domain)
      have hmono :
          ‖cmp116ComplexWeakeningMonomial newly sigma‖ ≤
            Rweak ^ newly.card := by
        apply norm_cmp116ComplexWeakeningMonomial_le_pow_card
          newly sigma (fun _ => Rweak - 1) Rweak
          (le_trans (by norm_num) hRweak)
        · intro d hd
          convert hcap d (hnewCarrier hd) using 1
          ring
        · intro d hd
          convert le_rfl using 1
          ring
      have hstep :
          ‖cmp116ComplexWeakeningMonomial newly sigma‖ ≤ Rweak ^ B :=
        hmono.trans (pow_le_pow_right₀ hRweak hcard)
      simp only [List.map_cons, cmp116ComplexVisitedWeakeningProduct,
        norm_mul]
      change
        ‖cmp116ComplexWeakeningMonomial newly sigma‖ *
            ‖cmp116ComplexVisitedWeakeningProduct sigma
              (visited.1 ∪ (domainActive step.domain ∩ carrier))
              (rest.map fun next =>
                domainActive next.domain ∩ carrier)‖ ≤
          Rweak ^ (B * (rest.length + 1))
      calc
        _ ≤ Rweak ^ B * Rweak ^ (B * rest.length) :=
          mul_le_mul hstep
            (ih (CMP116RestrictedVisitedState.update carrier visited
              (domainActive step.domain)))
            (norm_nonneg _) (pow_nonneg (le_trans (by norm_num) hRweak) _)
        _ = Rweak ^ (B * (rest.length + 1)) := by
          rw [← pow_add]
          congr 1
          simp [Nat.mul_add, Nat.add_comm]

/-- The canonical matrix of an entire physical continuation tail is bounded
after one coordinate transport.  The fixed matrix conversion factor is
outside the walk-length power. -/
theorem norm_cmp116PhysicalContinuationMatrix_tail_prod_le
    {Label Domain : Type*}
    {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (continuation : Domain →
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc)
    {rho rate : ℝ}
    (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ d : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (hcontinuation : ∀ domain,
      PhysicalCovarianceWeightedRowKernelBound
        (continuation domain) physicalBondDist rho rate)
    (htri : ∀ target source middle : PhysicalBond d N,
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (tail : List (CMP99WalkStep Label Domain)) :
    ‖(tail.map fun step =>
        cmp116PhysicalEndomorphismComplexMatrix
          (continuation step.domain)).prod‖ ≤
      max 1 (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum d rate) *
        rho ^ tail.length := by
  let conversion : ℝ :=
    ((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum d rate
  have hconversion : 0 ≤ conversion := by
    dsimp [conversion]
    exact mul_nonneg (Nat.cast_nonneg _)
      (cmp99PhysicalBondGeometricRowSum_nonneg hgeom)
  cases tail with
  | nil =>
      simp only [List.map_nil, List.prod_nil, List.length_nil, pow_zero,
        mul_one, norm_one]
      exact le_max_left 1 conversion
  | cons step rest =>
      have hrest :
          ∀ next,
            next ∈ rest.map
                (fun next => continuation next.domain) →
              PhysicalCovarianceWeightedRowKernelBound
                next physicalBondDist rho rate := by
        intro next hnext
        obtain ⟨nextStep, _hnextStep, rfl⟩ := List.mem_map.mp hnext
        exact hcontinuation nextStep.domain
      have hweighted :
          PhysicalCovarianceWeightedRowKernelBound
            (physicalOrderedProduct
              (continuation step.domain)
              (rest.map fun next =>
                continuation next.domain))
            physicalBondDist (rho * rho ^ rest.length) rate := by
        simpa only [List.length_map] using
          physicalCovarianceWeightedRowKernelBound_orderedProduct
            (d := d) (N := N) (Nc := Nc)
            (rho := rho) (rate := rate)
            physicalBondDist htri
            (continuation step.domain)
            (hcontinuation step.domain)
            (rest.map fun next =>
              continuation next.domain)
            hrest
      have hmatrix :
          ‖cmp116PhysicalEndomorphismComplexMatrix
              (physicalOrderedProduct
                (continuation step.domain)
                (rest.map fun next =>
                  continuation next.domain))‖ ≤
            (rho * rho ^ rest.length) * conversion := by
        simpa [conversion] using
          linfty_opNorm_cmp116PhysicalEndomorphismComplexMatrix_le_of_weightedRow
            (d := d) (N := N) (Nc := Nc)
            (A := rho * rho ^ rest.length) (rate := rate)
            (physicalOrderedProduct
              (continuation step.domain)
              (rest.map fun next =>
                continuation next.domain))
            hrate hgeom hweighted
      have htransport :
          ((step :: rest).map fun next =>
              cmp116PhysicalEndomorphismComplexMatrix
                (continuation next.domain)).prod =
            cmp116PhysicalEndomorphismComplexMatrix
              (physicalOrderedProduct
                (continuation step.domain)
                (rest.map fun next =>
                  continuation next.domain)) := by
        rw [physicalOrderedProduct_eq_head_mul_prod]
        symm
        simpa only [List.map_cons, List.prod_cons, List.map_map,
          Function.comp_apply] using
          (cmp116PhysicalEndomorphismComplexMatrix_list_prod
            ((step :: rest).map fun next =>
              continuation next.domain))
      rw [htransport]
      calc
        _ ≤ (rho * rho ^ rest.length) * conversion := hmatrix
        _ = conversion * rho ^ (rest.length + 1) := by
          rw [pow_succ']
          ring
        _ ≤ max 1 conversion * rho ^ (rest.length + 1) :=
          mul_le_mul_of_nonneg_right (le_max_right 1 conversion)
            (pow_nonneg hrho _)

/-- Source `Pi^4` specialization of the one-shot continuation-tail matrix
bound. -/
theorem norm_cmp116SourcePi4RestrictedContinuationMatrix_tail_prod_le
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate : ℝ}
    (hrho : 0 ≤ rho) (hrate : 0 < rate)
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
    (tail : List (CMP99WalkStep Unit
      ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)))) :
    ‖(tail.map fun step =>
        cmp116SourcePi4RestrictedContinuationMatrix
          K hc hmass hK step.label step.domain).prod‖ ≤
      max 1 (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum 4 rate) *
        rho ^ tail.length := by
  simpa [cmp116SourcePi4RestrictedContinuationMatrix] using
    (norm_cmp116PhysicalContinuationMatrix_tail_prod_le
      (Label := Unit)
      (continuation := fun chart =>
        cmp99PhysicalPatchContinuation
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK chart)
      hrho hrate hgeom Cert.continuation htri tail)

/-- Combining the exact visited-state factorization with a whole-tail matrix
bound gives the tail estimate consumed by the transfer-power criterion. -/
theorem norm_cmp116RestrictedVisitedTailProduct_le_of_matrix_tail
    {Label Domain Delta : Type*} [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (B : ℕ) (A rho Rweak : ℝ)
    (hB : ∀ X, (domainActive X).card ≤ B)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d ∈ carrier, ‖sigma d‖ ≤ Rweak)
    (hmatrix : ∀ tail : List (CMP99WalkStep Label Domain),
      ‖(tail.map fun step => R step.label step.domain).prod‖ ≤
        A * rho ^ tail.length)
    (visited : CMP116RestrictedVisitedState carrier)
    (tail : List (CMP99WalkStep Label Domain)) :
    ‖cmp116RestrictedVisitedTailProduct
        carrier domainActive R sigma visited tail‖ ≤
      A * rho ^ tail.length * Rweak ^ (B * tail.length) := by
  rw [← cmp116ComplexVisitedWeakeningProduct_smul_tailProd_eq
    carrier domainActive R sigma visited tail, norm_smul]
  have hweight :=
    norm_cmp116ComplexVisitedWeakeningProduct_tail_le
      carrier domainActive sigma B Rweak hB hRweak hcap visited tail
  calc
    ‖cmp116ComplexVisitedWeakeningProduct sigma visited.1
        (tail.map fun step => domainActive step.domain ∩ carrier)‖ *
        ‖(tail.map fun step => R step.label step.domain).prod‖ ≤
      Rweak ^ (B * tail.length) *
        (A * rho ^ tail.length) :=
      mul_le_mul hweight (hmatrix tail) (norm_nonneg _)
        (pow_nonneg (le_trans (by norm_num) hRweak) _)
    _ = A * rho ^ tail.length * Rweak ^ (B * tail.length) := by ring

/-- Literal source `Pi^4` geometry and the physical weighted-row certificate
produce summability of every restricted visited-state transfer power. -/
theorem summable_cmp116SourcePi4RestrictedVisitedTransferMatrix_pow
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate : ℝ}
    (hrho : 0 ≤ rho) (hrate : 0 < rate)
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
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (Rweak : ℝ) (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d ∈ carrier, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      (cmp116SourcePi4TerminalBranching Δ : ℝ) *
        rho * Rweak ^ 10000 < 1) :
    Summable fun n : ℕ =>
      cmp116RestrictedVisitedTransferMatrix
        carrier
        (cmp116SourcePi4RestrictedDomainActive anchor)
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
        sigma ^ n := by
  let Dict :=
    cmp116SourceSigmaZeroPi4PhysicalChartDictionary
      (Label := Unit) anchor hsourceRange
  let conversion : ℝ :=
    ((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate
  let A : ℝ := max 1 conversion
  have hA : 0 ≤ A := by
    exact le_trans (by norm_num) (le_max_left 1 conversion)
  have hbranch :
      ∀ X,
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R X).card ≤
            cmp116SourcePi4TerminalBranching Δ := by
    intro X
    have h :=
      Dict.card_physicalSuccessorSteps_le_labeledSimpleDomainBound
        Δ hΔ hΔ1 X
    simpa [Dict, cmp116SourcePi4TerminalBranching] using h
  have hactive :
      ∀ X,
        (cmp116SourcePi4RestrictedDomainActive anchor X).card ≤
          10000 := by
    intro X
    have h := Dict.active_card_le X
    simpa [Dict, cmp116SourcePi4RestrictedDomainActive] using h
  let sourceCell : FinBox 4 Q := Classical.arbitrary (FinBox 4 Q)
  let sourceChart : CMP99SourcePi4Chart Unit Q :=
    ⟨(), cmp99SourcePi4CollarDomain sourceCell⟩
  have hsourceChart :
      sourceChart ∈ (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) := by
    rw [mem_cmp99SourcePi4Charts_iff]
    exact (mem_cmp99SourcePi4Domains_iff
      (cmp99SourcePi4CollarDomain sourceCell)).mpr ⟨sourceCell, rfl⟩
  letI : Nonempty ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)) :=
    ⟨⟨sourceChart, hsourceChart⟩⟩
  apply summable_cmp116RestrictedVisitedTransferMatrix_pow_of_tail
    carrier
    (cmp116SourcePi4RestrictedDomainActive anchor)
    (cmp99PhysicalPatchSuccessorSteps
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      (cmp99SourcePi4ChartCore (M := M))
      cmp99SourcePi4ChartEnlarged physicalBondDist R)
    (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
    sigma
    (cmp116SourcePi4TerminalBranching Δ) 10000 A rho Rweak
    hbranch hA hrho (le_trans (by norm_num) hRweak)
  · intro n source tail htail
    have hlen :
        tail.length = n :=
      length_eq_of_mem_cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        htail
    have hmatrix :
        ∀ physicalTail : List (CMP99WalkStep Unit
            ↥(cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))),
          ‖(physicalTail.map fun step =>
              cmp116SourcePi4RestrictedContinuationMatrix
                K hc hmass hK step.label step.domain).prod‖ ≤
            A * rho ^ physicalTail.length := by
      intro physicalTail
      exact
        norm_cmp116SourcePi4RestrictedContinuationMatrix_tail_prod_le
          K hc hmass hK hrho hrate hgeom Cert htri physicalTail
    simpa [hlen] using
      (norm_cmp116RestrictedVisitedTailProduct_le_of_matrix_tail
        carrier
        (cmp116SourcePi4RestrictedDomainActive anchor)
        (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
        sigma 10000 A rho Rweak hactive hRweak hcap hmatrix
        source.2 tail)
  exact hsmall

end

end YangMills.RG
