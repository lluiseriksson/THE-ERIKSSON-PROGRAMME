/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FTCDecoupledResidual

/-!
# Domain-indexed recursion for the complete physical FTC remainder

This file defines the source-form candidate for the contribution of one
physical connected domain to the complete equation-(80) FTC remainder.

The recursion follows the literal tree:

* the base branch sets the current coordinate to zero;
* the fiber branch integrates that coordinate over `[0,1]`;
* every fiber prepends the newly differentiated coordinate to the derivative
  list, matching the order in `iteratedFDeriv_succ_apply_left`;
* a terminal nonempty derivative list is evaluated by the already constructed
  physical Faà di Bruno domain coefficient.

No post-hoc difference is used.  The equality between the finite sum of these
domain contributions and `cmp102Eq80SourcePi4FTCNondecoupledRemainder` is the
next theorem; here we first prove the exact support invariants needed by that
induction.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- Coordinate names retained by a reverse-chronological FTC history. -/
def cmp116FixedWeakeningCoordinateNames
    {D : Type*} :
    (history : List (D × ℝ)) → Fin history.length → D
  | [] => Fin.elim0
  | (d, _) :: history =>
      Fin.cons d (cmp116FixedWeakeningCoordinateNames history)

theorem cmp116FixedWeakeningCoordinateNames_mem
    {D : Type*} (history : List (D × ℝ))
    (i : Fin history.length) :
    cmp116FixedWeakeningCoordinateNames history i ∈ history.map Prod.fst := by
  induction history with
  | nil => exact Fin.elim0 i
  | cons p history ih =>
      rcases p with ⟨d, t⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [cmp116FixedWeakeningCoordinateNames]
      · simp only [cmp116FixedWeakeningCoordinateNames, Fin.cons_succ,
          List.map_cons, List.mem_cons]
        exact Or.inr (ih j)

/-- The recursive coordinate enumeration agrees with the first projection of
the corresponding history entry. -/
theorem cmp116FixedWeakeningCoordinateNames_eq_get
    {D : Type*} (history : List (D × ℝ))
    (i : Fin history.length) :
    cmp116FixedWeakeningCoordinateNames history i = (history.get i).1 := by
  induction history with
  | nil => exact Fin.elim0 i
  | cons p history ih =>
      rcases p with ⟨d, t⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simpa [cmp116FixedWeakeningCoordinateNames] using ih j

/-- A history without repeated coordinate names provides an injective
coordinate family for the arbitrary-order jet. -/
theorem cmp116FixedWeakeningCoordinateNames_injective
    {D : Type*} (history : List (D × ℝ))
    (hnodup : (history.map Prod.fst).Nodup) :
    Function.Injective (cmp116FixedWeakeningCoordinateNames history) := by
  intro i j hij
  let castIndex :
      Fin history.length → Fin (history.map Prod.fst).length :=
    Fin.cast (by simp)
  have hget :
      (history.map Prod.fst).get (castIndex i) =
        (history.map Prod.fst).get (castIndex j) := by
    simpa [castIndex, cmp116FixedWeakeningCoordinateNames_eq_get] using hij
  have hcast := hnodup.injective_get hget
  apply Fin.ext
  simpa [castIndex] using congrArg Fin.val hcast

/-- Recursive integrated coefficient assigned to one physical domain.

`history` is stored in reverse chronological order: when the next FTC fiber
differentiates coordinate `d` at interpolation value `t`, the new list is
`(d,t) :: history`.  Retaining the value makes the current nested derivative
literal rather than reconstructed after the fact. -/
noncomputable def cmp102Eq80SourcePi4FTCConnectedDomainContribution
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
    (history : List (FinBox 4 (2 * Q) × ℝ)) →
    (sigma : FinBox 4 (2 * Q) → ℝ) →
    (remaining : List (FinBox 4 (2 * Q))) →
    (W : Finset (FinBox 4 (2 * Q))) → ℝ
  | [], _sigma, [] , _W => 0
  | history@(_ :: _), sigma, [], W =>
      cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase sigma vertexCoordinates
        (cmp116FixedWeakeningCoordinateNames history) W
  | history, sigma, d :: tail, W =>
      cmp102Eq80SourcePi4FTCConnectedDomainContribution
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase vertexCoordinates history
          (Function.update sigma d 0) tail W +
        ∫ t in (0 : ℝ)..1,
          cmp102Eq80SourcePi4FTCConnectedDomainContribution
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
            vertexBase vertexCoordinates ((d, t) :: history)
            (Function.update sigma d t) tail W

/-- The full domain-indexed FTC contribution vanishes if its proposed label
omits any part of the literal `Pi^4` anchor. -/
theorem
    cmp102Eq80SourcePi4FTCConnectedDomainContribution_eq_zero_of_not_subset
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
    (history : List (FinBox 4 (2 * Q) × ℝ))
    (sigma : FinBox 4 (2 * Q) → ℝ)
    (remaining : List (FinBox 4 (2 * Q)))
    (W : Finset (FinBox 4 (2 * Q)))
    (hanchor : ¬cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ W) :
    cmp102Eq80SourcePi4FTCConnectedDomainContribution
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
      vertexBase vertexCoordinates history sigma remaining W = 0 := by
  induction remaining generalizing history sigma with
  | nil =>
      cases history with
      | nil =>
          simp [cmp102Eq80SourcePi4FTCConnectedDomainContribution]
      | cons p tail =>
          simpa [cmp102Eq80SourcePi4FTCConnectedDomainContribution] using
            cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt_eq_zero_of_not_subset
              anchor K hc hmass hK D D₃ V₀ Δπ J A
              vertexBase sigma vertexCoordinates
              (cmp116FixedWeakeningCoordinateNames (p :: tail)) W hanchor
  | cons d tail ih =>
      simp only [cmp102Eq80SourcePi4FTCConnectedDomainContribution]
      rw [ih history (Function.update sigma d 0)]
      simp_rw [ih ((d, _) :: history) (Function.update sigma d _)]
      simp

/-- The full domain-indexed FTC contribution vanishes on every disconnected
label. -/
theorem
    cmp102Eq80SourcePi4FTCConnectedDomainContribution_eq_zero_of_not_walkConnected
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
    (history : List (FinBox 4 (2 * Q) × ℝ))
    (sigma : FinBox 4 (2 * Q) → ℝ)
    (remaining : List (FinBox 4 (2 * Q)))
    (W : Finset (FinBox 4 (2 * Q)))
    (hconnected :
      ¬walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) W) :
    cmp102Eq80SourcePi4FTCConnectedDomainContribution
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
      vertexBase vertexCoordinates history sigma remaining W = 0 := by
  induction remaining generalizing history sigma with
  | nil =>
      cases history with
      | nil =>
          simp [cmp102Eq80SourcePi4FTCConnectedDomainContribution]
      | cons p tail =>
          simpa [cmp102Eq80SourcePi4FTCConnectedDomainContribution] using
            cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt_eq_zero_of_not_walkConnected
              anchor K hc hmass hK D D₃ V₀ Δπ J A
              vertexBase sigma vertexCoordinates
              (cmp116FixedWeakeningCoordinateNames (p :: tail)) W
              hconnected
  | cons d tail ih =>
      simp only [cmp102Eq80SourcePi4FTCConnectedDomainContribution]
      rw [ih history (Function.update sigma d 0)]
      simp_rw [ih ((d, _) :: history) (Function.update sigma d _)]
      simp

end

end YangMills.RG
