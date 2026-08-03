import YangMills.SU2ThetaPrism.Combinatorics

/-!
# Concrete SU(2) twice-spin coupling profile

Labels are twice the physical spin.  The multiplicity function is the general
triangle/parity rule for an SU(2) trivalent invariant; it is not a predicate
defined to equal the target sector.
-/

namespace YangMills.SU2ThetaPrism

/-- Twice-spin label: `0,1,2,...` represents `0,1/2,1,...`. -/
abbrev TwiceSpin := ℕ

/-- Dimension `2j+1`, expressed in the twice-spin label. -/
def representationDimension (j : TwiceSpin) : ℕ :=
  j + 1

/-- Triangle and parity conditions for a trivalent SU(2) invariant. -/
def CouplingAdmissible (a b c : TwiceSpin) : Prop :=
  a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ Even (a + b + c)

instance couplingAdmissibleDecidable (a b c : TwiceSpin) :
    Decidable (CouplingAdmissible a b c) := by
  unfold CouplingAdmissible
  infer_instance

/-- General multiplicity-free SU(2) trivalent coupling rule. -/
def couplingMultiplicity (a b c : TwiceSpin) : ℕ :=
  if CouplingAdmissible a b c then 1 else 0

/-- Concrete channel type; its cardinality is the coupling multiplicity. -/
abbrev CouplingChannel (a b c : TwiceSpin) := Fin (couplingMultiplicity a b c)

theorem theta_coupling_admissible : CouplingAdmissible 2 1 1 := by
  norm_num [CouplingAdmissible, Even]

/-- The `(1,1/2,1/2)` invariant channel has multiplicity one. -/
theorem theta_coupling_multiplicity_one :
    couplingMultiplicity 2 1 1 = 1 := by
  simp [couplingMultiplicity, theta_coupling_admissible]

theorem theta_channel_card : Fintype.card (CouplingChannel 2 1 1) = 1 := by
  simp [theta_coupling_multiplicity_one]

theorem theta_channel_nonempty : Nonempty (CouplingChannel 2 1 1) := by
  rw [show CouplingChannel 2 1 1 = Fin 1 by
    simp [CouplingChannel, theta_coupling_multiplicity_one]]
  infer_instance

theorem spinHalf_dimension : representationDimension 1 = 2 := by
  rfl

theorem spinOne_dimension : representationDimension 2 = 3 := by
  rfl

/-- The singlet projection coefficient is derived as the inverse fundamental
dimension; it is not stored as a result-bearing field. -/
def singletProjectionCoefficient : ℚ :=
  1 / representationDimension 1

theorem singletProjectionCoefficient_eq_half :
    singletProjectionCoefficient = 1 / 2 := by
  norm_num [singletProjectionCoefficient, representationDimension]

/-- Deleting a branch destroys the three-distinct-leg realization even though
the abstract label coupling remains a valid representation-theoretic rule. -/
theorem reduced_cell_has_no_theta_three_leg :
    ¬ HasThreeDistinctBranches ReducedBranch :=
  reducedBranch_not_hasThreeDistinct

end YangMills.SU2ThetaPrism
