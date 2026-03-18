# Next Session: KP Induction (Layer 3B completion)

## Target theorem
```lean
theorem kpOnGamma_implies_compatibleFamilyMajorant
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ)
    (hKP : KPOnGamma Gamma K a) :
    CompatibleFamilyMajorant Gamma K (Real.exp (theoreticalBudget Gamma K a) - 1)
```

## Step 1: inductionBudget_insert_avoiding_le
```lean
theorem inductionBudget_insert_avoiding_le {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (X : Polymer d L) (K : Activity d L) (a : ℝ) :
    ∑ S ∈ ((compatibleSubfamilies (insert X Gamma)).erase ∅).filter (fun S => X ∉ S),
      absFamilyWeight K S
    ≤ InductionBudget Gamma K a
```
Tools: compatibleSubfamilies_insert_avoiding, Finset.sum_le_sum_of_subset, absFamilyWeight_nonneg

## Step 2: representation lemma (key combinatorial step)
```lean
theorem mem_compatibleSubfamilies_insert_contains_iff {d : ℕ} {L : ℤ}
    {Gamma : Finset (Polymer d L)} {X : Polymer d L} {S : Finset (Polymer d L)}
    (hX : X ∉ Gamma) :
    (S ∈ compatibleSubfamilies (insert X Gamma) ∧ X ∈ S) ↔
    ∃ T ∈ compatibleSubfamiliesAvoidingX Gamma X, S = insert X T
```

## Step 3: inductionBudget_insert_containing_le
```lean
theorem inductionBudget_insert_containing_le {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (X : Polymer d L) (K : Activity d L)
    (a : ℝ) (hX : X ∉ Gamma) :
    ∑ S ∈ ((compatibleSubfamilies (insert X Gamma)).erase ∅).filter (fun S => X ∈ S),
      absFamilyWeight K S
    ≤ |K X| * ∑ S ∈ compatibleSubfamiliesAvoidingX Gamma X, absFamilyWeight K S
```
Tools: Step 2 + absFamilyWeight_insert + Finset.sum over image

## Step 4: inductionBudget_insert_le (the recurrence)
```lean
IB(insert X Gamma) ≤ IB(Gamma) + |K X| * (1 + IB(Gamma))
```
= (1 + IB(Gamma)) * (1 + |K X|) - 1

## Step 5: close the induction
```lean
by Finset.induction_on Gamma:
  base:  IB(∅) = 0 = exp(0) - 1
  step:  theoreticalBudget_insert + inductionBudget_insert_le
         + one_add_le_exp to convert (1+|KX|) ≤ exp(|KX|*exp(a*|X|))
         + exp(A) * exp(B) = exp(A+B) to close
```

## Rule: do NOT fix B formula early
Let the induction tell you what B is. The exp(theoreticalBudget)-1 form
emerges naturally from the step 4 recurrence + one_add_le_exp.
