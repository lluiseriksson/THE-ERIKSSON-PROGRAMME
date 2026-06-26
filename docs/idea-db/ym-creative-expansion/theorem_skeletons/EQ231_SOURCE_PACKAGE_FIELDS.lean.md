# Eq. (2.31) theorem skeletons

```lean
-- Field 1: source subset.  Smallest first target.
theorem cmp116Eq231_source_subset_gapCarrier_from_source
    ...
    : ∀ Z D P, sourceAdmissible Z D P →
        P ⊆ gapCubes Z D ×ˢ (Finset.univ : Finset (Fin 4)) := by
  -- Must use extracted source bond/base-cube statement.
```

```lean
-- Field 2: membership iff.  Do not prove from `admissible` tautology.
theorem cmp116Eq231_mem_iff_source_from_balaban_definition
    ...
    : ∀ Z D P, P ∈ PIndex Z D ↔ sourceAdmissible Z D P := by
  -- Must use source definition of Balaban's P family.
```

```lean
-- Field 3: boolean/source bridge.  Do not set admissible := decide(P∈PIndex).
theorem cmp116Eq231_admissible_iff_source_from_transcription
    ...
    : ∀ Z D P, admissible Z D P = true ↔ sourceAdmissible Z D P := by
  -- Must use a non-tautological transcription of page-12/page-18 conditions.
```
