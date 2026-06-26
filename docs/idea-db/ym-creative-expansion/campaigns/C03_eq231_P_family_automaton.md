# Campaign C03 — Eq. (2.31) P-family membership iff

## Goal
Remove the live P-carrier/source dictionary hypothesis.

## Target shape

```text
P ∈ PIndex Z D ↔
  P ⊆ gapCubes Z D × Fin 4 ∧ admissible Z D P = true
```

## Automaton idea
Define `admissible` as a Boolean conjunction:

```text
source_endpoint_ok ∧ positive_orientation_ok ∧ no_duplicate_bond ∧ source_gap_relation_ok
```

## Hard source work
This is not just a Lean unfolding. The actual theorem must be justified from CMP116/CMP109 source definitions and the positive-oriented bond convention.

## First Lean toy
A finite graph where `PIndex` is literally a filtered powerset and the membership iff compiles by `simp`.
