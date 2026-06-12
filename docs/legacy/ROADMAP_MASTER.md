# ROADMAP_MASTER

## Program horizon

This is a 10–15 year formal research program.

The terminal goal is a fully auditable, dependency-explicit Lean formalization path toward the 4D Yang–Mills mass gap problem, with no confusion between proof, imports, black boxes, and experimental proxies.

## Phase 0 — Sanitation and architecture
Status: active

Goals:
- define layers and node numbering
- build registry and dependency DAG
- freeze evidence taxonomy
- implement consistency checks
- define critical paths
- forbid undocumented axioms and untracked placeholders

Exit criteria:
- every critical node exists in the registry
- every node has status, evidence, dependencies, and definition of done
- dashboards build automatically
- CI validates registry consistency

## Phase 1 — Reusable infrastructure
Goals:
- finite lattice infrastructure
- discrete analysis on `ℤ^4`
- polymer combinatorics
- abstract Kotecký–Preiss
- cluster expansion for truncated correlations
- abstract OS framework
- abstract Wightman reconstruction interfaces

Exit criteria:
- reusable infrastructure track has multiple kernel-certified nontrivial results
- target track no longer depends on placeholder scaffolding for basic discrete structures

## Phase 2 — Balaban/Eriksson core closure
Goals:
- multiscale covariance interfaces
- local seminorms and jets
- small-field estimates
- large-field suppression
- inductive RG step
- terminal extraction of polymer activities
- non-vacuous bridge into KP

Exit criteria:
- a nontrivial route exists from lattice YM objects to terminal polymer bounds without undocumented axioms on the critical path

## Phase 3 — OS/Wightman
Goals:
- build limit Schwinger functions
- verify OS axioms
- formalize OS → Wightman reconstruction
- instantiate reconstruction for the target theory

Exit criteria:
- actual reconstructed objects replace placeholder packages
- critical OS/Wightman nodes are kernel-certified or isolated as explicit imports

## Phase 4 — Inconditional closure
Goals:
- remove remaining imports on critical paths
- close nontriviality and mass gap nodes
- produce final critical-path audit

Exit criteria:
- the final target path is closed using only kernel-certified theorems and accepted standard library imports

## Always-on goals
- preserve machine-readable state
- maintain anti-vacuity discipline
- separate target progress from infrastructure progress
- keep honesty statements synchronized with actual evidence
