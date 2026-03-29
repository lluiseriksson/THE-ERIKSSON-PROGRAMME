# AI_ONBOARDING

This file is the mandatory entry point for any new AI session working on this repository.

*(Note: Everything must be configured precisely so the agent always knows what is verified, what is not, how many steps remain in each layer, and what to focus on at any given moment. See the Dashboard.)*

## 1. What this project is

This repository is a long-term Lean 4 formalization program centered on the 4D Yang–Mills mass gap problem.

It is not assumed that the theorem is already solved here.
The repository is designed to make the state of the research explicit and machine-readable.

## 2. What you must not assume

Do not assume any of the following unless explicitly registered in `registry/`:
- that a theorem is already formalized,
- that a black-box interface corresponds to a real construction,
- that a passing audit/test implies a Lean proof,
- that a README claim is stronger than the node registry,
- that a placeholder object is mathematically nontrivial.

## 3. Source of truth

The source of truth is:

1. `registry/nodes.yaml`
2. `registry/dependencies.yaml`
3. `registry/critical_paths.yaml`
4. `registry/labels.yaml`

Human-readable summaries are secondary.

## 4. Evidence taxonomy

Every node must distinguish:
- status
- evidence type
- dependency list
- blocking relation
- definition of done
- next minimal action

Only `FORMALIZED_KERNEL` closes a critical node.

## 5. How to begin a session

Read in this order:
1. `STATE_OF_THE_PROJECT.md`
2. `dashboard/current_focus.json`
3. `registry/critical_paths.yaml`
4. `registry/nodes.yaml`
5. relevant layer docs under `docs/`

Then determine:
- whether your target node is open,
- whether it is blocked,
- whether it depends on missing infrastructure,
- whether there is already a defined next step.

## 6. How to propose work

Before editing Lean code:
- identify the target node ID,
- verify dependencies are satisfied or explicitly imported,
- check whether the node is on the critical path,
- check whether the target statement is exact enough,
- ensure the work is registered in `registry/nodes.yaml`.

## 7. What to record after work

Every meaningful contribution must update at least one of:
- `registry/nodes.yaml`
- `registry/dependencies.yaml`
- `DECISIONS.md`
- `STATE_OF_THE_PROJECT.md`
- `dashboard/current_focus.json`

No important progress may remain only in chat memory.

## 8. Anti-vacuity policy

You must explicitly flag:
- empty-domain constructions,
- trivial witnesses (`0`, `1`, empty set) used to satisfy interfaces,
- parameter-passing disguised as proof,
- packaging-only bridges,
- theorem statements weaker than the required mathematical target.

## 9. Two-track policy

The project contains two intertwined tracks:

### Track A: YM target
The direct route toward the 4D Yang–Mills mass gap target.

### Track B: reusable QFT infrastructure
General Lean infrastructure for constructive QFT, analysis, OS axioms, and reconstruction.

Do not confuse progress in Track B with closure of Track A.

## 10. If you are unsure

Do not invent missing state.
Mark the node as blocked, partial, or needing clarification in the registry.
