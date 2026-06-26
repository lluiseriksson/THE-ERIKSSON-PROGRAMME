# Changelog v4 — Mission contracts and patch gates

v4 converts the post-integration pack into an execution layer for Batch 003.

## Added

- Mission contracts `mission_contracts/OC_*.json`.
- Contract-specific prompts under `mission_prompts/`.
- Agent Mission Control and One-Commit-One-Hypothesis policy under `ops/`.
- Patch acceptance rubric and scoring script.
- Source promotion state machine.
- Formula/proof-routing cards D46-D60.
- New proof sprints 14-18.
- Lean templates for carrier injection, obligation state machines, common `O(1)` majorants and R-operation local-to-scalar records.

## Strategic change

v3 said: “do not add more consumers.”

v4 says: “compile each proof card into a contract, then reject patches that do not remove a field, promote a source, or sharpen a blocker.”
