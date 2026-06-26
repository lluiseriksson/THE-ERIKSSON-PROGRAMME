# Sprint 10 — Batch 003 queue alignment

## Goal

Ensure every constructor attempt maps to exactly one Batch 003 proof-obligation
card.

## Workflow

1. Pick one `proof.*` key from `data/batch003_hypothesis_removal_queue.v3.json`.
2. Read its matching `proof_obligation_cards/PO_*.md`.
3. Produce either a theorem patch or an extraction blocker.
4. Run the no-new-consumers detector.

## Fail condition

The sprint fails if the patch adds a theorem whose premise is the same live
source hypothesis under a new name.
