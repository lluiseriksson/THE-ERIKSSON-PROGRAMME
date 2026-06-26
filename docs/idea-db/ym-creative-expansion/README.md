# YM Creative Expansion Pack v6

**Batch-006 live-field control / raw-source M3 orchestration edition.**

This pack is for agents working on `lluiseriksson/THE-ERIKSSON-PROGRAMME` after
Batch 006.  v5 introduced the closed-loop patch harness; v6 adds a second control
plane for the Gaussian/root/Hessian/activity/H# stack so agents can discharge
one raw-source field at a time instead of hiding multiple analytic obligations in
a monolithic source package.

## Main use

```bash
python scripts/mission_board.py --ranked
python scripts/field_board.py --order
python scripts/compile_mission_prompt.py OC_016_covariance_root_certificate_dictionary
python scripts/generate_patch_intake.py OC_016_covariance_root_certificate_dictionary > patch_intake/my_patch.json
python scripts/score_patch_intake.py patch_intake/my_patch.json
python scripts/check_no_backfill.py patch_intake/my_patch.json
python scripts/check_patch_contract.py \
  --contract mission_contracts/OC_016_covariance_root_certificate_dictionary.json \
  --intake patch_intake/my_patch.json
```

## v6 additions

- Batch-006 raw-source field DAG and burndown matrix.
- 15 mission contracts for Gaussian/root/Hessian/activity/H# fields.
- Field-specific source extraction worksheets and Lean theorem skeletons.
- Anti-backfill audit: downstream H# / final Lemma 3 bounds cannot discharge
  upstream Gaussian/root/Hessian/source-dictionary fields.
- Source-acquisition planner for private artifacts and exact locator locks.
- New v6 scoring layer for field reduction, source promotion and forbidden
  downstream backfill.

## Correct field order

```text
covariance_root_certificate
  -> root_localization
  -> gaussian_pushforward
  -> wilson_hessian_identification
  -> local_physical_activity_construction
  -> support + measurability
  -> raw_pointwise_decay / termwise estimate
  -> Appendix-F H# consumer
  -> rooted_hsharp_remainder_identity
  -> Rsc / flow / IR frontier
```

Eq. (2.31) remains the highest near-term proof-card route, but v6 widens the
harness to the new Batch-006 frontier: a patch must now declare whether it works
on the Eq. (2.31) branch or on exactly one raw-source M3 live field.

## Hard boundary

This pack is not a mathematical source, not a Lean theorem, not evidence for
`hRpoly`, and not a route into `YangMillsCore`.  It is a control harness for
source extraction, field-level proof planning and patch rejection.
