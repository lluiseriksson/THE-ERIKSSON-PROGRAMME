# CI baseline observed during the reflection campaign

**6 September 2026.** The general control-plane suite is not green. This note
records the exact pre-existing failures instead of changing certificate
hashes or presenting an unrelated documentation check as a full PASS.

| Source | Evidence | Result |
|---|---|---|
| `main`, `ff9498df9bb13050a3c663103e4a0830e793c56f` | [5 September run 33957207604](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/33957207604) | 9 failed, 695 passed, 382.59 s |
| Documentation PR #77, `98431b5c6a10f6e721ad6cc14dddeb3b3e8a0cad` | [6 September run 34021217080](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/34021217080) | Same 9 failed, 695 passed, 371.34 s |

Both logs name the same failing tests:

- `test_surface_bulk_3_6.py::test_canonical_surface_bulk_3_6_transcript`
- `test_surface_final_seal.py::test_surface_final_seal`
- `test_surface_finite_role_relay.py::test_finite_role_relay_is_complete_and_logically_bound`
- `test_surface_g2_relay_admissibility.py::test_terminal_promotion_is_bound_to_the_frozen_ownership_fingerprint`
- `test_surface_g2_terminal_cover.py::test_surface_g2_terminal_domain_cover`
- `test_surface_high_beta_lambda3_joint_validator.py::test_committed_lambda3_joint_pair`
- `test_surface_high_beta_lambda3_weak_relay_inputs.py::test_lambda3_transcript_implies_tighter_weak_relay_bounds`
- `test_surface_terminal_prerequisites.py::test_terminal_prerequisites_are_rebuilt_from_evidence`
- `test_validate_surface_remainder_delta0_sixth_coefficient_transcript.py::test_authoritative_sixth_head_transcript_validates`

The failures include script/transcript byte-digest mismatches and their
downstream certificate consumers. The same lambda-three digest
`64cb5cb855fc3ddf90ea4efd06567c677cb4f880aaa5ca2d53eb70683387eb36`
and sixth-head digest
`ee5fb3edfda129a5c0177577032ac8f307418ae64ffe1088b5b4675a87cf5556`
appear in the two runs. PR #77 changes no scripts, tests, workflows,
certificates or `project-state.json`; its diff for those paths is empty.
This comparison establishes prior failure, not a repair or a re-certification
of the Surface theorem. The byte-representation contract requires a separate
audit before any stored digest or acceptance logic is changed.

Dashboard validation, public-documentation validation, epistemic-honesty
checks and the run-manifest structure/debt-delta check passed for PR #77.
That documentation-only PR was merged as
`541d41b039a7b13b68d0795dcf686462d279b88f`, with the failing baseline disclosed
in its description. The Pages deployment for that commit completed. The Lean
reflection module was not part of that merge.

Physical reflection and the 4D continuum remain open. The historical Clay
label **~0% (<0.1%)** remains a convention, not a measured percentage.
