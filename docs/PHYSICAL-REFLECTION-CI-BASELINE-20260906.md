# CI baseline observed during the reflection campaign

**6 September 2026.** The general control-plane suite is not green. This note
records the exact pre-existing failures instead of changing certificate
hashes or presenting an unrelated documentation check as a full PASS.

| Source | Evidence | Result |
|---|---|---|
| `main`, `ff9498df9bb13050a3c663103e4a0830e793c56f` | [5 September run 33957207604](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/33957207604) | 9 failed, 695 passed, 382.59 s |
| Documentation PR #77, `98431b5c6a10f6e721ad6cc14dddeb3b3e8a0cad` | [6 September run 34021217080](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/34021217080) | Same 9 failed, 695 passed, 371.34 s |
| R1 source PR #78, `ea58f6127696a962953c636bb363a43a79b3a6c1` | [6 September run 34022170958](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/34022170958) | Same 9 failed, 695 passed, 283.39 s |
| R2 source PR #79, `507e8a38ce7f7addf9c1b8f65d296dc00b77971b` | [6 September run 34035314140](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/34035314140) | Same 9 failed, 695 passed, 380.92 s |
| R2 final documentation, `fb4acd5654d9e4ef9f46573bb42522884c8dd81b` | [6 September run 34035574242](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/34035574242) | Same 9 failed, 695 passed, 365.86 s |

All five logs name the same failing tests:

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
appear in the compared runs. Neither PR #77 nor PR #78 changes scripts,
tests, workflows, certificates or `project-state.json`; their diffs for
those paths are empty.
This comparison establishes prior failure, not a repair or a re-certification
of the Surface theorem. The byte-representation contract requires a separate
audit before any stored digest or acceptance logic is changed.

Dashboard validation, public-documentation validation, epistemic-honesty
checks and the run-manifest structure/debt-delta check passed for PR #77.
That documentation-only PR was merged as
`541d41b039a7b13b68d0795dcf686462d279b88f`, with the failing baseline disclosed
in its description. The Pages deployment for that commit completed. The Lean
reflection module was not part of that merge.

For PR #78 at `ea58f6127696a962953c636bb363a43a79b3a6c1`, dashboard and
public-documentation validation passed in run `34022170862`; epistemic
honesty passed in `34022170848`; the manifest structure/debt-delta job passed
within `34022170958`. These scoped checks and the independent Colab Lean
results do not turn the failing general suite into a PASS.

For R2 PR #79, source-honesty, dashboard, public-documentation and
run-manifest structure/debt checks passed at both source and final
documentation revisions. The source-stage honesty/dashboard runs are
`34035314143`/`34035314156`; the final revision's corresponding runs are
`34035574272`/`34035574305`. The two control-plane logs above reproduce the
same nine test names and offending Surface digests; no new failure was
observed. R2 changes neither the affected Surface artifacts, tests and
validators nor their recorded acceptance hashes or `project-state.json`.
Its new saved-log validator lives under the R2 evidence directory and is
separately tested in Colab; it does not change Surface acceptance logic.

PR #79 merged without squash/rebase at `2026-09-06T13:23:55Z` as
`f2f7a8914f5945a3b14bbec77b74b9d246fc8e3f`, with the baseline failures
explicitly disclosed in the PR description. This follow-up records the
observed CI result; it makes no new Lean, terminal or Surface verification claim.

Physical reflection and the 4D continuum remain open. The historical Clay
label **~0% (<0.1%)** remains a convention, not a measured percentage.
