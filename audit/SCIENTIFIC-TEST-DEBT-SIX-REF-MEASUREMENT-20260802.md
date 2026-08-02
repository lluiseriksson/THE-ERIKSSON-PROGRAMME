# Six-ref scientific-test debt measurement — 2026-08-02

## Decision

Exact invariance was observed. All six isolated executions returned exit 1 with
the same ordered nine pytest nodeids, all in the call phase, and the same first
cause fingerprints. No collection error or timeout occurred. The differing
pass counts are explained by four run-manifest guard tests added after the five
historical PR heads: main has 695 passes; each PR head has 691.

Workflow: `.github/workflows/control-plane.yml`, `Validate repository control
plane`, job `test`. Exact measured command: `python -m pytest -q`.

| Ref | Exact SHA | Failed / passed | Pytest duration | Exit | Raw log SHA-256 |
|---|---|---:|---:|---:|---|
| main after #51 | `a73e2c5f658c801e3bb414f5b2bc47ea4ba46e18` | 9 / 695 | 524.38 s | 1 | `6d463c303230515dc2fda275322b893d395658ddfa6938d5fd94856f612e054f` |
| PR #35 head | `a66b1c7da3c7441e06864e327b5c4efa43e9c79d` | 9 / 691 | 513.05 s | 1 | `fb0351f5adff84dd3f45b85d3c7949fc3c9fb6d28339c365e97218ac5c0da08c` |
| PR #39 head | `14a4db49a3a5623de9222aac5882c7b4940ebefa` | 9 / 691 | 514.97 s | 1 | `b59448bfb1b2606a15c41aee42a1c68a929ce5c3f3878dcb56bf27a2f5a87bfa` |
| PR #40 head | `0766de86e696bd398abbfb39bc6f728191f3aded` | 9 / 691 | 509.41 s | 1 | `6f66871ce80cf133806c8e5c073802dbdc8e7dff09eebb18ca9bb2fc931f4d14` |
| PR #43 head | `21f98fe83f8ab897d9aefabf89cc2854e53d4aee` | 9 / 691 | 515.77 s | 1 | `70f5594f37fcf22373713a0625af2b26301bf456f9fb11e9676e1901fbae84ad` |
| PR #54 head | `a0a353de456a7ed0d05817fbcc2eca9399f923f2` | 9 / 691 | 518.15 s | 1 | `6358d15886921945631359f3d32f027d8d7b1cbcd3616fceccb2a1a909416712` |

The five PR SHAs above were resolved from GitHub and independently matched the
second parent of merge commits #35, #39, #40, #43 and #54. Every SHA is an
ancestor of `a73e2c5f658c801e3bb414f5b2bc47ea4ba46e18`.

## Nominal failures and first causes

The readable, machine-enforced list and its cause hashes are in
`.github/scientific-test-debt-baseline.json`. Ordered first causes are:

1. `tests/test_surface_bulk_3_6.py::test_canonical_surface_bulk_3_6_transcript` — `AssertionError: worktree script hash mismatch`
2. `tests/test_surface_final_seal.py::test_surface_final_seal` — `AssertionError: assert ['terminal pr...dit failed: '] == []`
3. `tests/test_surface_finite_role_relay.py::test_finite_role_relay_is_complete_and_logically_bound` — `AssertionError: assert 'NONE' == 'FINITE_ROLE_PROVED'`
4. `tests/test_surface_g2_relay_admissibility.py::test_terminal_promotion_is_bound_to_the_frozen_ownership_fingerprint` — `AssertionError: assert 'NONE' == 'FINITE_BULK_SIGN_CERTIFIED'`
5. `tests/test_surface_g2_terminal_cover.py::test_surface_g2_terminal_domain_cover` — `AssertionError`
6. `tests/test_surface_high_beta_lambda3_joint_validator.py::test_committed_lambda3_joint_pair` — `AssertionError: unexpected transcript digest`
7. `tests/test_surface_high_beta_lambda3_weak_relay_inputs.py::test_lambda3_transcript_implies_tighter_weak_relay_bounds` — `AssertionError: unexpected lambda-three digest: 64cb5cb855fc3ddf90ea4efd06567c677cb4f880aaa5ca2d53eb70683387eb36`
8. `tests/test_surface_terminal_prerequisites.py::test_terminal_prerequisites_are_rebuilt_from_evidence` — `AssertionError`
9. `tests/test_validate_surface_remainder_delta0_sixth_coefficient_transcript.py::test_authoritative_sixth_head_transcript_validates` — `AssertionError: assert 'ee5fb3edfda1...4675a87cf5556' == '27725eaac35f...6681d1eeeec9c'`

## Colab evidence

- Account: Lluís Eriksson (`lluiseriksson@gmail.com`).
- Notebook: `scientific-test-debt-six-ref-audit-20260802.ipynb`, prepared while disconnected at [Colab](https://colab.research.google.com/drive/1Fr2SqlbFSFF8V32zlB9ON6q4xR4FmDpm).
- Runtime: Colab Pro+ hosted Python 3, CPU, high RAM; 8 vCPU, 50 GiB RAM, Ubuntu 22.04.5 LTS, Linux 6.6.122+, Python 3.12.13, pytest 8.4.2, SymPy 1.14.0, mpmath 1.3.0, python-flint 0.9.0.
- Opened: `2026-08-02T17:35:06Z`; campaign ended `2026-08-02T18:27:56Z`; runtime disconnected and deleted at `2026-08-02T18:33:46Z` (about 58m40s connected).
- Downloaded ZIP: 42,315 bytes; SHA-256 `88a1ef4e1ddc2ac2cf176b22be6423028ad37cd87076cc67e0d88d213cd6a2d4`, verified after download.
- Every disposable Colab clone recorded `cleanup_exit=0`; there is no `CLEANUP-PENDING` path.
- No Lean, Lake, or mathematical oracle command was run.

## Guarantee boundary

The new control guarantees only that the current full pytest run has no failure,
collection error, timeout, or unexecuted nominal nodeid beyond the still-active
subset of the measured nine failures on the exact comparison base. A repaired
known failure is reported as an improvement; if a later commit reintroduces it,
the base comparison makes it a regression. Scientific tests remain visibly
FAILED in pytest output.

It does not prove the nine scientific claims, repair their data or hashes,
certify mathematical truth, or turn those tests into passes.
