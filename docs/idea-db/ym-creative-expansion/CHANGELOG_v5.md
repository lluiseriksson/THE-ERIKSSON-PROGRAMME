# Changelog v5 — execution harness / closed-loop patch edition

Version `5.0.0` turns the v4 mission-control pack into a closed-loop execution
harness.  The earlier packs generated ideas, contracts and prompt material; v5
adds patch-intake generation, scoreable acceptance tests, source-lock sheets,
router synchronization, and theorem-skeleton prompts so agents can move from a
mission contract to a reviewable patch without inventing new process.

## Added

- Six new mission contracts `OC_010`–`OC_015` for source-promotion gates,
  router synchronization, build/oracle evidence, source locator locks, theorem
  statement skeletons and OCR/sign/constant guardrails.
- Fifteen new formula/proof-routing cards `D61`–`D75`.
- A local execution harness under `execution_harness/`.
- Patch-review examples under `patch_review/examples/`.
- Source-lock worksheets under `source_locks/`.
- New scripts:
  - `mission_board.py`
  - `generate_patch_intake.py`
  - `score_patch_intake.py`
  - `render_hypothesis_burndown.py`
  - `validate_v5_harness.py`
- A theorem-skeleton queue for Eq. (2.31), Eq. (2.29), Eq. (2.37), activity
  termwise, Gaussian/root/Hessian, and R-operation bridge work.

## Changed

- The main playbook now requires a patch-intake JSON for every proposed commit.
- Patch scoring now separates source promotions, removed fields, toy theorems,
  new consumers, opaque propositions and build/oracle evidence.
- The priority list is expressed as a workboard with concrete acceptance tests.

## Non-goals

v5 is still not source evidence and not a proof of `hRpoly` or Clay.  It is a
local operating system for producing smaller, reviewable, non-cosmetic patches.
