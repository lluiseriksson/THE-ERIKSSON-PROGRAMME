# Support/Measurability Proof Prompts

## Prompt A - Support Dictionary

Open `proof.activity.support-measurability.v2`, `cmp116.localized-activity.2.7-2.10`, and the repository support conventions in `PhysicalGaugeCMP116Dictionary`.

Return:

- source localized domains for spectator variables;
- source localized domains for fluctuation variables;
- exact enlargement convention, including any Omega or skeleton relation;
- proposed Lean-side `physicalActiveSupport` statement;
- blockers remaining before `spectator_support_subset` and `fluctuation_support_subset`.

Do not use exponential decay as a support-containment proof.

## Prompt B - Measurability

Extract only the measurability statement for the adapted physical local activity.

Return:

- field variables and measurable space/domain assumptions;
- source statement proving measurability or continuity;
- Lean target shape for `activity_stronglyMeasurable`;
- dependencies on the finite H(Z) dictionary, if any;
- blockers that remain separate from support containment.

Do not infer measurability from the finite-sum display without checking the measurable summand and finite index data.

## Prompt C - Repository Support Convention

Compare the source active sets with repository `physicalActiveSupport`, `physicalBondsOfCells`, and skeleton conventions.

Return:

- exact source active-set definition;
- repository support object that should consume it;
- whether `active_support_subset_omega` or `active_support_subset_skeleton` is the correct intermediate target;
- source dictionary fields that remain open.

Do not promote repository convention routing to a primary-source theorem.
