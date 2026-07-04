# CMP122 R-Operation Proof Prompts

## Prompt A - Theorem 1 Handoff

Open `cmp122ii.theorem1.coupling-interval-induction`, `cmp119.theorem1.rt-inductive-assumptions`, and `crosswalk.r-operation-polymer-local-route`.

Return:

- exact small-coupling hypotheses and constant restrictions;
- CMP119 Sect. 2 assumptions that are restored after the R-operation;
- source symbols for density/action form, `T_k`, `A_k`, `E_k`, `R_k`, `B_k`, and `mathcalE_k`;
- proposed Lean-side theorem statement feeding `CMP119CMP122ERBSourceDecomposition`;
- blockers that remain before any `RawYMActivityDecay` consumer can use the field.

Do not treat the theorem handoff as a completed Lean source dictionary.

## Prompt B - R-Prime Bounds

Open `cmp122ii.rprime-bound.1.98-1.100` and inspect the visual formula fields separately.

Return:

- exponentiated `R'^(k)` expansion field;
- (1.99) pre-split bound with `c_1` and `d_{k, union Y_i}(X)`;
- (1.100) second-group bound with `exp(-p_0(g_k))` and `d_k(X)`;
- exact meaning of first-group/second-group domains;
- Lean metric/domain dictionary required before this can feed `rloc_decay`.

Do not collapse (1.99) and (1.100) into a single scalar geometric-decay claim.

## Prompt C - Post-R Action Split

Open `cmp122ii.post-r-action-split.1.101`.

Return:

- exact source statement of the post-R action split;
- first-group boundary versus second-group R dictionary;
- how `A_k`, `A'_k`, `R'^(k)`, and `B'^(k)` would map to repository local-activity components;
- whether the displayed split is enough for `PhysicalGaugeLocalActivity.globalEval`;
- remaining source-to-Lean blockers.

Do not claim the post-R split proves a Lean local-activity equality by itself.

## Prompt D - Large-Field C Bound

Open `cmp122i.large-field-c-bound.1.70`.

Return:

- exact hypotheses and variables for the `C_k^(n)` large-field bound;
- source role of the bound in the later post-R certificate;
- whether it feeds B/local amplitude, component decay, or only context;
- Lean-side target and blockers.

Do not use CMP122-I (1.70) as a pre-R surrogate for the full post-R certificate.

## Prompt E - CMP119 E/R/B Handoff

Open `cmp119.density-expansion-form.2.18`, `cmp119.t-operation-action-factorization.2.19-2.23`, `cmp119.e-term-local-regularity.2.24-2.29`, `cmp119.r-term-bound.2.31`, and `cmp119.b-term-local-regularity-bound.2.34-2.42`.

Return:

- density/action form dictionary;
- T-operation factorization dictionary;
- E/R/B action-component dictionary;
- R-term and B-term localization bounds separately;
- reserve/enlarged-space conditions needed before CMP122-II can hand off to Lean consumers.

Do not use CMP119/CMP122 routing to claim `source_construction`, `raw_pointwise_decay`, `hRpoly`, mass gap, or Clay progress.
