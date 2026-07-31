# Adjudication of stale CONT-C1 feedback — PR 34

Feedback source head: `b06fb6b8f44f7002fffaa2b371f39c790f42b447`

Audited current head: `0a46e266fc4808332ed20d2ab4611bfc271b208b`

This note adjudicates the supplied statement-level feedback against the
current public PR. It does not replace the clean-checkout report or credit the
feedback as evidence.

## Disposition

| Item | Current disposition |
|---|---|
| A — local KP predicate not connected to the checked theorem | **SUPERSEDED / CLOSED** |
| B — uniform cap for all nonnegative `t, epsilon` | **VALID STRENGTHENING; NOT PROVED** |
| C — “Structural no-go” and threshold wrapper are arithmetically thin | **CONFIRMED, scoped** |
| D — `beta2D` combined with arbitrary `d` | **CONFIRMED scope mismatch** |
| E — terminal theorem contains no `a` or cutoff object | **CONFIRMED** |
| F — retain audit base `81721890` | **STALE / REJECTED** |
| G — no public SU2 producer | **STALE / REJECTED** |

## A — the old drift blocker is closed

At `b06fb6b8`, `KPRadiusAtUnit` was only a lane-local retyping. At the current
head:

- `kpRadiusAtUnit_iff_checkedWindow` is only an `rfl` restatement of the
  unit-slice formula;
- `kpRadiusAtUnit_nonempty_from_checkedWindow` consumes the checked witness;
- `checkedCorrelatorAfterKPRadiusAtUnit` partially applies the actual
  `sun_two_plaquette_correlator_bound` through its `hr` argument;
- the canary compares the two bodies and its self-test mutates the exponent.

The generic theorem has a real bound parameter `B`, but the checked
`sun_two_plaquette_correlator_bound` is already the SU(`N_c`) specialization:
its `hr` contains `N_c` after the repository proves the
`fundamentalObservable` bound. Therefore no untyped `B -> N_c` substitution
remains in C1.

Verdict: the old FAIL is superseded by a typed **PASS** at `0a46e266`.

Minor prose defect: the docstring on
`kpRadiusAtUnit_iff_checkedWindow` says that it identifies a conjunct in
`sun_clustering_window_nonempty`, but the declaration itself mentions no
producer theorem and proves a character-for-character restatement by `rfl`.
The actual compile-time drift bridge is
`checkedCorrelatorAfterKPRadiusAtUnit` (and the positive-witness consumer is
`kpRadiusAtUnit_nonempty_from_checkedWindow`). This is a witnessed attribution
error, not a failure of the typed bridge or cap theorem.

## B — a stronger uniform-family theorem remains available

The current result fixes `t=epsilon=1`, hence uses `exp(3)`. For the actual
checked family, `t>=0` and `epsilon>=0` imply

```text
exp(t + epsilon + 1) >= exp(1).
```

Because the activity factor is nonnegative in the consumed domain, every
radius hypothesis in that family would imply the weaker uniform cap

```text
beta < log(1 + 1 / ((16d+1)^2 exp(1))) / N_c.
```

This would show that no choice of nonnegative `(t,epsilon)` rescues the radius
along a divergent nonnegative coupling. The current producer proves only the
unit slice and does not contain this monotonicity theorem.

For `d=4`, `N_c=3`, direct diagnostic evaluation gives
`3.927950692443041e-6` for the current `exp(3)` cap and
`2.902275551015614e-5` for the uniform `exp(1)` cap, a factor
`7.388777961493`. These floating-point values are orientation aids; the
missing Lean monotonicity theorem is still required for formal credit.

Verdict: current unit-slice E1 remains **PASS, scoped**. Any headline covering
the whole `(t,epsilon)` family is **BLOCKED** pending the typed generalization.

## C — non-circular, but nearly all content is in the cap lemma

`eventually_not_kpRadiusAtUnit_of_tendsto` uses:

1. the finite cap from `beta_lt_kpBetaCap`;
2. the definition of convergence to `atTop`;
3. `not_lt_of_ge`.

It is a valid routing corollary and does not assume continuum existence,
tightness, OS reconstruction, or a gap. It is therefore not circular under
the programme's continuum-circularity gate. The adjective “Structural” adds
no mathematical content.

Likewise, positivity of `g2*a^2` makes

```text
g2*a^2*kpBetaCap <= 1
```

algebraically equivalent to

```text
kpBetaCap <= beta2D.
```

Thus `not_kpRadiusAtUnit_beta2D` is an explicit threshold corollary of the cap,
not a construction of a cutoff trajectory or a new uniform estimate.

Verdict: logical validity **PASS**; substantive continuum content **NONE**.
Recommended prose repair: replace “Structural no-go” by “eventual cap
corollary” and describe `hsmall` as the threshold itself.

## D — the explicit trajectory is two-dimensional only

`ScaleDict.beta2D` is explicitly documented as the two-dimensional convention
`1/(g2*a^2)`, while `not_kpRadiusAtUnit_beta2D` quantifies over arbitrary
`d`. The Lean implication is arithmetically valid for every value of `d`, but
its physical interpretation is only the declared 2D one. The producer's
abstract `Tendsto beta l atTop` theorem is the only dimension-agnostic routing
statement.

Verdict: **FAIL of unqualified physical scope**, already subordinate to the
stronger sign/normalisation failure in the main audit. Minimum repair: fix
`d=2` in the explicit theorem or state in its theorem documentation that no
`d!=2` physical tuning law is represented.

## E — the terminal theorem is cutoff-free

The terminal eventual theorem contains no `ScaleDict`, lattice spacing,
physical volume, cutoff, regulator family, observable renormalisation, or
continuum measure. Its only scale input is an arbitrary filter and a real
function tending to `atTop`.

Verdict: **PASS only as an abstract filter corollary**; **BLOCKED** as any
claim about construction or control of an `a -> 0` continuum limit.

The standalone numerical witness `kpRadiusAtUnit_witness_4_3` uses `beta=0`.
It proves only that the locally written inequality is satisfiable. It is not
evidence of a nontrivial or positive-coupling window. The relevant
positive-coupling non-vacuity declaration is
`kpRadiusAtUnit_nonempty_from_checkedWindow`, which returns `0 < beta`.

## F — base correction in the feedback is false at the current snapshot

The public PR metadata gives base
`7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a`, not `81721890`. The source desk
audited the PR against its actual public base. Public `main` later advanced to
`1e6113a1`; that Paper 13 v1.1 change was audited separately and does not
rewrite PR 34's immutable base.

## G — public inventory has advanced

At final recheck:

```text
PR 34 / codex/continuum-c1:
  0a46e266fc4808332ed20d2ab4611bfc271b208b

PR 35 / codex/su2-wilson-reflection-positivity:
  5a1f2a08e18cdd86958a315a3254073b2f6370af

PR 36 / codex/continuum-c0:
  7fe64bbced729337f6a1060d731e661384863c42
```

SU2 and CONT-C0 therefore both have public artefacts and separate
clean-checkout audits. These later refs do not alter the immutable C1 result.
