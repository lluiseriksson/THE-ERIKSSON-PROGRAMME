# (9) Fabricante del prisma theta: contract and charter

Status: **PRE-REGISTERED BEFORE THE FINAL BUILD RESULTS**

Canonical task number and name: **(9) Fabricante del prisma theta**.  The
artefact, delivery summary, branch description, and draft pull request must use
that exact numbering; no suffixed or alternate task number is permitted.

This charter fixes the scope of a post-pre-audit manufacturing pass.  It is
not an external audit verdict.  The artefact built under this charter must not
claim a physical plaquette, Osterwalder--Schrader positivity, or Gate 7.

## Immutable provenance policy

- Construction base: raw commit `43c003b2c0c98aceeabbf10ba28a4783de5859f1`.
- Frozen reference, if a convention or existing theorem is needed: raw commit
  `a66b1c7da3c7441e06864e327b5c4efa43e9c79d`.
- The two incoming read-only pre-audits were supplied without raw commit SHAs.
  Their mathematical outputs are therefore treated as pre-registered inputs,
  not as repository provenance and not as terminal certification.
- Tags must not be named, queried, resolved, or used in any command or record.

## Frozen negative-diff lane

There must be no change to:

- pull request 35;
- `YangMills/OS/SU2WilsonReflection*`;
- `docs/su2-os/**`;
- the certified raw commit named above.

No continuous `ReflectionSplitting` import is permitted in the new artefact.
No definition may identify the abstract cell with `GaugeConfig`.

## Fixed abstract cell and normalization

The group is `SU(2)` with normalized product Haar.  There are vertices
`a-`, `b-`, `a+`, `b+`; three upper branches `A0,A1,A2`, three lower branches
`B0,B1,B2`, and transversals `s,t`.  The branch holonomies, reflection,
relative variables, witness and weight are fixed as follows:

```text
H_i = s A_i t^-1 B_i^-1
theta: A_i <-> B_i, s -> s^-1, t -> t^-1
U = A0^-1 A1, V = A0^-1 A2
F(U,V) = chi(U) chi(V) - (1/2) chi(U V^-1)
weight = product_i exp((beta/2) chi(H_i))
```

Here `chi` is the trace in the fundamental representation.  The fabrication
domain is exactly `0 < beta <= 1`.

## Pre-registered numerical targets

The following values may not be changed in response to build or calculation
results:

1. `integral chi(W A1) chi(W A2) dW = (1/2) chi(A2^-1 A1)`;
2. simultaneous conjugation invariance, nonzero witness, and the three full
   orthogonalities to functions of `U`, `V`, and `U V^-1`;
3. witness norm squared `3/4`;
4. pure sector `(1, 1/2, 1/2)`, multiplicity one;
5. `alpha_j(beta) = integral exp((beta/2) chi(g)) chi_j(g) dg`;
6. pairing `alpha_1 alpha_(1/2)^2 / 16`;
7. manufactured gate `pairing >= beta^4 / 512` for `0 < beta <= 1`;
8. after deleting the third branch the half-cell cycle rank falls from two to
   one and the theta sector is unavailable.

The item numbered 7 above is only the local manufactured inequality.  It must
not be presented as programme Gate 7.

## Layer contract and allowed open bricks

The implementation must use new modules with one-way dependencies:

1. a finite combinatorial half-cell, three branches, deletion, and cycle rank;
2. concrete SU(2) configuration, reflection, holonomy identity and weight;
3. concrete witness algebra and anti-vacuity witnesses;
4. a Haar-analysis layer whose unavailable analytic facts are fields of a
   named, nonempty-input certificate rather than project axioms;
5. a representation layer using the general SU(2) twice-spin coupling rule,
   not a predicate definition equated to the desired sector;
6. a coefficient layer deriving dimensions, central multipliers, the factor
   `1/16`, and the gate from explicit coefficient lower-bound hypotheses;
7. an endpoint returning only the conjunction actually discharged.

The anticipated open bricks, if existing infrastructure cannot close them
without expanding the contract, are:

- the concrete normalized-Haar two-character integral and its integrability;
- the coordinate-change/Fubini discharge from the three conditional identities
  to the complete `L2` orthogonal complements;
- the concrete SU(2) character-expansion coefficient bounds on the fixed beta
  interval;
- the identification of the abstract coupling profile with a fully constructed
  continuous SU(2) representation tensor product.

Every such brick must occur in Lean as a named hypothesis or structure field.
No prose-only hole is permitted.

### Loaded-hypothesis rule

A loaded hypothesis must state the missing **technical step**, never restate a
headline conclusion.  In particular, if an endpoint concludes `X = c * Y`, it
is forbidden to load `h : X = c * Y`.  Permitted inputs are concrete missing
steps such as a measure-preserving coordinate change, a Fubini exchange with
its integrability premises, a Schur integral, or a convergence/lower-bound
lemma for a coefficient series; the endpoint equality must then be derived by
the artefact's own definitions and lemmas.

Operational participation test: after a loaded hypothesis is discharged, the
proof of each headline must still invoke a substantive lemma defined by this
artefact.  If removing the artefact lemmas leaves the headline as a direct use
of the hypothesis, that hypothesis is malformed and the endpoint must be
reduced.  The repository validator for this task must make this rule visible by
rejecting hypothesis/field declarations that contain a headline constant or a
headline equality verbatim, followed by a recorded manual participation review
for cases that syntax alone cannot decide.

## Sign discipline

No theorem in this artefact may enlarge the gate beyond `0 < beta <= 1`.
If a negative-beta observation is ever recorded, it must be marked `POST-HOC`
and kept as the indivisible statement: the concrete witness retains a positive
pairing and the bound through the square of `alpha_(1/2)`, but this is not
reflection positivity because a one-link operator has negative half-integer
eigenvalues and the form is not positive semidefinite.

## Two-core caveat

Any pruning result must take a local hypothesis that the incidence-one edge
occurs only in the weight and not in the observable.  Cycle rank at least two
is necessary and is never stated to be sufficient.

## Anti-vacuity and acceptance tests

The final artefact must exhibit, independently of its target equalities:

- a point at which `F` is nonzero;
- a normalized measure with nonzero total mass;
- membership of `beta = 1` in the exact domain;
- cardinality three of the branch type;
- a concrete proof that SU(2) is not a singleton;
- derivations, rather than result-bearing definitions, of `1/2`, `3/4`,
  `1/16`, and `beta^4/512` wherever each is claimed.

Acceptance requires exact-target Lean builds, a separate `#print axioms`
oracle whose headline output is contained in `[propext, Classical.choice,
Quot.sound]`, no `sorry`, `admit`, `sorryAx`, or project axioms, documentary
validators, `git diff --check`, a clean worktree after commit, an independent
rational/numerical certificate run twice with byte-identical output when it
adds evidence, and a zero diff in the frozen lane.

The delivered SHA must be sent to a new blind adversarial audit.  This charter
does not authorize the manufacturer to assign that external verdict.
