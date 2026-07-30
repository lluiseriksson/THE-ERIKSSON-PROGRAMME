# CONTINUUM-C1 technical report

## Autonomous result: a finite strong-coupling cap

The checked two-plaquette theorem uses, at `t=ε=1`, the strict hypothesis

```text
(16d+1)² exp(3)
  ((exp(|β|N_c)-1) + s + (exp(|β|N_c)-1)s) < 1
```

with `s>0`. C1 proves in Lean that this forces

```text
β < β_max(d,N_c)
  := log(1 + exp(-3)/(16d+1)²) / N_c
```

whenever `β≥0` and `N_c>0`. The cap is finite, positive, and independent of
volume and cutoff. It is necessary, not sufficient: it is the supremum
obtained by dropping the positive `s` terms.

The same file proves two consequences:

1. for `β(a)=1/(g²a²)`, the KP hypothesis fails whenever
   `g²a² β_max≤1`;
2. for every abstract trajectory `β(i)→+∞`, the KP hypothesis is eventually
   false.

It also proves non-vacuity in two independent ways:

- `kpRadiusAtUnit_nonempty_from_checkedWindow` consumes the repository theorem
  `sun_clustering_window_nonempty` and returns a witness with `β>0`;
- `kpRadiusAtUnit_witness_4_3` verifies the numerical point
  `(d,N_c,β,s)=(4,3,0,1/200000)`.

The first theorem is the typed producer bridge: an incompatible change to the
checked window now breaks the C1 build.

`checkedCorrelatorAfterKPRadiusAtUnit` goes one step further and partially
applies the actual `sun_two_plaquette_correlator_bound` through its `hr`
argument. The remaining hypothesis/result type is inferred by Lean. Thus a
change to the consumer's radius argument, even if an old non-vacuity lemma
survived, also breaks C1.

Thus the existing volume-uniform clustering theorem cannot be sampled along
any continuum trajectory whose bare inverse coupling diverges. Volume
uniformity and cutoff uniformity are different obligations.

| `d` | `N_c` | `β_max` |
|---:|---:|---:|
| 4 | 3 | `3.927950692443e-6` |
| 4 | 2 | `5.891926038665e-6` |
| 3 | 2 | `1.036787842219e-5` |

The executable arithmetic audit is VERIFIED only; the Lean theorem is the
proof.

## Dimensional contract

`TightnessScaleNoGo.lean` introduces only:

```text
ScaleDict.a              -- positive physical length
ScaleDict.g2             -- positive physical squared coupling
physicalLength(n)=a n
physicalArea(n)=a² n
beta2D=1/(g²a²)
```

It imports the checked two-plaquette producer, but does not edit or assume
Continuum-C0, RG, hRpoly, or thermodynamic-limit infrastructure.

## Status of the positive target E2

The preregistered two-dimensional free-boundary `U(1)` target was

```text
| (I₁(β(a))/I₀(β(a)))^ceil(A/a²) - exp(-g²A/2) |
  ≤ 3 g⁴ A a².
```

It was not proved, and no claim of it is made. The first blocker is analytic,
before the finite-lattice factorization. The Amos development defines
`besselIReal` by a Γ-power series, whereas the `U(1)` Haar computation
produces

```text
∫ exp(β cos θ) dθ
and
∫ exp(β cos θ) cos θ dθ.
```

The pinned Mathlib tree contains no Bessel development that identifies these
integrals with the repository series. The minimal successor contract is
therefore:

```text
besselIReal_integral_repr_zero (x>0) :
  besselIReal 0 x = (1/π) ∫₀^π exp(x cos θ) dθ

besselIReal_integral_repr_one (x>0) :
  besselIReal 1 x = (1/π) ∫₀^π exp(x cos θ) cos θ dθ
```

After that bridge, the finite free-boundary `U(1)` factorization is a separate
and likely smaller obligation. Driver's Theorems 8.8/8.10 give related planar
convergence but not either missing theorem or the preregistered constant.

A heat-kernel/Villain version is a useful warm-up: its character coefficients
give an exact fixed-area expectation with rate zero. It would validate the
factorization machinery, but is not the Wilson `O(a²)` result and must not be
presented as such.

The elementary Haar calculation has been removed from the body. It is isolated
in `HAAR-BETA-ZERO-APPENDIX.md`, whose title and scope state explicitly that it
says nothing about `β>0`.

## Adversarial audit

- The proof keeps `s>0`; setting `s=0` changes the checked hypothesis.
- `β_max` contains only `d` and `N_c`, not a volume or cutoff.
- The theorem is a no-go for this KP radius, not for all cluster expansions
  or for continuum Yang--Mills itself.
- The physical `a` and `g²` are explicit and positive; the abstract no-go
  assumes only `β→+∞`.
- The window has both a producer-derived positive-coupling witness and a
  fully numerical witness.
- E2/G1 and E2/G2 remain unproved and are labelled as such.
- Fable High returned HTTP 429 and contributed nothing.

## Verification and classification

The direct Lean build succeeds. All seven oracle queries report exactly
`[propext, Classical.choice, Quot.sound]`; the prose checker reports one
module and zero failures. There are no `sorry` declarations or project
axioms.

This lane closes a real negative lemma and isolates the first missing positive
bridge. It is a technical report, not a programme paper.
