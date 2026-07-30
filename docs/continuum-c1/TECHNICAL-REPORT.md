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

It imports only Mathlib. It does not import, assume, or edit Continuum-C0, RG,
hRpoly, or thermodynamic-limit infrastructure.

## Status of the positive target E2

The preregistered two-dimensional free-boundary `U(1)` target was

```text
| (I₁(β(a))/I₀(β(a)))^ceil(A/a²) - exp(-g²A/2) |
  ≤ 3 g⁴ A a².
```

It was not proved, and no claim of it is made. The exact first blocker is G1:
the repository has no `U(1)` configuration/measure, axial-gauge, or
free-boundary plaquette-independence theorem from which to derive

```text
⟨W_a⟩ = (I₁(β(a))/I₀(β(a)))^ceil(A/a²).
```

The existing Amos real bounds provide the right analytic bracket for G2, and
Driver's Theorems 8.8/8.10 establish convergence in a related planar setting,
but neither substitutes for G1 or supplies the preregistered constant.
Building the missing gauge substrate here would duplicate infrastructure
outside this lane's ownership.

The minimal successor contract is:

```text
freeBoundaryU1WilsonFactorization :
  expectation WilsonLoop =
    (Real.besseli 1 beta / Real.besseli 0 beta) ^ enclosedPlaquettes
```

with the finite domain, boundary condition, orientation, and normalization in
the theorem type. Only after this bridge exists is the Amos-to-`O(a²)`
inequality a valid C1 target.

## Auxiliary Haar obstruction

At the independently controlled Haar endpoint, the checked repository
identities `|Re Tr U|≤N_c` and `E Re Tr U=0` imply, for `N_c≥2`,

```text
P(a⁻⁴(N_c-Re Tr U) ≥ N_c/(2a⁴)) ≥ 1/3.
```

Indeed `X=N_c-Re Tr U` satisfies `0≤X≤2N_c` and `E X=N_c`; splitting at
`N_c/2` gives

```text
N_c ≤ N_c/2 + (3N_c/2) P(X≥N_c/2).
```

This calculation is diagnostic evidence, not a C1 Lean artifact and not a
claim about a tuned weak-coupling law. Transport to a lattice plaquette still
requires an explicit Haar pushforward premise.

## Adversarial audit

- The proof keeps `s>0`; setting `s=0` changes the checked hypothesis.
- `β_max` contains only `d` and `N_c`, not a volume or cutoff.
- The theorem is a no-go for this KP radius, not for all cluster expansions
  or for continuum Yang--Mills itself.
- The physical `a` and `g²` are explicit and positive; the abstract no-go
  assumes only `β→+∞`.
- E2/G1 and E2/G2 remain unproved and are labelled as such.
- Fable High returned HTTP 429 and contributed nothing.

## Verification and classification

The direct Lean build succeeds. The three oracle queries report exactly
`[propext, Classical.choice, Quot.sound]`; the prose checker reports one
module and zero failures. There are no `sorry` declarations or project
axioms.

This lane closes a real negative lemma and isolates the first missing positive
bridge. It is a technical report, not a programme paper.
