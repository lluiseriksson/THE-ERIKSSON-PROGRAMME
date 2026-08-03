# CONTINUUM-C1 obligation matrix

## Reproducibility anchor

- Lane: `codex/continuum-c1`
- Upstream: `origin/main`
- Fixed starting SHA: `81721890ad3e111d73cbe45074d42ec698ce07b2`
- Latest fetched `origin/main` at closeout:
  `7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a`
- Recorded: 2026-07-30 (Europe/Stockholm)

The later upstream commit changes only occupied Paper 13 files. It is not
merged into this lane.

There is no physical lattice-spacing variable in the checked Lean tree.  The
`spacing` names under `YangMills/RG/**` are dimensionless block indices, not a
physical length.  C1 therefore owns a minimal dimensional contract and does
not wait for, import, or edit Continuum-C0.

## The three obligations

| Observable | Physical normalization and `a` dependence | Existing evidence | Exact gap |
|---|---|---|---|
| Wilson loop at fixed physical area `A` | In two dimensions use `n_p(a)=⌈A/a²⌉`, `β(a)=1/(g²a²)`, and compare `⟨W_a⟩` with `exp(-g²A/2)`. | The repo proves real-order Amos upper and lower bounds for its Γ-series definition of `I_{ν+1}/I_ν`. The strong-coupling area law is uniform only in volume. | First prove the integral representation of `besselIReal` at `ν=0,1`; only then identify the `U(1)` Haar Fourier coefficient, prove free-boundary factorization, and apply Amos with the ceiling error. |
| Smeared curvature / plaquette | In two dimensions a curvature-scale plaquette observable has an `a⁻²` normalization; in four-dimensional action density the normalization is `a⁻⁴`. | The checked Haar identities give an elementary diagnostic at exactly `β=0`, isolated in `HAAR-BETA-ZERO-APPENDIX.md`. | A positive result needs a scale-dependent weak-coupling law plus centering/smearing and a uniform moment. The `β=0` diagnostic says nothing about any `β>0` trajectory. |
| Connected correlator at fixed physical separation `r` | Lattice separation is `k(a)=⌈r/a⌉`; a lattice rate `exp(-c k)` corresponds to physical mass `c/a`. | `sun_two_plaquette_correlator_bound` gives a volume-uniform lattice-distance rate in a finite small-`β` window. | The continuum trajectory has `β(a)→∞`, while the KP hypothesis forces `|β|<β_max(d,N_c)<∞`; the existing result cannot be evaluated along sufficiently small `a`. |

## Independently derived KP cap

At `t=ε=1`, the binding radius hypothesis in
`TwoPlaquetteCorrelator.lean` is

```text
(16d+1)² exp(3)
  ((exp(|β|N_c)-1) + s + (exp(|β|N_c)-1)s) < 1.
```

The activity factor is exactly `exp(|β|N_c)(1+s)-1`.  For `s>0`, the
hypothesis implies the strict necessary cap

```text
|β| < β_max(d,N_c)
    := log(1 + exp(-3)/(16d+1)²) / N_c.
```

Independent binary64 evaluation:

| `d` | `N_c` | `(16d+1)²` | `β_max` |
|---:|---:|---:|---:|
| 4 | 3 | 4225 | `3.927950692443e-6` |
| 4 | 2 | 4225 | `5.891926038665e-6` |
| 3 | 2 | 2401 | `1.036787842219e-5` |

This is a necessary supremum as `s ↓ 0`, not the conservative witness
constructed by `sun_clustering_window_nonempty`.

## Decision

E1 is proved: any trajectory with `β(a)→∞` is eventually incompatible with
the checked KP radius hypothesis. Its non-vacuity theorem consumes
`sun_clustering_window_nonempty` directly, so the connection is compiler
checked. E2 remains the positive two-dimensional target. Its first missing
analytic bridge is the integral representation of the repository's
Γ-series `besselIReal` at orders zero and one.
