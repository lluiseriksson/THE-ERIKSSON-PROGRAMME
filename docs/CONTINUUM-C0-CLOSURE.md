# CONTINUUM-C0 closure

**Status: CLOSED as a scale-limit substrate and obstruction package; not
merged; no paper.**

CONTINUUM-C0 supplies typed language for asking a cutoff-limit question
without assuming that a continuum Yang--Mills field already exists.  The
artifact is frozen at
[`7fe64bbced729337f6a1060d731e661384863c42`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/7fe64bbced729337f6a1060d731e661384863c42)
and reviewed through
[draft PR #36](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/36).
It remains outside `main` and therefore outside the current
`YangMillsCore` import closure.

## What the frozen artifact proves

- The explicit spacing `a_n = 1/(n+1)` is positive and tends to zero.
- Scale-indexed observable maps and Gibbs-state sequences are constructed from
  existing discrete data.  The state at scale `n` is produced by the existing
  `integerInfiniteLocalGibbsState`; it is not an arbitrary continuum state
  supplied as input.
- Pointwise weak convergence transports normalization, real linearity,
  positivity, integer-translation invariance, and conditional reflection
  positivity under the named compatibility hypotheses.
- Every `UniformLocalKPRegime d B beta` with `B>0` forces

  ```text
  |beta| < 1 / (((16 d + 1)^2) B).
  ```

  In `d=4`, `B=2`, this is `|beta| < 1/8450`; hence the existing KP state
  producer cannot remain valid along any schedule `beta_n -> +infinity`.
- The canonical axis-pair family consumes the repository's actual
  infinite-volume clustering theorem.  Uniformly for coupling schedules that
  remain inside the proved four-dimensional KP window, the constructed
  connected correlation tends to zero as the lattice offset `2k` tends to
  infinity.
- Pairing that correlation limit with `a_k=1/(k+1)` gives

  ```text
  (physical separation, connected correlation) -> (2, 0).
  ```

  This theorem is the conjunction of **two independent limits in the product
  topology**.  It does not prove that the second component depends on the
  first, identify a continuum two-point law, or establish a physical
  scale--coupling relation.

The deliberately coarse envelope used by the last asymptotic certificate is

```text
3.2 * 10^13 * exp(-k/100).
```

Its first integer value below `1` is `k=3110`, corresponding to lattice offset
`6220`.  This is an asymptotic tail certificate, not a useful quantitative
estimate at moderate separation.

## What it does not prove

CONTINUUM-C0 does **not** construct a continuum probability law, prove
tightness of a genuinely varying family, derive a physical running-coupling
law, connect the declared geometric radius to every embedded observable,
establish a nonzero limiting variance, construct geometric
reflection-positivity data, prove finite-separation nonvanishing, perform
Osterwalder--Schrader/Wightman reconstruction, or prove a continuum mass gap.

The `(2,0)` endpoint is ultralocal/trivial in this strong-coupling lane: the
decay rate remains fixed in lattice units, so the corresponding physical
correlation length shrinks to zero.  The result is valuable as a typed
anti-overclaim boundary and as a list of successor contracts; it is not
positive Clay progress.  The repository's stated distance remains
`~0% (<0.1%)`.

## Frozen evidence

- Branch head:
  [`7fe64bbced729337f6a1060d731e661384863c42`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/7fe64bbced729337f6a1060d731e661384863c42)
- Review vehicle:
  [draft PR #36](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/36)
- Remote `honesty` check on that exact head: `SUCCESS`
- `TwoPointFactorization.lean` elaborated and its `.olean` was regenerated
- Twenty-eight oracle queries: exactly
  `[propext, Classical.choice, Quot.sound]`
- Oracle stderr: empty
- The threshold statement records `k=3110` as the first integer crossing and
  labels it asymptotic rather than practically quantitative
- The paired-endpoint docstring explicitly rejects any inferred dependency
  between the two coordinates

## Successor contracts

C0 is complete on its registered scope.  Its remaining obligations are
successor campaigns:

1. a state producer outside the strong-coupling KP window, with a physical
   scale--coupling law and compatible spacing convention;
2. genuine candidate laws and tightness for a variable family;
3. support-derived geometric scaling for embedded observables;
4. a nontriviality witness such as strictly positive limiting variance;
5. a geometric reflection-positive producer on the continuum-facing test
   algebra; and
6. reconstruction and a continuum spectral gap.

