# Eq. (2.37) source dictionary commit queue

## Commit 1 — source extraction only

```text
docs(sources): extract CMP116 Eq237 fixed-Z0prime display
```

Touches only citation/catalog/report files. No Lean theorem unless the statement is purely definitional.

## Commit 2 — fiber dictionary

```text
feat(RG): identify Eq237 source fiber with Lean Z0Fiber
```

Repository-side helper now available:

```text
cmp116Eq237Z0Fiber_mem_iff
```

Remaining source-side target:

```text
cmp116Eq237_sourceFiber_mem_iff
```

## Commit 3 — component product dictionary

```text
feat(RG): align Eq237 component product with source components
```

Target: product over connected components of `Z0'`, preserving `d_{k+1}`.

## Commit 4 — constant majorants

```text
feat(RG): derive Eq237 amplitude and alpha5 majorants
```

Target:

```text
cmp116Eq237Amplitude
cmp116Eq237FixedZ0PrimeWeight
CMP116Eq237MajorizationBoundary
```

## Commit 5 — feed existing consumer

```text
feat(RG): feed post-P source bound from Eq237 source data
```

Use existing:

```text
cmp116PostPResidualSourceBound_of_eq237
```

No downstream propagation.
