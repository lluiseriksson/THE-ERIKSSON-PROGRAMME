# Eq. (2.29) D-family dictionary plan

The Eq. (2.29) source route must prove more than a scalar inequality.

## Source objects to identify

```text
Y0                 fixed connected component before Eq. (2.27)
D                  finite family of localization domains Y
Y in D             individual localization domain
union_D Y = Y0     source coverage condition used by Eq. (2.27)
d_k(Y)             localization-domain metric
alpha6 exp(-delta*kappa*d_k(Y))   polymer activity/weight
```

## Lean-side targets

```text
DIndex
DParts
cmp116Eq229Product
CMP116Eq229Summability
CMP116Lemma3Eq229ScaleBoundary
```

`DIndex` and `DParts` are Lean argument/field surfaces in the Eq229 summability
route.  They are not standalone source-extracted declarations, and the
dictionary remains open until the source predicate for Balaban D-families,
admissibility/overlap convention, and metric convention are extracted.

## Dictionary theorem shape

```text
D ∈ SourceDFamily(Y0)
  ↔ DParts(D) is a finite admissible family of localization domains,
     union(DParts(D)) = Y0,
     and the source compatibility relation matches the Cammarota polymer relation.
```

## Required metric facts

```text
sum_{Y in D} (d_k(Y)+5) >= d_k(Y0)+5
(3*2^3)^-1*M^-4*|Y| <= d_k(Y) <= M^-4*|Y| - 1
```

These are already source-located under CMP116, but a compact clean excerpt should be prepared before theorem formalization.
