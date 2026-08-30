# CMP89 rectangular region to CMP99 owner geometry

Status: design only.  This note is not compiler or seal authority.

## Boundary left by the owner-rate consumer

The hot-green owner-rate theorem consumes exactly

```text
L^j <= reflectionPeriodNat(m, mu)
(L^j) * ownerDist <= l1(x-n) + boundary.
```

It does not accept or construct an owner map.  A source-facing specialization
must construct both facts from the actual rectangle and the CMP99 localization
geometry.

## First independent sub-brick: period floor

For the half-open integer rectangle, expose the physical side-floor condition

```text
(L^j : Z) <= m_mu.
```

Together with `m_mu > 0` from the representation certificate and the literal
period `2*m_mu`, this proves

```text
L^j <= cmp89NeumannReflectionPeriodNat m mu.
```

This theorem must cite the already sealed cast equality for the natural
period.  It may not replace the coordinate periods by a common period or infer
the floor merely from positivity of `m`.

## Physical owner/metric sub-brick

CMP89 page 584 uses integer coordinates on the fine lattice
`xi Z^4`, `xi = L^-j`; CMP99 owners are the `blockSite` owners at fine side
`L^j`.  The physical specialization therefore needs one literal embedding of
the source rectangle point into the actual finite fine carrier and must then
apply the sealed inverse-scale comparison

```text
ell * finBoxDist(owner x, owner n)
  <= finBoxDist(x,n) + 2*(ell-1).
```

The remaining bridge is in the load-bearing direction

```text
finBoxDist(embedded x, embedded n) <= l1(x-n).
```

No arbitrary `ownerOf` field is admissible.  The embedding must be defined
internally from the nonnegative half-open rectangle coordinates and a visible
fit condition into the actual finite carrier.  Translation of a nonzero
rectangle origin, if required by the source dictionary, must be a separate
explicit equality rather than silently setting the origin to zero.

## Acceptance gates

- Period floor and metric bridge remain separate theorems.
- The boundary payment is the literal `2*(L^j-1)` and its exponential cost is
  visible.
- The owner is definitionally the CMP99 localization owner after the source
  embedding.
- The result does not construct CMP89 (2.42), claim uniformity in depth,
  attain window 15, move `20/41`, or instantiate `TermSource`.

