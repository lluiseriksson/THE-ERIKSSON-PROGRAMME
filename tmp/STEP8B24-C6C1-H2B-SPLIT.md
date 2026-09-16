# Step 8b.24 C6c.1/H2b radial split (PRE-VALIDATION)

This note fixes the two radial branches produced when the global H2a strip
quotient is multiplied by the already sealed noncentral complex endpoint
quotient.  It is design evidence only; no declaration below is currently
compiler-verified.

For the shifted real alias momentum

```text
q_m(mu) = p(mu) + 2*pi*m(mu),     m != 0,
```

H2a on the concrete local pair gives, after the CMP95 carrier proves
`0 < ||u||_2 <= 1`,

```text
phaseQuotient(z,u,alpha)
  <= 2*exp(2*rho) * (||q_m||_2^alpha + rho).
```

The sealed derivative/average/fine-symbol quotient contributes

```text
R(rho) * ||q_m||_2^(-1) * aliasWeight(1,m),
```

where `R(rho) = cmp89Eq251ComplexNoncentralEndpointRadialConstant rho`.
Their product therefore has two and only two radial branches:

```text
source branch:    ||q_m||_2^(alpha-1) * aliasWeight(1,m)
vertical branch:  rho * ||q_m||_2^(-1) * aliasWeight(1,m).
```

The source branch uses
`cmp89Eq251EuclideanNorm_rpow_mul_aliasWeight_le_sourceWeight` at `alpha`.
The vertical branch uses the same theorem at `alpha = 0`, then the new
pointwise exponent-monotonicity lemma
`cmp89Eq251AliasWeight_alpha_zero_le_alpha`.  Consequently both land on the
single literal weight

```text
aliasWeight(cmp89Eq251AliasSeriesExponent 4 alpha, m)
```

with no alias-cardinality loss and no second hidden series.  A source-shaped
combined constant may be written explicitly as

```text
2 * exp(2*rho) * R(rho) * (3^(1-alpha) + 3*rho).
```

There are two consumers and they must not be conflated.  The source-generic
H2b signature must obtain `||u||_2 <= 1` from the concrete CMP95 (1.109)
seminorm index.  The physical hRpoly specialization already has a stronger
route: the sealed physical-bond dictionary supplies a unit integer
displacement, the H1 draft proves `||xi*u||_2 = xi`, and
`cmp89Eq245_inverseScale_mem_Ioc` gives `xi <= 1` for
`xi = (L^j)^(-1)`.  Thus the physical producer can construct the local-pair
witness internally even before the primary CMP95 carrier is frozen.  Neither
route may accept that inequality, either radial bound, or the final
source-weight estimate as a caller hypothesis.
The transport endpoint phase remains part of the literal complete summand;
its signed-contour decay is handled only after the H3/H4 complete-integrand
contour and must not be removed by an absolute-value split in H2b.

The first physical H2b subbrick is now written statically as

```text
BalabanCMP89Eq249PhysicalFineComplexHolderPhaseQuotient.draft.lean
```

It stops deliberately before the endpoint product. Its endpoint constructs
`u != 0`, rewrites the physical Euclidean norm to `xi`, and proves

```text
physicalFineComplexPhaseQuotient
  <= 2*exp(2*rho) * (||q_m||_2^alpha + rho).
```

The two imports naming the promoted H1 and H2a modules are an explicit future
import contract; the draft is not a compilable target until those leaf bricks
have been promoted and materialized. No part of this note or draft changes
the terminal counters.
