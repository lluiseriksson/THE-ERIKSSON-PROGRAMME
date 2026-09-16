# CMP89 Neumann arbitrary-depth continuation

Status: design checkpoint only.  This file is not compiler evidence and does
not move `20/41`.

## Immediate promoted brick after physical feedback seals

`BalabanCMP89SourceNeumannGeneratedTwoScalePhysicalPoincare`

- construct `Omega2` and the first coarse region from the literal iterated
  lift;
- construct the first coarse background from
  `CMP99SourceNormalizedRegionalScale.ofFineSmall`;
- derive its small-field radius from the supplied closed `Ubar` budget;
- consume
  `cmp89SourceNeumann_twoScale_quantitativePoincare_of_physical_feedback`;
- use the already proved common positive radius to produce one quantitative
  depth-two `CMP89SourceNeumannRegionalPoincare` certificate.

No independent region, coarse background, radius or Poincare certificate is
accepted from the caller.

## Honest recurrence boundary

The arbitrary-depth continuation is not repetition of the current scalar
gate.  If `C_r` is the already constructed coarse-prefix Poincare coefficient,
the next composition requires the literal inequality

```text
C_fine(r) * C_r * feedback(r) < 1,
```

and returns

```text
TwoLevelPoincareConstant
  C_fine(r) C_r derivative(r) feedback(r).
```

At depth two, `C_r` is one one-scale coefficient.  At greater depth it is the
recursive coefficient, so the existing product of two one-scale constants
does not discharge the gate.

## Required next algebraic brick

Define the generated recursive coefficient from the physical source data:

```text
C(0)       = oneScalePoincare(spacing_at_terminal)
C(r + 1)   = TwoLevelPoincareConstant
               oneScalePoincare(spacing_r)
               C(r)
               physicalDerivativeCoefficient
               physicalFieldFeedback(radius_r, radius_(r+1)).
```

Then prove one induction theorem that constructs the regional certificate
from the generated region/background/radius tower and a *single terminal
record* containing every adjacent contraction.  A free family of Poincare
certificates or independently chosen backgrounds is forbidden.

The analytic question is whether the source-generated radius chain implies
those adjacent contractions uniformly in prefix depth.  Until that theorem
exists, depth-two reachability must not be reported as a retained-tower or
CMP89 (2.42) result.
