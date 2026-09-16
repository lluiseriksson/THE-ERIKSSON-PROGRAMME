## What changed

- constructs the literal interacting Wilson Hessian and physical corrections `R₁`, `R₂`, and `R₃`;
- closes the real-sector equation-(2.16)/(2.21) chain and literal real interaction exponent;
- derives the face-connected localization geometry and discharges the equation-(2.19) metric budget from primary-source conditions;
- proves exact support of the localized mixed derivative kernel;
- constructs the radial Taylor/Riesz operator `Q_f(B)` and proves `f(B) = 1/2 <B,Q_f(B)B>` under the exact origin normalizations;
- defines the mandatory source core `F_Y = V_k - V''_k`, constructs `Q(Y,B)` only from its radial Hessian, and reconstructs `V_k` exactly;
- proves the no-loss transfer from a radial Hessian bound to the printed equation-(1.43) bound on `Q(Y,B)`;
- formalizes the exact pre-localization CMP102 equation-(80) functional
  `-<H D₃(A'),J> - <A',Δπ H D(A')> + 1/2 <H D(A'),Δπ H D(A')> + V₀(A' - H D(A'))`;
- proves its value and derivative vanish at the origin from the source-facing normalizations, without assuming `D'(0)=0`;
- proves its `C²` regularity from `C²` data and supplies a nontrivial witness;
- formalizes the repeated fundamental-theorem-of-calculus mechanism of
  equations (1.9)--(1.10) as a finite-depth expansion tree whose branches must
  equal genuine coordinate derivatives and interval integrals;
- proves that every valid FTC tree sums exactly to its fully coupled endpoint,
  with a nonzero certified witness and without replacing the derivative
  integrals by endpoint finite differences;
- constructs the canonical connected component of the active weakening carrier
  containing the distinguished plaquette cube;
- proves exact finite regrouping by those anchored connected domains, rather
  than by an arbitrary domain label;
- defines the literal weakened finite random-walk sum with coefficient
  `prod_{Delta in active(walk)} s(Delta)`;
- proves recovery of the original walk sum at `s = 1`, exact removal of walks
  leaving `K` when `s = 0` outside `K`, and the coordinate derivative term by
  term;
- consumes that derivative in the genuine one-coordinate FTC identity, so the
  weakened walk algebra is connected directly to the interpolation layer;
- adds focused axiom audits for every new public endpoint.

## Why

The source-facing chain now has two rigorously separated levels:

```text
CMP102 equation (80), before localization
  -> exact global potential functional
  -> origin normalization and C² regularity

(localized total V_k, specified residual V''_k)
  -> F_Y := V_k - V''_k
  -> physical Hessian bound along tB
  -> radial Taylor average
  -> Q(Y,B) with the identical bound
  -> 1/2 <B,Q(Y,B)B> + V''_k(Y,B) = V_k(Y,B).

finite physical weakening family (once constructed)
  -> repeated genuine FTC in every s(Delta)
  -> raw derivative-integral terms
  -> canonical anchored connected component Y
  -> exact fiberwise regrouping by Y.

finite walk terms and their active cubes
  -> literal weakened sum H(s)
  -> exact coordinate derivative
  -> FTC step
  -> exact support restriction when s vanishes outside K.
```

The radial transfer loses no constants because `2 * integral_0^1 (1 - t) dt = 1`. The interfaces cannot silently set `V''_k = 0`, assume a bound directly on `Q`, identify `Q(Y,B)` with the endpoint Hessian, or insert the global equation-(80) functional as an already localized activity.

## Epistemic boundary

The following remain open and are not claimed here:

- instantiating the global equation-(80) data `D`, `D₃`, `V₀`, `H`, `Δπ`, and `J` with the concrete CMP102/CMP116 objects;
- performing the source-faithful localization/decomposition into `Y` and identifying the resulting concrete `total` and `residual`;
- constructing the concrete generalized random walks and operator-valued terms
  of the physical propagators, then proving their source kernel decay and
  instantiating the finite weakened-sum/FTC layers;
- deriving the raw-term `active` carrier and distinguished plaquette `anchor`
  from those propagators, then identifying the resulting connected fiber sums
  with the CMP116 localized activities;
- deriving the physical radial-Hessian estimate of equation (1.43) from that localized activity;
- deriving the separate residual estimate (1.36) for `V''_k(Y,B)`;
- the complex-contour analogue and source-faithful distribution inside equation (2.14);
- the complete residual/cardinality ledger and factorization of (2.26);
- `hraw`, `hRpoly`, the continuum limit, or the Yang--Mills mass gap.

No pointwise-Hessian substitution, zero-residual shortcut, synthetic summand, post-hoc `termWeight`, renamed kernel hypothesis, or global-to-local identification replaces these open physical steps.

## Validation

- `lake build YangMillsCore`: success, **8,582 jobs** at head `193036c3`;
- focused CMP102 equation-(80) build: **2,473 jobs**;
- focused iterated-FTC build: **2,623 jobs**;
- focused anchored connected-regrouping build: **8,183 jobs**;
- focused weakened-random-walk build: **2,659 jobs**;
- all six new equation-(80) endpoints report only `propext`, `Classical.choice`, and `Quot.sound`;
- all fourteen FTC/regrouping endpoints report only `propext`, `Classical.choice`, and `Quot.sound`;
- all twelve weakened-random-walk endpoints report only `propext`, `Classical.choice`, and `Quot.sound`;
- the six equation-(80) endpoints, fourteen FTC/regrouping endpoints, twelve weakened-walk endpoints, 34 radial identity/operator/support/dictionary/source-split/bound endpoints, and 24 preceding source-geometry/localized-derivative endpoints are audited (**90 endpoints** in this source-facing slice);
- no `sorry`, `admit`, local `axiom`, `unsafe`, or `opaque` in the new modules;
- branch remains a draft stacked on `codex/hrpoly-b3-card-tilt`;
- frozen CMP116 reduction releases are unchanged.

No public GitHub Actions run is claimed for this head; the builds and audits above were executed locally in the pinned project environment.
