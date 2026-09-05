# CMP89 (2.42): regional value-bound consumer design

Status: cold-sealed at source checkpoint
`466b9de31df1fd65ec86092908746a250edb5b4b` by the fail-closed
same-checkout supplement recorded in Ledger Addendum 973.  This note remains
design context; the ledger and evidence package are seal authority.

## Exact boundary

The cold-gated prefix constructs and bounds the literal source-order image
series for the normalized full-lattice CMP89 (2.48) Green.  The remaining
source input is the named
`CMP89NeumannReflectionRepresentationCertificate` tying one explicit
regional kernel to that same explicit full-lattice kernel by CMP89 (2.42).

The next module is a consumer, not a reconstruction of (2.42).  It must:

1. take the regional kernel and the representation certificate as parameters
   of the theorem signature;
2. fix the full-lattice kernel definitionally to
   `cmp89Eq248PhysicalFullLatticeGreen L j mass a`;
3. rewrite the regional value by
   `CMP89NeumannReflectionRepresentationCertificate.eq_series`;
4. apply `norm_cmp89Eq248PhysicalNeumannReflectionSeries_le_draft` without
   changing its literal amplitude, fine rate, varying-period product or
   retained direct `l1` weight.

The theorem may not receive a regional bound separately, choose a second
`B0`/`delta0`, exchange a fine distance for an owner distance mentally, or
claim that the representation certificate has been produced by Lean.  The
certificate remains the single named CMP89 (2.42) source input until the
printed multiple-reflection derivation is reconstructed.

## Required output

For `x,n` in the nonempty half-open source rectangle, derive

```text
norm (regionalGreen x n) <=
  2^4 * cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
    (product_mu 2 /
      (1-exp(-(rho/L^j)*cmp89NeumannReflectionPeriodNat m mu))) *
    cmp89SignedLatticeL1ExponentialWeight (rho/L^j) (x-n).
```

Every factor must remain visible.  In particular, there is no rectangle
cardinality, common scalar period, ball-count majorant or hidden regional
constant.

## Acceptance gates

- The representation certificate fixes the same `m`, `regionalGreen` and
  literal physical full-lattice Green consumed by the bound.
- The mass window, common radius, amplitude condition, central complex window
  and noncentral complex radius remain explicit inputs.
- `side_pos` comes from the representation certificate; it is not duplicated
  as an independently chosen rectangle hypothesis.
- The output is a regional value estimate only.  Derivative/Laplacian action,
  fine-to-owner scale transport, uniform-in-depth `B0, delta0`, window 15,
  rows 23--24 and `TermSource` remain open.
- This brick does not move `20/41`.

## Sealed result

The consumer and its audit compile in the fresh cold-origin checkout.  The
single theorem rewrites through the named CMP89 (2.42) representation
certificate and applies the already sealed source-order image-series bound.
It introduces no regional constant, rectangle cardinality, common-period
replacement or owner-metric identification.  The certificate construction,
fine-to-owner transport and uniform-in-depth pair remain open.
