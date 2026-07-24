# Finite-interval direct W-sign relay: logical audit (2026-07-22)

A bounded independent consultation was requested from Fable High and accepted
only after the bridge reported `verified_model=claude-fable-5` and
`isError=false`.  The question supplied the exact identities

```text
W^J = exp(-8 beta) W
W   = 4 F_B^2 E'
```

The logical conclusion is:

1. On a genuine interval cover whose every box has an outward-rounded strict
   upper bound `W^J<0`, the exact positive rescaling gives `W<0`; then
   `W=4 F_B^2 E'` forces `F_B != 0` and `E'<0` pointwise.
2. Such a cover may replace `(H_tail)` only on the covered compact domain and
   only after a role audit shows that `(H_tail)` is not used elsewhere in the
   proof.  Any noncompact complement still needs `(H_tail)` or another proved
   tail argument.
3. Candidate or sampled rows are insufficient: promotion still requires exact
   box adjacency, domain inclusion, directed rounding, strict margins, replay,
   hashes, and a manuscript proof that uses the direct-sign proposition in
   place of the old relay only on the matching domain.

This audit does not promote any gate.  The current pair mean-value archive is
only a right-edge candidate strip; it is not an exhaustive cover of
`beta in [1629/16,1000/9]` and `t in [0.6,pi-3/(2 beta)]`, so the finite relay
and G2 remain open.

## Executable algebra check (2026-07-24)

The quotient step is now independently checked by the dependency-free script
`scripts/verify_surface_finite_w_sign_relay.py`.  On exact rational abstract
numerator/denominator jets it verifies

```text
4*F_B^2*E_prime = W,
W^J = s^2 W  (s>0),
F_B>0 and W<0  =>  E_prime<0.
```

This closes the algebraic implication only.  It does not certify the missing
finite-beta cover, the analytic tail bound, or any gate promotion.

## Rescue-300 dependency checks (2026-07-24)

The role audit `scripts/audit_surface_h_tail_role_usage.py` finds eight
manuscript occurrences of `(H_tail)`, all confined to the extraction/regular
tail discussion and Proposition `k2endpoint`; it reports no unexpected use in
the finite direct-sign row.  The rescue-specific contraction audit
`scripts/verify_surface_scaled_bulk_cwin3p2_rescue300_tail_contract.py` passes
the six available order-40/order-50/300-bit production units, with global
maximum derivative-tail ratio `0.0205197526375481973...` (at the
`[3259/32,3261/32]` unit).  These are dependency and role checks only: they
do not establish the missing finite cover or convert `W<0` into `(H_tail)`.
