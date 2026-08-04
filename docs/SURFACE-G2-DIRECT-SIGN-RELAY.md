# Direct finite-beta sign relay

The scaled coefficient families are homogeneous of degree four in the common
factor `J_m=e^{-beta}I_m`.  Therefore, for an abstract positive scale `s`,
`A^J=s^4 A` and `B^J=s^4 B`, including their derivatives in `t`.  The
Wronskian consequently satisfies `W^J=s^8 W`.  Independently,

```text
W = 2(A_t B - A B_t) = 4 B^2 (A/(2B))_t.
```

The executable polynomial certificate
`scripts/verify_surface_direct_sign_relay.py` proves these identities without
floating point arithmetic or sampled values.  Thus a terminal finite-beta
cover of `W^J<0`, together with the already separate theorem `B=F_B>0`, would
imply `E'<0` directly on that covered domain.

This is an algebraic relay only.  It does not prove `B>0`, fill the remaining
beta gaps, certify the moving `t` seam globally, or discharge the historical
`(H_tail)` extraction obligation.  It therefore carries no G2/G6 promotion
until the coverage and gate contract are amended and independently audited.
