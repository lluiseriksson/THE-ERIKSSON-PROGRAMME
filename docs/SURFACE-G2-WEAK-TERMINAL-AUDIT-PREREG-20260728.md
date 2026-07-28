# G2 weak-main terminal composition audit — preregistration (2026-07-28)

This read-only audit is the proposed successor to the withdrawn sharp-K2
composition.  It may promote only after both weak-main transcript pairs exist
and independently validate.

The audit must reconstruct:

1. the authoritative finite role on `20<=beta<=1000/9`;
2. all three G5 lanes on `0<lambda<=3`;
3. `Q>19/20` on the high-beta interior;
4. the near weak-main certificate on
   `delta in [0,9/1000]`, `t in [21/10,pi_up]`;
5. the far weak-main certificate on
   `delta in [0,9/1000]`, `t in [0,21/10]`;
6. exact adjacency of those two rectangles and `pi<pi_up`;
7. the common-variable mirror inputs
   `rho<7/200`, `|C_mirror|<43/50`, the exact near relay, and the third block;
8. the fixed-gap mirror bound, exact far relay, and the same third block;
9. all beta, delta, lambda, and `p=101/200` seams.

The audit must not import or execute the superseded sharp-positive K2
transcripts, `verify_surface_high_beta_main_positive.py`, or the old
R7/R8 coefficient route.

Until the audit returns
`G2_WEAK_TERMINAL_COVER_PROVED`, the authoritative G2 state remains blocked.
