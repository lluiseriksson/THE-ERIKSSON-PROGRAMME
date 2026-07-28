# Surface release gate — independent closed-form anchors (2026-07-28)

The prior final seal checked consistency among manifests, transcripts, gates,
and the PDF.  It could not detect a normalization error shared by all of those
artifacts.  The double-`H0/K0` incident was instead detected by an independent
closed-form normalization.

The replacement release rule is:

> No load-bearing assembled quantity may enter a green final seal without an
> independently derived exact algebraic or closed-form anchor wired into the
> executable seal.

The first mandatory anchor set is:

1. all live full-moment `Y` helpers use the physical factor
   `4*B/(delta*KD^2)` and contain no legacy second `H0/K0`;
2. every relative companion has exact constant term one and
   `Brel*D-2*root*Arel` vanishes exactly at `delta=0`;
3. the `Q` half-line algebra is rederived symbolically;
4. the two-block and three-block determinant decompositions are symbolic
   identities;
5. both weak-main terminal relays have positive exact-rational margins;
6. the finite Wronskian relay satisfies
   `4*F_B^2*E'=W` and preserves sign under positive common scaling.

This gate is independent of interval coverage.  Both it and the numerical
coverage auditors must pass.  Neither can substitute for the other.
