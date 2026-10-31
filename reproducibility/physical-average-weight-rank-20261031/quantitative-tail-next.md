# Exact next interface after the finite physical bound

One active question: quantitative tail and actual-family rank divergence.
Existing theorem in TorusFourierEnergyBound.lean:

    stdAddChar_centered_bound (R : Nat) (k : Fin (2*R+1)) :
      norm(stdAddChar((k.val:ZMod n)-(R:ZMod n))-1)
        <= 2*pi*R/n

It needs NeZero n but does NOT need 2R<n. For r:Fin R take
k.val=r.val+1+R; omega gives k.val<2R+1. Push natural casts and use ring
to identify k-R with r+1 in ZMod n. Do not use wrapped ZMod.val as a small
integer representative. The resulting squared norm is bounded by
(2*pi*R/n)^2. Sum R terms and use nonnegativity of the actual spatial mean
(derived from hw) to get the sufficient total trace bound

    8*pi^2*(1+b_ij)*R^3/n^2.

No exact sum of r^2 or optimal constant is required. Keep the finite
inequality's R<n cutoff; it is enough that n grows past each fixed R.
For a family use lattice sizes n+1 to get NeZero automatically, fixed
d,Nc,i,j and fixed c>0. Allow F_n, w_n, observations, K_n,delta_n,radius_n
to vary. Assume the actual directional mean ratio (1+b_ij(n))/(n+1)^2
tends to zero. For each fixed R the derived trace bound tends to zero,
hence is eventually<c. If q_n<2R, integrality gives q_n+1<=2R, forcing
c<=c*(2R-q_n)<=trace<c, contradiction. Thus q_n>=2R eventually, and
q_n tends to infinity. Fixed positive c is essential; do not silently let
c_n tend to zero. This does not yield volume-order density.

Implement the positive-frequency multiplier transport, trace bound, scalar
integer-rank convergence lemma and actual-family composition without
inserting the desired trace comparison as an assumption. No original
priority, physical source, interacting/continuum result or mass gap follows.
