# Offline verification specification for the coexact point-support adapter

Hash context: unit177, analytical proof based on main88f31a1981b757b9240a9076e2012545066b9028.
This is preparation only. No test has executed and no numerical/formal PASS
is claimed. Use an own CPU Colab Pro+ Linux runtime, never a local Windows
oracle. Prepare while disconnected; export, record consumption and disconnect
at the end. Terminal replay requires two fresh clones at the same recipe SHA.

Use Fraction arithmetic and the exact rational triangular profile. Test D=3,
even n=4,8,16. Set c=384,mu=n^2, matching the analytical family. Predeclare:
empty S; one point at0; points at0 and(n-1,0,0); an adjacent three-point
chain; and, for n>=8, a diagonal pair at0 and(n/2,n/2,n/2): connected at n=8 (distance4), separated at n=16 (distance8). Include S=X
only for n=4 as a zero-witness boundary case. An optional n=64 singleton
at(n/4,0,0) checks subtraction of the potentially large primitive value.

For each case construct F, the distance<=4 sample components, chi on their
radius1 neighbourhoods, G, the backward-adjoint eta, and U=U0-eta exactly
as in the proof. Use periodic indices and every component of the actual
positive-pair curl and backward divergence; no continuum surrogate.

Acceptance must independently verify:

1. mean(f)=0, each difference has magnitude4/n, and the exact norm formula.
2. F(t-1)-F(t)=f(t), including t=0 across the cyclic wrap.
3. delta(d_1*G)=0, and actual U vanishes in every component at every sample.
4. support(eta_alpha) is within N2(S_alpha), these sets are disjoint, and
   potential amplitudes are <=4s_alpha. U agrees with U0 off the union.
5. The actual Hodge energy equals the summed forward-gradient energy.
6. The displayed norm and energy bounds, with exact rational comparisons.
7. A nonzero witness is required only when its analytical norm bound is
   positive. Record the actual target-c defect, including any finite case
   that does not yet violate the target; do not tune a hidden better case.

These finite cases test the dictionary, not the universal lower bound(8).
The all-n implication is the analytical proof. Do not infer it from a fit.

Real rejecting mutations: use a forward adjoint; omit eta's component1;
make chi1 only at S rather than N1(S); omit primitive-centre subtraction
in the large-primitive case; split adjacent points into falsely separated
clusters; drop a positive plaquette pair; or use averaged rather than
counting norms in the asserted identity. Record every mutation and actual
disposition. Do not assert a mutation must fail unless its affected check
has an explicit witness among the declared cases.

No acceptance decision may use Python assert. Run normal and -O with
explicit counters, nonzero exits on failed checks, full logs, SHA256
manifests and actual one-line decimal exit sentinels. Preserve negative
results. Record runtime type/open/close/connected time and disconnect both
own allocations; no shared runtime or extra paid service/model.
