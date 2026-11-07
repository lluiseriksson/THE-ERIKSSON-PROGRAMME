# Offline replay specification for unit175

Hash context: analytical note based on main
88f31a1981b757b9240a9076e2012545066b9028. No computation has been executed
for this specification. It is not a PASS, independent proof or necessary
substitute for reading the universal proof.

If a replay is useful during later grouped consolidation, run it in an
own CPU Colab Linux runtime, with two fresh clones at the same eventual
recipe SHA, and disconnect/export immediately on completion. Do not run
it on Windows. No GPU, new package, paid model or API is needed.

Use Python's Fraction with c=1,a=1/2,b=2. Index the eight vertices of
(Z/2Z)^3. Construct all27 nonempty geometric rectangles (each coordinate
is {0},{1} or {0,1}). Generate disjoint covers uniquely by choosing the
lexicographically first uncovered point and branching over rectangles
containing it; deduplicate final sorted rectangle tuples defensively.

For each cover with q<8, construct exact rational matrices

    P=sum_R 1_R 1_R^T / |R|,
    E=11^T/8, V=sigma sigma^T/8,
    L=2(I-E)-(3/2)V.

Check P^2=P=P^T, P1=1, L1=0, Lsigma=sigma/2, and every off-diagonal
weight is either1/16 or7/16. On u=sigma-Psigma, if u!=0, verify directly

    t=sigma^T P sigma/8,
    u^T L u / (u^T u)=1/2+(3/2)t,
    t<=q/8.

For all covers with q<=2, require u!=0 and quotient<=7/8<1. Also
include a four-vertex 1D cyclic interval case to exercise wrapped
intervals, and whole-space/singleton boundary cases. Add the 1D length16
partition with six consecutive singleton cells and the remaining
length10 interval. Require t=3/8 and positive semidefiniteness on H
of L+8P-I, with a zero direction; reject the false necessity q>=N/2
using this successful q=7 case. For a PSD check, use exact rational
elimination with proper zero-pivot compatibility, not rounded eigenvalues.
The finite cases
illustrate, but do not prove, the all-n rectangular theorem.

Required rejecting mutations: wrong sign for V; omit E; incorrectly
normalize P by |R|^2; omit a covering cell; duplicate/overlap a cell;
declare a zero u a nonzero witness; change the predicted threshold to
q>=N/2 or permit a finite K at t=1/3. Include the exact mutation
disposition and acceptance counter.
Never use Python assert to decide acceptance, in normal or -O mode.

Capture actual process exits after termination, exact one-line decimal
sentinels, complete logs and SHA256 manifests. Record runtime type,
opening/closing and connected time. Do not label files independent model
assessments or claim formal verification from rational examples.
