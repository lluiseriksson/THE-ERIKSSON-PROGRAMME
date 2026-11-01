# Guard: the constant rank floor does not survive removing the harmonic sector

Analytic negative boundary, not a refutation of the stated full-domain result. No Lean endpoint or PDF change.

For n>=2 let the admissible domain be actual divergence-free cochains whose mean in every field/internal coordinate is zero. This is a strictly smaller domain than the original actual divergence-free space, which contains the constant h-dimensional sector.

On this mean-zero domain every scalar Fourier coefficient at frequency0 vanishes. Direct actual cyclic forward-difference diagonalization gives lambda(k)=4 sum_i sin^2(pi*k_i/n). Every remaining frequency has lambda(k)>=lambda1(n)=4sin^2(pi/n)>0. Thus actual flat energy K0 is at leastlambda1 times the counting norm squared on that domain.

Choose m_n=c/lambda1(n), actual constant weightsw=m_n-1, C=0 into the0-dimensional real space and Phi=0. The actual total-stiffness identity gives Q_w=m_n*K0, so c||A||^2<=Q_w(A) globally on the smaller domain. C(0)=0, DC(0)=0 and any positive local radii/penalty neighbourhoods hold withK=0. The required positiveTOTAL means are exactlym_n. Yet q=0 while max(1,n^D/(1+m_n)^(D/2))>=1 for every n. Hence the positive constant rank floor and its exact order statement cannot be transferred unchanged to this mean-zero/quotient setting. The violated original hypothesis is the FULL divergence-free domain; no weakening ofc>0 or mean conventions is involved.

The same example does not contradict the original full-domain theorem: nonzero constants have zero energy and no observation/penalty, so they immediately violate its local coercivity hypothesis. It explains why the actual constant-sector injection is useful but must not be presented as a physical quotient-space mass-gap argument. The construction and spectral mechanism are classical; no new general principle or independent review is claimed. PR29 stays20/41 and TermSource=0. Primary spectral background is the separately checked Lin/Wan/Zhang arxiv2403.06105v1 Theorem1.2; the cyclic-difference normalization here is derived directly as in unit080.
