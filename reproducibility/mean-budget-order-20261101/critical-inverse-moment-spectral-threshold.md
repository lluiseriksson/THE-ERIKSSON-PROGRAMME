# The critical inverse moment suffices for actual flat spectral observations

Unit102, 2026-11-02. Base af10db0c108e216169a265b8fef13a6856d78532. This extends the analytic p>D/2 result to the critical exponent and supplies counterexamples below it. Grouped in the same mean-budget dossier; no separate paper, PDF or AIRR submission. The new arguments have not been Lean-compiled or independently reviewed.

## The actual statement and the locality distinction

Fix D>=3, Nc>=2 and c>0, and put p=D/2>1 and h=D*(Nc^2-1). Let n>=1, m>=1 and a(x)>0 be a scalar actual total coefficient, shared by all derivative directions and field components on (Z/nZ)^D. Suppose

    n^(-D) sum_x (m/a(x))^p <= M.                         (Hcrit)

There exist an ordinary real Euclidean F and an explicit linear spectral observation C such that, for every actual finite flat cochain U,

    c||U||^2 <= Q_w(U)+c||C(U)||^2,
    dim F <= C_*(D,c,Nc,M)*max(1,(n/sqrt(1+m))^D).         (Tcrit)

The original nonlinear data are C, Phi(y)=c||y||^2, K=c, with any positive configuration-space radii. They in particular hold on the actual divergence-zero subspace. The observation is a GLOBAL spectral projection constructed below; it is not claimed to be a spatially local block-mean map. 'Local' in the original nonlinear hypothesis specifies a neighbourhood of the zero field, not a spatial support requirement on C. No low-band certificate is assumed: its actual dimension is bounded in the proof.

The original subclass 1<=a<=2m with exact arithmetic mean m is included; these extra normalizations are not needed for sufficiency. The inverse-moment hypothesis itself remains additional. Q_w is identified with the actual componentwise energy sum_(x,i,j) a(x)||partial^+_i U_j(x)||^2 by the existing flat Hodge identity (formal source dfd49d0b0730a4d36f58a4cbb7a17d6a41fb60bc). No interacting/covariant replacement is made.

Moreover for EVERY fixed 0<r<D/2 the analogous uniform implication from mean((m/a)^r)<=2 is false, even with 1<=a<=2m and exact mean m. Thus D/2 is the sharp exponent for this family of global inverse-moment sufficient conditions in the scalar finite flat observation problem. This does not assert optimality for other coefficient conditions or spatially local observations.

## 1. Finite Fourier counting lemma, including normalization and kernels

Let X be a finite abelian group of size V, with counting inner product. Write F for its unitary Fourier transform, whose entries have modulus V^(-1/2). For a frequency function g let

    L=V^(-1) sup_(t>0) t^p * #{k: |g(k)|^2>t},
    I_p=(p-1)^2/[p*(p+1)],
    Gamma_p=[p/(p-1)]*I_p^(-(p-1)).

For every position function f and s>0,

    #{eigenvalues of K*K greater than s}
      <= Gamma_p*L*s^(-p)*sum_x |f(x)|^(2p),
    K=M_f F* M_g F.                                     (1)

The factor V^(-1) in L is essential. Both sides count ordinary complex multiplicities; no volume-normalized matrix trace occurs.

Here is a finite-dimensional proof, not an unproved transfer of a continuum Cwikel theorem. Phases are removed by left and right unitaries, so take f,g>=0. Set A=F* M_(g^2) F, and let A^+ be its inverse on its range and zero on its kernel. If L=0 then g=0 and (1) is immediate. Otherwise put B=p*L/(p-1). For 0<=gamma<=A set rho(x)=<delta_x,gamma delta_x>. Positivity implies gamma annihilates ker A. For E>0 let

    P_E=1_{A>0, A^+<=E},
    R_E=1_{A^+>E} on range(A).

On this range P_E+R_E=1. The Fourier diagonal and the weak-frequency tail give

    <delta_x,P_E A P_E delta_x>
      =V^(-1) sum_(g(k)^2>=1/E) g(k)^2 <= B*E^(p-1).

The same weak bound applies with >= by taking thresholds from below. To verify the tail estimate directly, for t>0 write the sum over g^2>t as t*count(g^2>t)+integral_t^infinity count(g^2>u)du; this is bounded by V*L*p/(p-1)*t^(1-p).

The vector triangle inequality applied to gamma^(1/2)delta_x, split with P_E and R_E, and gamma<=A now gives

    <delta_x,R_E gamma R_E delta_x>
      >= (sqrt(rho(x))-sqrt(B)*E^((p-1)/2))_+^2.

Spectral layer integration is exact in finite dimension:

    Tr(A^+ gamma)=integral_0^infinity Tr(R_E gamma R_E)dE
      >= I_p*B^(-1/(p-1))*sum_x rho(x)^(p/(p-1)).         (2)

The scalar integral uses the substitution E=(rho/B)^(1/(p-1))*t and integral_0^1(1-t^((p-1)/2))^2dt=I_p. Zero rho terms cause no issue.

To deduce(1), let P be the spectral projection of A^(1/2) M_(f^2) A^(1/2) onto eigenvalues>s, and let nu=rank(P). These are the squared singular values of K. If nu=0 there is nothing to show. Put gamma=A^(1/2)P A^(1/2). Then 0<=gamma<=A, Tr(A^+gamma)<=nu, and

    s*nu < Tr(f^2 gamma)=sum_x f(x)^2*rho(x)
      <= (sum_x f(x)^(2p))^(1/p)
                    *(sum_x rho(x)^(p/(p-1)))^((p-1)/p).

Inserting(2) and raising to p gives(1), since the resulting constant is B*I_p^(-(p-1))=Gamma_p*L. This explicitly handles the zero-frequency kernel instead of assuming invertibility on the full space.

Primary method context, inspected directly: Rupert L. Frank, Cwikel's theorem and the CLR inequality, arXiv:1206.3325v1, https://arxiv.org/pdf/1206.3325 , section2, Theorem2.1, Corollary2.2 and Lemmas2.4-2.5 (printed pages4-7). The density-splitting method there follows Rumin. We credit that classical argument; the finite Fourier normalization, kernel treatment and lattice/actual-cochain adapters are supplied here. We do not claim a new Cwikel mechanism or independent priority. No source prose or figures are reproduced.

## 2. Uniform actual lattice multiplier bound

For n>=2, on scalar functions let d=(partial^+_1,...,partial^+_D), L_0=d*d, and H_0 be the actual counting-mean-zero subspace. Fourier symbols are

    z_i(k)=exp(2*pi*i*k_i/n)-1,
    lambda(k)=sum_i |z_i(k)|^2=4*sum_i sin(pi*k_i/n)^2.

On k!=0 the operator d_i L_0^(-1) has symbol g_i(k)=z_i(k)/lambda(k); set g_i(0)=0 on the full space. Choose centred integer representatives r_i with |r_i|<=n/2, choosing only one representative at the even-n endpoint. Concavity of sine on [0,pi/2] gives

    lambda(k)>=16*|r|^2/n^2,
    |g_i(k)|<=lambda(k)^(-1/2)<=n/(4*|r|), k!=0.         (3)

If |g_i(k)|>tau, then 0<|r|<R=n/(4*tau). For R<=1 this set is empty. For R>1 the number of centred integer vectors is at most (2*floor(R)+1)^D<=(3R)^D. Restricting to the chosen representatives can only reduce it. Thus, with V=n^D and p=D/2,

    V^(-1) sup_(t>0) t^p*#{k: |g_i(k)|^2>t}
      <= (3/4)^D.                                     (4)

This proves the n-uniform finite weak-frequency estimate rather than importing an infinite-volume heat kernel bound. It includes even n and n=2, with the actual directed-edge convention.

## 3. Comparison with the actual weighted inverse

For one scalar coordinate set L_a=d* M_a d; a multiplies every edge by its actual start-site value. On H_0 this is positive definite, since all a>0 and the torus is connected. For f in H_0 put v=L_a^(-1)f. Every edge flow j with d*j=f has

    <f,L_a^(-1)f> <= <j,M_(a^-1)j>.

For completeness the minimizer is j_*=M_a d v. Indeed d*j_*=f, <j_*,M_(a^-1)j_*>=<f,v>, and for j=j_*+k with d*k=0 the cross term is <d v,k>=<v,d*k>=0. The difference of energies is therefore <k,M_(a^-1)k>>=0. Choose the feasible actual flow j=d L_0^(-1)f. We obtain the quadratic-form comparison on H_0

    L_a^(-1) <= sum_i T_i*T_i,
    T_i=M_(a^-1/2) d_i L_0^(-1).                       (5)

Each T_i is defined on the full scalar space with its zero-frequency value set to0. From(1),(4), for every s>0,

    n(s,T_i*T_i)<=Gamma_p*(3/4)^D*s^(-p)*sum_x a(x)^(-p).

The number of eigenvalues of a sum of D nonnegative matrices greater than t is at most the sum of their individual counts above t/D. To see this without a commutativity assumption, intersect the complements of their high spectral subspaces. The codimension is at most the sum of their ranks, and on that intersection the sum's quadratic form is <=t times the norm squared. The finite-dimensional min-max principle gives the claim.

Apply it at t=1/c, together with(5). Inversion on H_0 reverses eigenvalue order and the scalar constant mode contributes exactly one zero eigenvalue. Therefore the ACTUAL scalar low-eigenvalue count is

    number of eigenvalues of L_a in [0,c)
      <= 1+Gamma_p*(3/4)^D*D^(p+1)*c^p*sum_x a(x)^(-p)
      <= 1+Gamma_p*(3/4)^D*D^(p+1)*c^p*M*n^D/m^p.       (6)

Only positivity, actual incidence operators, an explicit feasible flow, proved Fourier counting and min-max were used. There is no assumed estimate for L_a or spectral-band dimension.

## 4. Actual real nonlinear data and dimension

Because L_a is a real symmetric matrix, choose a real orthonormal eigenbasis in the counting norm. Let C retain the actual coefficients in all its scalar eigenvectors with eigenvalue<c, separately for each actual real adjoint coordinate and field component. Complexification of a real symmetric matrix preserves each eigenvalue's multiplicity: it does not double the real dimension. Thus dim F equals h times the count in(6).

For eigenvalues>=c, energy already dominates c times squared coefficient. For eigenvalues<c, the additional c||C(U)||^2 does so. Summing proves(Tcrit) for every cochain. C is linear, C(0)=0, and Phi(y)=c||y||^2 supplies the original local penalty with K=c, without a supplied abstract observation witness.

Since p=D/2 and m>=1, (1+m)/m<=2. One safe constant is

    C_*=h*[1+Gamma_p*(3/4)^D*D^(p+1)*c^p*M*2^p].        (7)

For n=1 take C to be the identity on all h coordinates; its dimension is h and(7) still works. This completes the analytic sufficiency proof at the critical exponent. Higher moments imply(Hcrit) by normalized Holder, but unit101 also retains its different, constructive block-mean observation.

## 5. Every lower positive inverse exponent is insufficient

Fix 0<r<D/2 and the same D,Nc,c. Reuse the explicitly proved actual compact curls from global-reciprocal-mean-trap-refutation.md (unit100): choose a fixed integer ell>3D/c, P=2ell+2 and B=(2ell+1)^D. Each curl is exactly divergence zero, has forward-gradient start support in its own B-site weak box, and has exact Rayleigh quotient

    lambda_ell=3/ell+6*(D-1)/(2ell^2+1)<=3D/ell<c.

The source note derives these actual directed-difference identities and the disjoint support construction; no arbitrary abstract slow subspace is introduced here. Along sufficiently large n divisible by P set

    m=n^2, J=floor(n^(D-2r)/B), s=B*J/n^D.

Because D-2r>0, J>=n^(D-2r)/(2B) tends to infinity. Also J<=(n/P)^D eventually: the needed inequality P^D<=B*n^(2r) holds for sufficiently large n since r>0. Choose J separated boxes. Set a=1 on their union and a=A=(m-s)/(1-s) elsewhere. Then s<=n^(-2r)=m^(-r), eventually s<=1/2, and exactly

    mean(a)=m, 1<=a<=2m, A>=m,
    mean((m/a)^r)=s*m^r+(1-s)*(m/A)^r<=2.               (8)

Every real combination of the J actual disjoint curls still has Q_w=lambda_ell*||U||^2, by disjoint field and gradient supports. The original nonlinear coercivity data force dim F>=J: if the actual derivative DC(0) has a nonzero kernel vector U in this J-dimensional subspace, then C(tU)=o(t), its locally quadratically bounded penalty is o(t^2), and division of the claimed inequality by t^2 followed by t->0 contradicts lambda_ell<c. This uses the original differentiability and C(0)=0 assumptions, not a rank certificate.

At m=n^2 the proposed max(1,(n/sqrt(1+m))^D) equals1, while J diverges. Thus(8) refutes the uniform claim for every r<D/2. It extends unit100, which was the special r=1. The present sharp exponent statement combines a separately proved endpoint implication and an actual counterexample family; it is not inferred from failure of the adaptive tree count.

## Scope, one next question, and retained work

This removes the strict exponent margin p>D/2 from the sufficient global-observation theorem: p=D/2 is enough. It does not remove the critical distribution condition, prove it from arithmetic means, or verify a physical interacting/continuum mass gap. Finite scalar coefficients and actual flat componentwise energy remain essential to the stated proof. PR29 remains20/41, TermSource=0.

ONE next active bounded question: under(Hcrit) and the original scalar exact-mean class, can the same rank order be realized by normalized means on a partition into axis-aligned integer rectangles, instead of the global spectral projection? Mechanism: a critical-scale covering/partition argument that avoids overcounting nested bad boxes. Falsifier: actual coefficient profiles satisfying(Hcrit) for which every such coercive block-mean partition needs unboundedly more boxes than max(1,(n/sqrt(1+m))^D). Stop/change route after three substantive units without a proved reduction or useful falsifier, preserving the concrete obstruction. This is a spatial-locality strengthening, distinct from the now answered original spectral-existence question. Formalizing the endpoint proof and consolidating the dossier are preservation tasks, not additional active new questions.

## Model assessments and review context

FIRST exact-note self-assessment6/10 by the preparing Codex agent. Actual served backend identity and effort are unexposed. No independent review, human peer review, editorial acceptance or PDF assessment. Rubric0-10: analytic derivation7, originality3, dossier relevance8, verification maturity3; overall6 is a qualitative judgement, not a calibrated probability or arithmetic average. No score inherited from unit101, other sources or PDFs; no repeated review to improve a grade.

Exact-note audit: normalized unitary entries and V^-1; phases, zero-frequency kernel and pseudoinverse support; weak tail with >= thresholds; projection triangle inequality; layer integral and I_p; positive spectral projection and Holder exponents; actual sine constant16 and centred even representatives; noncommuting sum min-max; correct direction of feasible-flow inverse comparison; strict low threshold and constant mode; actual real dimension h; factor2^p in(7); n=1; arbitrary lower r packing, s<=1/2, exact arithmetic/critical-moment distinctions; derivative-kernel contradiction on actual curls. No numerical fixture, new Lean run, oracle, Colab runtime or terminal reproduction occurred in this analytic unit.

O1. All new finite Fourier, inverse, counting, field and endpoint adapters are analytic, not Lean-verified; operational CI on an unchanged Lean tree does not verify them.

O2. The density method is classical Cwikel/Rumin/Frank. Independent novelty and complete priority comparison for this particular finite adapter are unestablished; no standalone small paper is warranted.

O3. Observations at the endpoint are global spectral coordinates. The prior logarithmic limitation for block means is not resolved by calling this projection local.

O4. The proof treats one scalar profile shared by all directions/components. Matrix-valued, anisotropic, interacting and continuum transfers need their own arguments.

O5. The distribution assumption remains substantive. The sharp exponent refers only to the stated family of global inverse-moment conditions and fixed uniform rank order.

O6. Constants are safe, not optimized. Finite diagnostics and terminal reproductions remain absent; source self-assessment supplies no independent validation or exact-PDF evaluation.

O7. No physical mass gap, new paper/deposit, AIRR acceptance or publication is claimed. Existing scores, frozen PDFs, permissions and negative results remain attached to their own exact versions.
