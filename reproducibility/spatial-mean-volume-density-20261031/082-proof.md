# Volume-order output rank from actual spatial mean bounds

Analytic theorem and proof, 31 October 2026. This is a continuation of the existing coarse-information dossier, not a separate paper or a Lean-verified endpoint. Side length is n here (the code's positive side parameter is sometimes k+1).

## Statement

Fix integers d>=2, Nc>=2 and let m=Nc^2-1. Put X=(Z/nZ)^d, V=n^d, and let E be the actual real one-cochain space with m internal coordinates and counting Euclidean norm. Let D=ker(delta), using the actual flat backward divergence. For every forward-gradient direction i and field component l let w(i,x,l)>=0, with spatial mean b(i,l)=V^-1 sum_x w(i,x,l)<=M, where M>=0 is fixed independently of n. This includes diagonal pairs i=l: the packet has nonzero diagonal gradients. No weakening to off-diagonal means alone is proved.

Let Q(A)=<A,K0 A>+sum_(i,x,l) w(i,x,l)||A_l(x+e_i)-A_l(x)||^2. This is the actual flat Hodge form plus actual componentwise repair, not a supplied band or order certificate. Let F be any finite-dimensional real normed output space, C:E->F differentiable at zero with C(0)=0 and derivative L. Suppose Phi(y)<=K||y||^2 for ||y||<delta0, where delta0>0 and K is finite. Suppose for some r>0 and c>0,

    c||A||^2 <= Q(A)+Phi(C(A))  (A in D, ||A||<r).

For every integer R>=1 with 2R<n put H=2R(2R+1)^(d-1) and B=4*pi^2*d*R^2/n^2. Then

    dim_R(F) >= H * (1-(1+M)*B/c).                     (T)

In particular define

    alpha = min(1/4, sqrt(c/(8*pi^2*d*(1+M)))),
    rho = alpha^d/2 > 0.

For every integer n>=2/alpha, choose R=floor(alpha*n). Then the same hypotheses force

    dim_R(F) >= rho*n^d.                              (D)

For families, only d,Nc,M,c are fixed. C,L,F,Phi,K,delta0,r and the nonnegative weights may all vary with n. No uniform bound on the observation norm, derivative remainder, K, inverse radius or inverse penalty neighbourhood is required. There is no pointwise upper cap on w. No continuum, interacting or physical mass-gap conclusion follows.

## 1. An actual normalized coexact packet

Use two orthonormal internal coordinates to identify C with a real internal plane by J(z)=(Re z,Im z,0,...,0). It is a real isometry; it is not identification with a scalar real field. Select the frequency set

    P={k: k_1 in {1,...,R}, k_j in {-R,...,R} for j>=2}.

It has N=R(2R+1)^(d-1) elements. Because 2R<n, distinct vectors in this set remain distinct modulo n: every coordinate difference has absolute value at most 2R<n. Define chi_k(x)=exp(2*pi*i*k.x/n), forward symbols s_j=exp(2*pi*i*k_j/n)-1 and backward symbols t_j=1-exp(-2*pi*i*k_j/n). As 1<=k_1<=R<n, t_1!=0. Thus h_k=sqrt(|t_1|^2+|t_2|^2)>0. Put

    p_1(k)=t_2/h_k, p_2(k)=-t_1/h_k, p_l(k)=0 (l>2),
    U_k,l(x)=V^-1/2 p_l(k) chi_k(x).

Their squared component amplitudes sum to one. Actual backward differences give

    delta U_k = V^-1/2 chi_k * (t_1*p_1+t_2*p_2) = 0.

These are images of the actual two-component backward-difference map: apply it to chi_k/(sqrt(V)*h_k). The normalized packet does not assume that a supplied subspace is coexact. For each k use the two real fields J(U_k) and J(i U_k), componentwise. They lie in D.

The finite root-of-unity identity follows coordinatewise from the geometric sum: sum_x conjugate(chi_k(x))*chi_h(x)=V if k=h and zero otherwise. Consequently the complex vector-valued inner product of U_k and U_h is delta_(kh); taking real parts yields unit norms and zero inner products for all the 2N real fields, including the same-frequency quadratures since Re(i)=0. No conjugate-pair restriction or missing factor of two is allowed: the two internal coordinates store an unrestricted complex amplitude, even if conjugate frequencies were present. Hence their real span S is an actual H-dimensional subspace of D, H=2N.

## 2. Actual weighted diagonal and trace

Forward differencing multiplies each mode by s_i. For either real quadrature and every x,i,l the actual squared gradient is

    ||G_(i,x,l) J(U_k)||^2 = V^-1 |s_i|^2 |p_l|^2.

The Hodge identity on the actual whole cochain space gives <A,K0 A>=sum_(i,x,l)||G_(i,x,l)A||^2. Thus the diagonal Q-value of either quadrature is exactly

    lambda(k) + sum_(i,l) |s_i|^2 |p_l|^2 b(i,l),
    lambda(k)=sum_i |s_i|^2.

Summing over this derived orthonormal basis proves the actual compression-trace identity

    tr_S Q = 2 sum_(k in P) [lambda(k)+sum_(i,l)|s_i|^2 |p_l|^2 b(i,l)].  (E)

No invariance of S under the weighted repair, pointwise weight cap or frame-isotropy hypothesis is used. From the actual means and sum_l|p_l|^2=1 the bracket is <=(1+M)lambda(k). Also |exp(it)-1|<=|t| and |k_i|<=R, so lambda(k)<=B. Hence tr_S Q<=H(1+M)B. Nonnegativity of actual weights implies Q>=0 on E; this positivity is needed in the next step.

## 3. Local nonlinear observations and the rank step

For v in D intersect ker L, differentiability gives C(tv)=o(t). For all sufficiently small nonzero real t, the original local estimate and the local penalty bound apply. Homogeneity of the actual quadratic Q gives

    c||v||^2 <= Q(v)+K ||C(tv)||^2/t^2.

The final term tends to zero, so c||v||^2<=Q(v). This uses no uniform-in-n neighbourhood or remainder.

Let f=dim_R F and U=S intersect ker L. Rank-nullity gives dim U>=H-f. Choose an orthonormal basis of U and extend it to one of S. The first diagonal terms are at least c; all the complementary terms are nonnegative because Q>=0. Therefore

    c(H-f) <= c dim U <= tr_S Q <= H(1+M)B.

Rearrangement gives (T). This trace/rank argument remains valid if H-f is negative; no hidden assumption f<H is made.

## 4. Explicit positive density on every sufficiently large side

Alpha is positive and <=1/4. For n>=2/alpha, R=floor(alpha*n)>=alpha*n-1>=alpha*n/2>=1, and 2R<=2alpha*n<=n/2<n. The definition of alpha gives (1+M)B<=4*pi^2*d*(1+M)*alpha^2<=c/2. Thus (T) yields f>=H/2=N. Moreover 2R+1>=alpha*n, so

    N=R(2R+1)^(d-1) >= (alpha*n/2)*(alpha*n)^(d-1)=rho*n^d.

This proves (D) for all large integer n, not only a specially dilated subsequence. The constants are explicit and deliberately nonoptimal.

## Scope, originality and falsifiers

Compared with the existing pointwise-capped density result, the analytic density conclusion here uses actual nonnegative spatial means; no pointwise cap is proved or assumed. Positivity of weights, local differentiability, C(0)=0, local quadratic upper control and fixed positive c remain. This is a genuine analytic change in sufficient hypotheses, not discharge of a physical Yang-Mills assumption. Signed means alone cannot replace the nonnegative mean condition, as the existing fixed-output counterexample shows.

The proof uses classical Fourier, finite-dimensional trace and rank-nullity mechanisms. Exact originality of the combined mean-weight coexact statement is not established; do not publish this as a new general spectral principle or separate corollary paper. Spielman's author-hosted Spectral Graph Theory chapter, sections16.3.2,16.4 and16.5, provides primary background for Laplacian forms, cycle Fourier modes and Courant-Fischer reasoning: https://www.cs.yale.edu/homes/spielman/PAPERS/SGTChapter.pdf . It does not itself state the present local nonlinear mean-weight conclusion. Ky Fan1949 is a related original variational-trace reference (bibliographic record verified at https://pmc.ncbi.nlm.nih.gov/articles/PMC1063101/); its scanned full theorem was not successfully read in this unit, so no exact theorem equivalence or novelty refutation is attributed to it.

Falsifiers actively checked in the written derivation: backward rather than forward divergence symbols; nonzero normalization at every selected frequency; injective residue indexing; both real quadratures; exact V cancellation against the spatial mean; use of Q>=0 in the complementary trace; a floor cutoff valid for every sufficiently large n. Dropping positivity breaks the trace argument. Finite floating-point checks can detect implementation errors but cannot prove these universal statements. No Lean endpoint or independent scientific review is claimed for this note.
