# Two-component band: dimension, energy and an extensive observation budget

Preparing-agent analytic derivation, not independent scientific review. The current CoexactFlatBand Lean module addresses construction, injection, dimension and actual flat divergence only. The energy transport and capacity conclusions below are not claimed as its Lean endpoints.

Let spatial dimension D=d+2>=2, Nc>=2, n>2R. Take the actual centered scalar characters whose first centered frequency is a+1 for a inFinR and whose otherD-1 centered labels are unrestricted. Distinct labels give independent actual characters without modular aliasing. The scalar span has complex dimensionR(2R+1)^(D-1) and twice that real dimension. Map each scalar potential f to the actual physical field

 A_0=EmbedInternal(Delta^-_1 f), A_1=-EmbedInternal(Delta^-_0 f), A_j=0 for j>=2,

where EmbedInternal places real and imaginary parts in two distinct real SUN coordinates and Delta^-_i f(x)=f(x)-f(x-e_i). The actual flat gauge divergence is the sum of the backward differences of the corresponding bond components. Commuting shifts give Delta^-_0 Delta^-_1 f-Delta^-_1 Delta^-_0 f=0, so every constructed field lies in its actual kernel. This does not assume an annihilated comparison subspace.

If the physical field is zero, evaluate its second bond component. The proved physical embedding norm identity gives Delta^-_0 f=0. It follows that the first forward difference of f is zero too. Its actual Fourier coefficient at each selected frequency is multiplied by chi_k(e_0)-1. The first residue is a+1, with0<a+1<=R<n, so injectivity of the actual standard additive character shows this multiplier is nonzero. Character independence forces every coefficient to vanish. Thus the physical map is injective and its real image dimension is

 B_D(R)=2R(2R+1)^(D-1).

This is a deliberately smaller positive-first-frequency subfamily of the initially proposed first-two-nonzero family. The larger formula2*((2R+1)^D-(2R+1)^(D-2)) remains neither proved nor refuted here. The positive subfamily already has full degreeD inR, whereas the prior one-bond construction had degreeD-1. No optimal leading constant is claimed. The factor2 is the actual internal two-real-coordinate embedding, not a duplicate count of real scalar characters.

## Actual Hodge-energy transport — analytic, pending new Lean endpoint

Each backward difference of f remains in the actual full centered scalar span, since it multiplies each character coefficient by its actual shift multiplier. Write g_0=Delta^-_1 f and g_1=-Delta^-_0 f. Their embeddings occupy different bond components, so the actual physical counting-L2 norm satisfies

 ||A||²=countingL2Mass(g_0)+countingL2Mass(g_1).

Use the already proved actual global identity componentwiseFlatGradient_eq_hodge and its finite-sum formula componentwiseFlatGradient_energy, rather than adding two quadratic Hodge inequalities and dropping unknown cross terms. The gradient sum splits by bond component. Internal embedding preserves each scalar difference norm. Hence the actual flat Hodge energy of A equals the sum, over all directions, of the forward-shift energies of g_0 and g_1. The actual scalar Parseval/multiplier bound gives

 q_n(A)<=b_D(R,n)||A||², b_D(R,n)=4*pi²*D*R²/n².

For the actual constructed componentwise weighted derivative repair withw<=M,M>=0, the already proved global comparison componentwiseWeightedRepair_le_hodge gives total quadratic energy at most(1+M)b_D(R,n)||A||² on this image. The missing new Lean work is to transport the scalar difference/span and the two-component norm/gradient split explicitly. That work is not replaced by a supplied comparison field.

## Local observation obstruction — analytic, pending formal transport

Let C:E_n→F_n be differentiable at0 withC(0)=0, F_n a finite-dimensional real normed space of dimensionm_n. Suppose Phi_n(y)<=K_n||y||² near0 in a positive neighborhood. If m_n<B_D(R), rank-nullity on the actual derivative restricted to the derived physical band yields a nonzero v withDC(0)v=0. Its entire ray lies in the actual linear divergence-zero sector. Along that ray, differentiability makes the observation/norm ratio tend to0, while the actual energy band bound applies at every scale. Thus any local lower bound with coefficient

 c>(1+M)b_D(R,n)

is impossible on every positive-radius ball in that sector. This is the same established tangent mechanism applied to the new actual band once its energy transport is proved. No uniform derivative bound, uniform K_n or lower bound on the positive ball/neighborhood radii is needed across n.

## Explicit extensive budget consequence — analytic, not a Lean claim

Fix D>=2, M>=0 and c>0. Choose a constant alpha with

 0<alpha<min(1/2,sqrt(c/((1+M)*4*pi²*D))).

For sufficiently large integers n letR_n=floor(alpha*n). ThenR_n>=alpha*n/2>=1,2R_n<n and(1+M)b_D(R_n,n)<c. If the proposed local lower bound with coefficientc holds on the actual divergence-zero sector, the finite obstruction forces

 m_n>=B_D(R_n)=2R_n(2R_n+1)^(D-1)>=(2R_n)^D>=(alpha*n)^D.

Consequently m_n/n^D>=alpha^D for every sufficiently large n admitting that bound. In particular, output dimensions m_n=o(n^D) cannot support a common positive local coercivity coefficient, even with arbitrary n-dependent differentiable observations, n-dependent local upper-quadratic penalty constants and arbitrarily shrinking positive local balls. This is a necessary observation-dimension condition, not a sufficiency or spectral theorem. It retains a uniform upper weight bound M and flat unit spacing.

At fixed physical size with spacing1/n, multiplying the operator byn² removes the decaying energy scale used here, so the argument does not produce this growing-volume budget claim for a physical continuum limit. Interacting backgrounds need not have commuting shifts. No physical mass gap, Wilson/hRpoly producer or continuum result is established. PR29 remains20/41,TermSource=0. The coexact mechanism is classical (Sushch equations2.16–2.18); no originality priority or separate paper is claimed.
