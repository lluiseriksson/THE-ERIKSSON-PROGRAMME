# Componentwise derivative repairs: a global identity and the coefficient frontier

Research note with a checked formal core, 30 October 2026. This is not a new paper or part of the frozen PDFb37f. The actual componentwise operator, global all-cochain Hodge quadratic identity and weighted comparison are now proved in Lean at dfd49d0b0730a4d36f58a4cbb7a17d6a41fb60bc, with two complete fresh Colab reproductions. The growing-envelope obstruction and matching quadratic escape below remain analytic. Original convention anchor: a9937ee1dd5978bf372174500a2395cf259eb395.

## Concrete operator and actual conventions

Let d>=1, n>=1, Nc>=2, m=Nc²-1 and X=(Z/nZ)^d. Use E=(R^m)^(X×{1,...,d}) with the physical counting inner product. For scalar/vector site fields put T_i f(x)=f(x+e_i), D_i=T_i-I and B_i=I-T_i^(-1). These are explicitly finite permutation matrices and differences, not supplied comparison maps. Translation is orthogonal, so D_i*=-B_i, B_i*=-D_i, and every T_i and T_j^(±1) commute.

For A in E define the actual stacked derivative map

    (G A)(i,x,j)=A_j(x+e_i)-A_j(x).

Its codomain is the counting Hilbert space on (i,x,j). It is a concrete real-linear continuous map, with ||GA||²<=4d||A||² by ||T_i-I||<=2. For arbitrary real finite weights w(i,x,j), let W be the diagonal matrix with those entries and set V_w=G*WG. This constructs the repair on E rather than postulating its quadratic form or a low-band inequality. Direct adjunction gives

    <A,V_w A>=sum_(i,x,j) w(i,x,j)||A_j(x+e_i)-A_j(x)||².       (1)

It is symmetric; it is nonnegative if w>=0. Finite-dimensional continuity needs no uniform coefficient hypothesis. If 0<=w<=M, its operator norm is at most4dM. For the energy upper bound below only w<=M is needed.

The repository's trivial-background curl is D_i A_j-D_j A_i on each unordered pair i<j, counted once (PhysicalGaugeCochains.covariantD1CLM_trivial_apply). Its constraint is sum_i B_i A_i (gaugeConstraintQCLM_trivial_apply). The checked Hodge quadratic identity is the sum of their squared norms (flatGaugeHodgeK0_inner_right). These conventions are read at the pinned source, not assumed to match a Wilson Hessian.

## Derived global flat Hodge identity

For each unordered i<j, using the actual finite adjoints and commuting shifts,

    <D_i A_j,D_j A_i>
      =<A_j,D_i* D_j A_i>
      =<A_j,D_j D_i* A_i>
      =<D_j* A_j,D_i* A_i>
      =<B_j A_j,B_i A_i>
      =<B_i A_i,B_j A_j>.                                  (2)

The inner products in (2) sum over every site and internal coordinate. Also ||B_i f||=||D_i f|| because B_i=T_i^(-1)D_i. Expanding both squared terms yields

    sum_(i<j)||D_i A_j-D_j A_i||² + ||sum_i B_i A_i||²
      =sum_(i!=j)||D_i A_j||² +sum_i||B_i A_i||²
       -2 sum_(i<j)<D_i A_j,D_j A_i>
       +2 sum_(i<j)<B_i A_i,B_j A_j>
      =sum_(i,j)||D_i A_j||²
      =||GA||².                                             (3)

Thus, for every physical one-cochain, not just one-component Fourier witnesses,

    <A,K0 A>=||GA||².                                       (4)

Since both K0 and G*G are symmetric, polarization also gives K0=G*G as operators in this finite real Hilbert model. No operator equality is inferred from a single test vector: (4) holds for every A and is now checked by componentwiseFlatGradient_eq_hodge. The operator equality by polarization is analytic here; no separate Lean operator-equality endpoint is claimed.

Equations(1)-(4) give the constructed-family comparison

    w<=M  ==>  <A,V_w A><=M<A,K0 A> for every A.              (5)

Unit weights give equality of forms and operators. The componentwise family is constructed explicitly, with the comparison (5) checked by componentwiseWeightedRepair_le_hodge. It is distinct from the weighted curl/divergence family of PR98. The global cross-term cancellation and actual unordered-plaquette transport have been proved, without introducing a structure assuming the desired identity or bound.

## Obstruction with growing, even subquadratic, coefficient envelopes

Fix finite real F of dimension h. Let n_L=(L+1)Nprime for a fixed positive integer Nprime. At every L allow an arbitrary real-linear C_L:E_L->F and an arbitrary finite-valued Phi_L:F->R with Phi_L(0)=0. Let w_L<=M_L pointwise, with M_L>=0. No rank bound, translation invariance or smoothness of the weights is required.

Use the already constructed actual physical band S_R of real dimension2(2R+1)^d and K0 energy <=a_R/n_L² times norm², a_R=4*pi²*d*R², when2R<n_L. Choose one integer R with2(2R+1)^d>h, for example R=h+1. Rank-nullity for C_L restricted to S_R supplies a nonzero A_L with C_L A_L=0. From(5),

    <A_L,(K0+V_wL)A_L> +Phi_L(C_L A_L)
       <= (1+M_L)*a_R/n_L² *||A_L||².                      (6)

Therefore a full-space bound c||A||²<=energy for every L,A, with one fixed c>0, NECESSARILY forces

    (1+M_L)/n_L² >= c/a_R

at every L large enough for2R<n_L. In particular any subsequence L_k->infinity with (1+M_Lk)/n_Lk²->0 refutes the uniform bound. This includes M_L=o(n_L²), and is weaker than imposing a uniform coefficient bound. The hypothesis has been weakened by a proved comparison and explicit witness argument, not moved into a new structure. This is analytic, not a new verified Lean result or a statement about arbitrary nonderivative repairs.

An upper envelope deliberately inflated to order n² satisfies this necessary condition without proving anything about the actual weights. For content one can take M_L=max(0,max w_L). Quadratic envelope growth is necessary in this sense; it is not sufficient for every variable weight field or every coarse measurement.

## Sharpness of the order and the role of the coarse mean

The componentwise construction also supplies an escape exactly at quadratic order. Define

    (C_n A)_j=n^(-d/2) sum_x A_j(x),

in the fixed real space F=(R^m)^d, dimension dm independent of n. If P0 is the orthogonal projection onto direction-wise constants, then ||C_n A||²=||P0 A||². Its penalty is Phi(y)=||y||².

For n>=2, direct finite Fourier synthesis diagonalizes (4). The character at k has eigenvalue

    lambda(k)=sum_i |exp(2*pi*i*k_i/n)-1|²
             =4 sum_i sin²(pi*k_i/n).

All nonconstant modes satisfy lambda(k)>=4sin²(pi/n)>=16/n². To see the second bound, use sin(t)>=2t/pi for0<=t<=pi/2 at t=pi/n. Thus K0 >=(16/n²)(I-P0) as quadratic forms. For constant weights w=n²/16, the explicitly constructed repair is V_w=(n²/16)K0, and

    <A,(K0+V_w)A>+||C_n A||²
       >= ||(I-P0)A||²+||P0 A||²
       =||A||².                                            (7)

For n=1 all fields are direction-wise constant, C_1 is the identity on E and(7) remains true, without invoking a nonexistent positive eigenvalue. Consequently the subquadratic obstruction cannot be extended to all quadratic derivative weights. This is a concrete uniformly coercive counterexample to that overextension, with a fixed-dimensional LINEAR measurement and a derivative repair, not a zero-order identity repair.

The n=2 normalization deserves an explicit check: a one-dimensional cycle profile (a,b) has derivative energy2||a-b||² and the antisymmetric mode has Rayleigh quotient4. Our positive-bond convention counts both periodic forward differences. Treating it as a simple single-edge graph would introduce an incorrect factor two. The Fourier formula above follows directly from our derivative, so it includes this case correctly.

A second symbolic check of the cross terms: for d=2,n=2, A_1=p*(-1)^(x1+x2) and A_2=q*(-1)^(x1+x2), curl and divergence energies sum to16[(p-q)²+(p+q)²]=32(p²+q²), exactly the stacked derivative energy. This hand expansion tests the cancellation signs; it is not a numerical oracle run.

The quadratic escape is consistent with the already recorded physical-spacing companion: a refinement-squared derivative strength changes the operator. Equation(7) does not supply a positive unscaled pure-K0 gap, an interacting precision estimate, hRpoly, a continuum limit or a Yang-Mills mass gap. PR29 remains20/41 and TermSource=0.

## Classical background, originality and review limits

Primary source read: Daniel A. Spielman, Spectral Graph Theory Lecture3, 5September2018, https://cs.yale.edu/homes/spielman/561/lect03-18.pdf. Section3.2 gives weighted difference quadratic forms; Theorem3.5.2 gives additive product spectra; Lemma3.7.1 gives the cycle spectrum. These support the classical mechanisms. The final line of the displayed cycle computation appears to omit a factor2; the lemma statement and its preceding algebra give2-2cos, and we independently derived our multiplier above. Our n=2 convention is stated separately.

The earlier bull1557.pdf lookup timed out and the2012 lecture lookup was unavailable through the web tool. Neither failure is evidence of absence or novelty. No exhaustive priority search was performed. Weighted derivative comparisons and Fourier scaling are classical; the programme value is closing the specific componentwise construction and its normalization/cross-term obligations, with the exact subquadratic frontier and a matching escape recorded together. Do not turn this into a separate small paper or add it silently to an assessed PDF.

Prepared and analytically checked by the same Codex agent with programme context, not blind or organizationally independent. No new alternate-model review, score, peer review, acceptance or publication. No Windows Lean/Lake, numeric oracle or sustained local computation was executed.

## Formal core and reproduction boundary

ComponentwiseFlatGradient constructs G and V_w and proves (1), periodic summation by parts, commuting-shift cross cancellation and the upper bound against gradient energy. ComponentwiseFlatHodge proves matrix_sum_eq_diag_add_orderedPairs, finite_flat_curl_div_energy, componentwiseFlatGradient_eq_hodge and componentwiseWeightedRepair_le_hodge. The actual plaquette equivalence counts each unordered pair once; there is no curl-zero or mean-zero assumption. Thus the previously active formalization obligation (2)-(5) is closed.

Runs040/040b are complete fresh dedicated CPU/high-RAM Colab Linux clones at source dfd49d0b0730a4d36f58a4cbb7a17d6a41fb60bc. Each recovered package has12 checked manifest entries,2 pinned sources,9 exit-zero steps,4 exact-name axiom reports (only propext,Classical.choice,Quot.sound), and three actual-evidence mutations rejected in each of normal/optimized Python. The .olean, oracle and source-manifest hashes match. All runtimes were released; this is focal reproduction, not independent scientific review or repository-wide terminal closure. Full hashes and pinned drivers are in reproducibility/component-gradient-20261030/global-hodge-reproduction.json. Failure039 is preserved: inner-product ordering, over-recursive square expansion and two redundant closing tactics were repaired without changing oracle statements.

The asymptotic coefficient frontier, Fourier sharpness example, operator norm estimates and operator equality by polarization remain analytic claims in this note. None is silently promoted by the checked quadratic-form endpoints. This closes a concrete finite-flat proof obligation; it supplies no Wilson Hessian, hRpoly producer or physical continuum result. No assessment of the frozen PDF is inherited.
