# Actual physical quadratic mean construction — unit046

Verified source 7f37d6437a8f69a1d3fddf3dc0bcfad74c6bf9b6. Fresh Colab clones067/067b passed with matching compiled, raw-oracle and source-manifest hashes. Full reports in paired-validation.json are the proof/reproduction witnesses; this explanatory note is not an independent review.

For fixed D>0 and Nc>0, let A range over the actual PhysicalGaugeOneCochain D n Nc, n>0. Observe its directional arithmetic mean mu_j = n^(-D) sum_x A(x,j) in the fixed type PiLp 2 (fun j : Fin D => SUNLieCoord Nc). This type does not depend on n. The candidate constructs its continuous linear observation, hence its derivative, rather than postulating it.

Transport the verified actual modular-torus Poincare estimate through finBoxZModEquiv and its actual shift lemma. Sum over physical directions to get

  ||A - lift(mu)||^2 <= D*n^2 ||G A||^2,
  ||lift(mu)||^2 = n^D ||mu||^2.

The elementary inequality ||u+v||^2 <= 2||u||^2+2||v||^2 suffices. Thus no orthogonal mean decomposition is needed for the intended example. With actual repair R=G* W G, W(p)=2D*n^2, and Phi_n(y)=2n^D||y||^2, the candidate gives

  ||A||^2 <= <A,R A> + Phi_n(mu(A))

on the entire finite physical cochain space. In particular it holds on any divergence-free subspace. W is positive for D,n>0; Phi_n is nonnegative, zero at zero and exactly quadratic. K_n=2n^D varies with n; no uniform K, optimal coefficient, or exact orthogonal split is claimed. Numeric output dimension D*(Nc^2-1) is not a new formal endpoint; only the actual fixed type and its finite dimensionality are checked.

Falsifiers: actual shift/reindex/norm mismatch; a mean-zero nonzero zero-gradient field; failure of actual G*WG energy identity. Retain every real diagnostic and source patch. After three units without useful mathematical progress, identify the concrete obstruction or change route.

This is a classical finite-path/mean mechanism, not an original-priority claim. Primary background already consulted: Levin/Peres, Markov Chains and Mixing Times, section13.4, author-hosted https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf; pinned Mathlib finite Cauchy-Schwarz source at07642720480157414db592fa85b626dafb71355b. The contribution sought here is the verified connection with the repository's actual finite physical operators.

If verified, this illustrates why allowing quadratic repair weights can permit fixed observation dimension. It removes no interacting or continuum Yang-Mills hypothesis, proves no physical mass gap, and changes neither PR29 20/41 nor TermSource=0. Keep related results in the existing coarse-information dossier. No separate utility paper or new deposit; frozen public AIRR v3 c9de923a...c3efb5b9 is unchanged.
Run066 atf933 failed on Nat power cast normalization and the noncomputable PiLp norm definition. Full original source, patch, raw compiler output and ZIP manifest retained. At7f37d643 only those terms change; no statement or oracle criterion is weakened. Prepared066b was never run. New067/067b drivers target7f37d643.
