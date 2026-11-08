# Strictly positive parity laws: exact heat-bath spectrum and a quantitative information obstruction

Analytical result for consolidation into the existing parity paper; not a new AIRR publication or a numerical assessment. The old PDF and its actual major-revision report remain unchanged. No novelty, formal replay, independent review, fixed-local interaction or physical mass-gap claim is made.

## Precise model and result

Let n>=2, Omega={-1,+1}^n, u the uniform product law, chi_S(x)=product_{i in S} x_i, and

    mu_t(x)=2^(-n)(1+t chi_[n](x)),  -1<t<1.

Every configuration has positive probability. Every proper coordinate marginal is exactly the corresponding uniform product marginal: integrating over any omitted coordinate annihilates chi_[n]. This includes t=0. Let rho_i>0 be fixed update rates, R=sum_i rho_i and m=min_i rho_i. Write P_i f=E_mu_t[f | x_j,j!=i], and use the positive continuous-time generator

    H=sum_i rho_i (I-P_i).

Each site has rate rho_i; this is not the random-scan operator divided by R. Define the optimal variance tensorization constant C_rho(t) by

    Var_mu_t(f) <= C_rho(t) sum_i rho_i E_mu_t[Var_mu_t(f | x_j,j!=i)]

for every real f. The following exact statements hold:

1. The constant mode has eigenvalue 0; chi_[n]-t has eigenvalue R.
2. For each unordered pair {S,S^c} with S nonempty and proper, put a=sum_{i in S} rho_i and b=R-a. Its two eigenvalues are

       lambda_+(a),lambda_-(a) = (R +/- sqrt((a-b)^2+4t^2 ab))/2.

   These blocks together with item1 give the whole spectrum, with repetitions counted by blocks.
3. The spectral gap and optimal tensorization constant are

       gap_rho(t) = (R-sqrt((R-2m)^2+4t^2 m(R-m)))/2,
       C_rho(t) = 1/gap_rho(t).

   The numerically stable equivalent is

       gap_rho(t) = 2(1-t^2)m(R-m)/(R+sqrt((R-2m)^2+4t^2 m(R-m))).

In particular, for unit rates,

    gap_n(t) = (n-sqrt((n-2)^2+4(n-1)t^2))/2.

The n=2 case is gap_2(t)=1-|t|. At t=0 the gap is m. At fixed n and rates, as |t| tends to1,

    gap_rho(t)/(1-t^2) -> m(R-m)/R,
    (1-t^2) C_rho(t) -> R/[m(R-m)].

For unit rates and fixed |t|<1, gap_n(t) tends to 1-t^2 as n tends to infinity. These limits follow from the stable formula, without relying on finite diagnostic cases.

## Complete proof

For every fixed rest configuration y,

    mu_t(X_i=s | rest=y) = [1+t s chi_[n]\{i}(y)]/2.

The rest marginal is uniform. Thus E[X_i | rest]=t chi_[n]\{i}. If i is not in S, P_i chi_S=chi_S. If i is in S, multiplication of Boolean characters cancels the common indices and gives P_i chi_S=t chi_{S^c}. Consequently

    H chi_S = a chi_S - t a chi_{S^c}.

This formula also holds at S=[n], where a=R and chi_empty=1, and at S=empty, where a=0. Hence H1=0 and H(chi_[n]-t)=R(chi_[n]-t).

For a proper nonempty pair the matrix on coefficients of (chi_S,chi_{S^c}) is

    B(a) = [[a, -t b], [-t a, b]].

The distinction between -ta and -tb in its two off-diagonal entries matters for unequal rates. Its trace is R, determinant (1-t^2)ab, and discriminant (a-b)^2+4t^2ab. This proves the displayed two roots. Both are positive because a,b>0 and |t|<1.

To justify completeness and the variational interpretation, character orthogonality under u gives

    E_mu_t[chi_S chi_T] = 1_{S=T} + t 1_{S=T^c}.

Distinct complement pairs are orthogonal under mu_t, including the pair {empty,[n]}. Within each pair the Gram matrix is [[1,t],[t,1]], positive definite for |t|<1. The full set of 2^n characters is a basis. The constant and centered-full-character modes plus the 2^(n-1)-1 proper complement pairs therefore exhaust all dimensions. Each P_i is the orthogonal conditional-expectation projection in L2(mu_t), so H is self-adjoint and

    <f,Hf>_mu_t = sum_i rho_i E_mu_t[Var_mu_t(f | rest)].

For a proper subset, m<=a<=R-m, since both it and its complement contain at least one site with rate>=m. Therefore a(R-a)>=m(R-m), with equality for a singleton site of minimum rate. The lower root is an increasing function of a(R-a) (subtract sqrt(R^2-4(1-t^2)a(R-a)) from R). Its minimum is attained at that singleton/complement block. This lower root is at most R/2 and therefore is no larger than the separate eigenvalue R or any upper root. It is the smallest positive eigenvalue. The Rayleigh quotient of a finite self-adjoint positive operator on the mean-zero space gives exactly C_rho=1/gap_rho, and a gap eigenvector attains equality. This proves optimality, not just a trial-function lower bound.

For t!=0 and a=m, an explicit extremizer is

    f=chi_S + [(m-gap_rho)/(t(R-m))] chi_{S^c}.

Substitution into B proves the eigenvector equation; its mean is zero and its variance is strictly positive by the positive Gram matrix. For t=0, chi_S alone is an extremizer. The formulas cover n=2 and equal rates, including the repeated eigenvalue at t=0.

## Corollary: remove the exact-zero and hard-support restrictions

Let M_{n-1}(mu) be the literal tuple of ALL proper coordinate marginals, with coordinate names retained. For fixed n>=2 and fixed positive rates there is no finite-valued function F of this tuple such that

    C_rho(mu) <= F(M_{n-1}(mu))

for every strictly positive law on Omega. Indeed M_{n-1}(mu_t)=M_{n-1}(u) for all |t|<1. A finite F at that common input is constant along this family, whereas the exact C_rho(t) tends to infinity as |t| tends to1. More generally no positive gap lower bound depending only on those marginal data can hold on this class.

For any fixed marginal order r, take n=r+1. Thus strict positivity of every individual measure does not restore a finite universal quantitative certificate based only on order<=r marginal data. This is stronger in hypotheses than the old exact-zero comparison schema: the conclusion requires neither a right-hand side vanishing at the product nor a zero-probability configuration. It does NOT exclude a positive bound on a class with a specified uniform lower-probability bound or other structural information. The two removed restrictions are proved unnecessary for this quantitative obstruction; nothing is merely renamed as a certificate structure.

This corollary concerns optimal variance tensorization constants and heat-bath gaps of finite probability laws. It does not assert an entropy constant formula, spatial covariance decay, a theorem for fixed-local Gibbs interactions, or a continuum mass gap.

## Concrete checks of the old review's objections

* Conditioning on n-1 sites is not the same input as knowing n-1-coordinate marginals. The displayed conditional law explicitly varies with t although all proper marginals are fixed.
* For the standard total-variation full-conditional influence, c_ij=|t| for i!=j: flipping x_j flips the conditional Bernoulli bias of X_i. Its row sum is (n-1)|t|, while all the proper marginal data remain unchanged. Therefore true Dobrushin coefficients do not factor through those data. No generic Dobrushin-to-entropy constant is invoked.
* If n>=3, distinct coordinate covariances vanish for every t, including when the gap is arbitrarily small. A pair-coordinate covariance claim cannot be the separating functional.
* The specified block observables X_n and product_{i<n} X_i have covariance t. No spatial-decay statement is inferred without geometry and support-dependent constants.
* The old audit corollary has no supplied four-formula bridge. It must be removed from the revised paper, not declared repaired by this calculation. The exact-zero schema may remain only as its explicitly restricted lemma.
* The new result has an explicit conditional generator and a complete basis proof. It is not a claim that the historical Lean file formalizes these new spectral statements.

## Primary-source positioning and originality limits

Alon--Goldreich--Mansour, *Almost k-wise independence versus k-wise independence* (2003), author source https://www.wisdom.weizmann.ac.il/~oded/p_agm.html, supplies the classical restricted-marginal context. No priority is claimed for the parity family or for the elementary equal-input argument.

Caputo--Menz--Tetali, *Approximate tensorization of entropy at high temperature*, Ann. Fac. Sci. Toulouse24(4) (2015),691--716, https://www.numdam.org/item/AFST_2015_6_24_4_691_0.pdf, define tensorization using actual conditionals and give their precise entropy theorem under ergodicity and gamma+kappa<1. The present result is an explicit finite variance-spectrum calculation, not that entropy theorem and not a contradiction of it.

A targeted primary-source search on2026-11-08 for parity/Glauber gaps, parity/variance tensorization and single-hyperedge Glauber spectra did not locate this exact weighted block formula. Search incompleteness is not novelty evidence. The formula follows from elementary Fourier blocks for a global n-spin interaction, since mu_t is proportional to exp(atanh(t) chi_[n]); treat originality and scientific importance as unestablished until a declared exact-manuscript assessment and further primary comparison. This analytical derivation is a result of the preparing agent, not an independent model assessment.

## Verification status and next publication boundary

The proof above is analytical and all-n. A separate exact rational diagnostic exercises the actual conditional resampling operator and the complement blocks, in normal and optimized Python, on an owned Colab Linux runtime. Its finite cases support implementation checks only. No Lean/Lake replay or all-n machine proof is claimed. No new numerical rating is issued here; the historical2.40/10 assessment belongs only to its frozen historical PDF. Consolidate this result and the explicit scope corrections into one revised parity paper, then render/review the exact new PDF and retain all prior objections before any AIRR submission/publication.
