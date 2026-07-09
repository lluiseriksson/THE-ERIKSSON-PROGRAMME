# A Weighted Turan-Type Monotonicity Lemma (paper 3, v1)

phi_m(x) = [(m-1)I_{m-1}^2 + (m+1)I_{m+1}^2]/(m I_m^2) is strictly increasing (real m >= 1, all x > 0), by the exact factorization (S-3c)(P-(2m+1)c)+(2m+1)c^2 over the calibrated Amos bound - the third lock opened by the same key (companion: papers/bessel-amos-fh).

Application: determinant ordering c_mn < 0 of the pi-local surface expansion (2D SU(2) LGT) - structural half of the open positivity problem W < 0, which is stated precisely with its parity-mirror phenomenology (|W| ~ e^{-2.1 beta}) and explicitly NOT claimed.

Machine verification: PhiMonotone.lean (amos_calibration', amos_small, phi_unit_step, phi_step_of_recurrences), oracle [propext, Classical.choice, Quot.sound] x4, no sorry (see LEAN-VERIFICATION-LOG.txt). Twin copy + attack notes in surface-theorem/.

Novelty: ingredients classical (Amos 1974; Segura 2011; Turan-type: Thiruvenkatachar-Nanjundiah 1951, Baricz, Baricz-Pogany); the weighted statement itself not found in the literature - no stronger claim made.

v2 (9.10/10 review applied): Open Problem 5 reformulated - the parity rewriting is an exact identity for ALL pairs; bracket positivity claimed only for q*eps <= pi (q = m+n unbounded in the sum); brackets with q*eps > pi noted as not sign-definite; the open claim restated as signed-weight dominance, exact in the rewriting and open in the dominance.
