# Formula Registry — Batch 002 LLM Index

This index flattens every formula-shaped claim in the current source DB. `verified` means the formula record itself is marked source-verified; it still may require a Lean theorem.

Total formulas: **66**. Source-verified records: **57**. Unverified/inferred route targets: **9**.

| Formula id | Source | Status | Equations | Verified | Exactness | ASCII |
|---|---:|---|---|---:|---|---|
| `cmp116.c3.visual` | Balaban CMP116 | `visual_confirmed` | 2.37, 2.38 | yes | normalized_formula | `C3 = 2*(L+2)^4*O(1)*2*E0*C1*alpha4^(-1)*alpha6^(-1)*M^q*exp(C2*kappa1)` |
| `cmp116.eq229.main` | Balaban CMP116 | `visual_confirmed` | 2.27, 2.28, 2.29, 2.30 | yes | normalized_formula | `sum_D prod_{Y in D} alpha6 * exp(-delta*kappa*d_k(Y)) <= 1` |
| `cmp116.eq230.metric` | Balaban CMP116 | `visual_confirmed` | 2.27, 2.28, 2.29, 2.30 | yes | normalized_formula | `(3*2^3)^(-1)*M^(-4)*\|Y\| <= d_k(Y) <= M^(-4)*\|Y\| - 1` |
| `cmp116.eq231.rho` | Balaban CMP116 | `visual_confirmed` | 2.31 | yes | normalized_formula | `rho = gamma2*epsilon1^2/(20*gk^2)` |
| `cmp116.eq231.entropy` | Balaban CMP116 | `visual_confirmed` | 2.31 | yes | normalized_formula | `exp(-M^(-4)*\|Z0\Y0\|*(rho - 4*M^4*exp(-2*rho))) <= 1` |
| `cmp116.eq231.p-lower` | Balaban CMP116 | `visual_confirmed` | 2.31 | yes | normalized_formula | `\|P\| >= (1/2)*M^(-4)*\|Z0\Y0\|` |
| `cmp116.eq238.activity` | Balaban CMP116 | `visual_confirmed` | 2.38 | yes | normalized_formula | `\|H(Z)\| <= C3*epsilon1*exp(-((1-8*delta)/2)*L*kappa*d_(k+1)(Z))` |
| `cmp119.eq231.r` | Balaban CMP119 | `visual_confirmed` | 2.31 | yes | normalized_formula | `\|R^(j)(X,(U,J))\| <= g_j^kappa0*exp(-kappa*d_j(X))` |
| `cmp122i.eq1.70.bound` | Balaban CMP122-I | `visual_confirmed` | 1.70 | yes | normalized_formula | `\|C_k^(n)(X,(U,J))\| <= C_0 * exp(-(1+3*beta)*kappa*d_m(X))` |
| `cmp122ii.eq1.98.exponentiation` | Balaban CMP122-II | `visual_confirmed` | 1.98, 1.99, 1.100 | yes | normalized_formula | `{...} = exp R'^(k) = exp (sum_X R'^(k)(X))` |
| `cmp122ii.eq1.99.bound` | Balaban CMP122-II | `visual_confirmed` | 1.98, 1.99, 1.100 | yes | normalized_formula | `\|R'^(k)(X,(U,J))\| <= O(1) * c_1 * exp(-(1 + (1/2)*beta)*kappa*d_{k, union Y_i}(X))` |
| `cmp122ii.eq1.100.bound` | Balaban CMP122-II | `visual_confirmed` | 1.98, 1.99, 1.100 | yes | normalized_formula | `\|R'^(k)(X,(U,J))\| <= exp(-p_0(g_k)) * exp(-kappa*d_k(X))` |
| `cmp99.eq3.27.background-field-propagator` | Balaban CMP99 | `visual_confirmed` | 3.26, 3.27 | yes | normalized_formula | `G(U) = G = (Delta_a \| Omega_0)^(-1)` |
| `cmp99.theorem3.3.background-field-green-bounds` | Balaban CMP99 | `visual_confirmed` | Theorem 3.1, Theorem 3.3, 3.42-3.47 | yes | normalized_formula | `Assumptions of Theorem 3.1 -> G(U) satisfies inequalities (3.42)-(3.47)` |
| `cmp99.theorem3.11.positive-definite-family` | Balaban CMP99 | `visual_confirmed` | Theorem 3.11 | yes | normalized_formula | `Theorems 3.1-3.10 assumptions -> Delta'_a, G', (Q'G'^2Q'^*)^(-1), Delta_a, G are positive definite` |
| `cmp99.theorem3.12.external-gauge-field-propagators` | Balaban CMP99 | `visual_confirmed` | 3.35, 3.36, Theorem 3.12 | yes | normalized_formula | `Regularity conditions (3.35),(3.36) with alpha_0 sufficiently small -> Theorems 3.3, 3.10, 3.11 hold for G,G1, and the stated H,H1 estimates hold, with the listed exception` |
| `cmp99.theorem3.15.covariance-propagator-decay` | Balaban CMP99 | `visual_confirmed` | 3.185, 3.187, Theorem 3.15 | yes | normalized_formula | `M*alpha_0 sufficiently small -> C^(k)(A) is given by (3.185) and \|C^(k)(Lambda; y,y')\| <= B0 * exp(-delta0 * \|y-y'\|)` |
| `cmp102.eq22.gauge-action-expansion-input` | Balaban CMP102 | `visual_confirmed` | 22 | yes | normalized_formula | `U_1 = exp(i eta A) = 1 + i eta A + (i eta)^2 A^2 / 2! + (i eta)^3 A^3 / 3! + (i eta)^4 A^4 R_4(i eta A)` |
| `cmp102.eq44-46.linearizing-operator-H` | Balaban CMP102 | `visual_confirmed` | 44, 45, 46 | yes | normalized_formula | `H minimizes (1/2)<A,Delta A> subject to L^j_eta Q_j A = B and RD^*A = 0; L^j_eta Q_j H B = B, RD^*H B = 0, and \|HB\|, \|nabla HB\| have CMP99 Theorem 3.12 bounds` |
| `cmp102.eq142.hessian-quadratic-expansion` | Balaban CMP102 | `visual_confirmed` | 142 | yes | normalized_formula | `F(A') = A(U_k) + (1/2)<A', Delta_1 A'> + V(A'); the second-order differential at A'=0 is this positive-definite quadratic form` |
| `dimocki.eq297.raw-activity` | Dimock I | `source_extracted` | 296, 297, 298, 299 | yes | normalized_formula | `\|H(X,Phi)\| <= H0*exp(-kappa*d_M(X))` |
| `dimocki.eq299.hsharp-decay` | Dimock I | `source_extracted` | 296, 297, 298, 299 | yes | normalized_formula | `\|H#(Y)\| <= O(1)*H0*exp(-(kappa-3*kappa0-3)*d_M(Y))` |
| `dimocki.eq334.c-resolvent-identity` | Dimock I | `source_extracted` | 334, 335 | yes | normalized_formula | `C_(k,r) = A_(k,r) + a_k^2 * A_(k,r) * Q_k * G_(k,r) * Q_k^T * A_(k,r)` |
| `dimocki.eq335.green-resolvent` | Dimock I | `source_extracted` | 334, 335 | yes | normalized_formula | `G_(k,r) = (-Delta + mu_bar_k + a_k*Q_k^T*Q_k - a_k^2*Q_k^T*A_(k,r)*Q_k)^(-1)` |
| `dimocki.eq67.covariance` | Dimock I | `source_extracted` | 66, 67, 68, 69, 70, 72, 73, 74 | yes | normalized_formula | `C_k = (Delta_k + (a/L^2) * Q^T * Q)^(-1)` |
| `dimocki.eq74.normalization` | Dimock I | `source_extracted` | 66, 67, 68, 69, 70, 72, 73, 74 | yes | normalized_formula | `Z_(k+1) = Z_k * N_(a,T^1_(M+N-k))^(-1) * (2*pi)^(\|T^0_(M+N-k)\|/2) * (det C_k)^(1/2)` |
| `dimocki.eq289.size-summability` | Dimock I | `source_extracted` | 289, 290 | yes | verbatim_formula | `sum_{X: X contains Box} exp(-a*\|X\|_M) <= b` |
| `dimocki.eq290.metric-summability` | Dimock I | `source_extracted` | 289, 290 | yes | verbatim_formula | `sum_{X: X contains Box} exp(-kappa_0*d_M(X)) <= K_0` |
| `dimocki.eq84.green-random-walk` | Dimock I | `source_extracted` | 84, 85 | yes | verbatim_formula | `G_k = sum_omega G_{k,omega}` |
| `dimocki.eq85.green-decay` | Dimock I | `source_extracted` | 84, 85 | yes | normalized_formula | `\|(G_k f)(x)\|, \|(partial G_k f)(x)\|, \|(delta_alpha partial G_k f)(x,x')\| <= C*exp(-(gamma_0/2)*d(y,y'))*\|\|f\|\|_infty` |
| `dimocki.eq293.pinned-metric-sum` | Dimock I | `source_extracted` | 292, 293, 294, 295 | yes | normalized_formula | `sum_{X superset square} exp(-kappa0*d(X)) <= K0` |
| `dimocki.eq294.intersection-sums` | Dimock I | `source_extracted` | 292, 293, 294, 295 | yes | normalized_formula | `sum_{X: X intersect Y != empty} exp(-a*\|X\|_M) <= b*\|Y\|_M; sum_{X: X intersect Y != empty} exp(-kappa0*d_M(X)) <= K0*\|Y\|_M` |
| `dimocki.eq236.small-field-exponentiation` | Dimock I | `source_extracted` | 235, 236, 237 | yes | normalized_formula | `Xi'_k(phi) = exp(sum_{Y in D^0_(k+1)} E#_k(Y,phi))` |
| `dimocki.eq237.small-field-activity-decay` | Dimock I | `source_extracted` | 235, 236, 237 | yes | normalized_formula | `\|E#_k(Y,phi)\| <= O(1)*L^3*lambda_k^(1/4-10*epsilon)*exp(-L*(kappa-5*kappa0-5)*d_LM(Y))` |
| `dimockii.appendixf.eq634.input-decay` | Dimock II | `source_extracted` | 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645, 646 | yes | normalized_formula | `\|H(X,Phi_prime,Phi)\| <= H0 * exp(-kappa * d_M(X, mod Omega^c))` |
| `dimockii.appendixf.eq636.hsharp-decay` | Dimock II | `source_extracted` | 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645, 646 | yes | normalized_formula | `\|H#(Y,Phi_prime)\| <= O(1) * H0 * exp(-(kappa - 3*kappa0 - 3) * d_M(Y, mod Omega^c))` |
| `dimockii.eq641.metric-stitching` | Dimock II | `source_extracted` | 637, 638, 639, 640, 641, 642, 643, 644 | yes | normalized_formula | `d_M(Y, mod Omega^c) <= sum_i d_M(X_i, mod Omega^c) + (n-1)` |
| `dimockii.eq642.first-activity-decay` | Dimock II | `source_extracted` | 637, 638, 639, 640, 641, 642, 643, 644 | yes | normalized_formula | `\|K(Y)\| <= O(1)*H0*exp(-(kappa-kappa0-2)*d_M(Y, mod Omega^c))` |
| `dimockii.eq644.ultralocal-ksharp` | Dimock II | `source_extracted` | 637, 638, 639, 640, 641, 642, 643, 644 | yes | normalized_formula | `K#(Y,Phi_prime) = integral K(Y,Phi_prime,Phi) dmu_Lambda(Phi)` |
| `dimockii.eq646.second-ursell` | Dimock II | `source_extracted` | 645, 646 | yes | normalized_formula | `H#(Y) = sum_{n>=1} 1/n! * sum_{(Y1,...,Yn): union_i Yi=Y} rho^T(Y1,...,Yn) * product_i K#(Yi)` |
| `dimockii.eq503.cluster-representation` | Dimock II | `source_extracted` | 501, 502, 503, 504, 505, 506 | yes | normalized_formula | `Xi''_(k,Pi+)(t,u) = exp(sum_{Y intersect Lambda_(k+1) != empty} H#_(k,Pi+)(t,u,Y))` |
| `dimockii.eq504.cluster-output-decay` | Dimock II | `source_extracted` | 501, 502, 503, 504, 505, 506 | yes | normalized_formula | `\|H#_(k,Pi+)(t,u,Y)\| <= O(1)*exp(-L*(kappa-6*kappa0-6)*d_LM(Y, mod Omega_(k+1)^c))` |
| `dimockii.eq506.cluster-input-decay` | Dimock II | `source_extracted` | 501, 502, 503, 504, 505, 506 | yes | normalized_formula | `\|H_(k,Pi+)(t,u,Y)\| <= c0*exp(-L*(kappa-3*kappa0-3)*d_LM(Y, mod Omega_(k+1)^c))` |
| `dimockii.eq272.restricted-covariance` | Dimock II | `source_extracted` | 271, 272, 273, 274, 275, 276 | yes | normalized_formula | `C'_(k,Omega) = [Delta_(k,Omega)(Lambda_k^*) + (a/L^2)*Q^T*Q]^(-1) restricted to Omega_(k+1)` |
| `dimockii.eq273.square-root-resolvent` | Dimock II | `source_extracted` | 271, 272, 273, 274, 275, 276 | yes | normalized_formula | `(C'_(k,Omega))^(1/2) = (1/pi) * integral_0^infinity dr/sqrt(r) * C'_(k,Omega,r)` |
| `dimockii.eq274.resolvent-decomposition` | Dimock II | `source_extracted` | 271, 272, 273, 274, 275, 276 | yes | normalized_formula | `C'_(k,Omega,r) = [A_(k,r) + a_k^2*A_(k,r)*Q_k*G'_(k,Omega,r)*Q_k^T*A_(k,r)] restricted to Omega_(k+1)` |
| `dimockii.eq507.boundary-factorization` | Dimock II | `source_extracted` | 507, 508, 509, 510 | yes | verbatim_formula | `Xi''_{k,Pi+}(1,1) = exp(sum_{Y # Lambda_{k+1}} B#_{k,Pi+}(Y)) * Xi''_{k,Pi+}(1,0)` |
| `dimockii.eq508.boundary-bound` | Dimock II | `source_extracted` | 507, 508, 509, 510 | yes | verbatim_formula | `\|B#_{k,Pi+}(Y)\| <= O(1)*L^3*lambda_k^(1/4-10*epsilon)*exp(-L*(kappa-6*kappa_0-6)*d_{LM}(Y, mod Omega_{k+1}^c))` |
| `dimockii.eq510.cauchy-boundary` | Dimock II | `source_extracted` | 507, 508, 509, 510 | yes | normalized_formula | `B#(Y) = (1/(2*pi*i)) * integral_{\|u\|=R} H#(1,u,Y)/(u*(u-1)) du` |
| `dimockii.eq627.modified-metric-sum` | Dimock II | `source_extracted` | 627, 628, 629, 630, 631, 632 | yes | verbatim_formula | `sum_{X in D_k(mod Omega^c), X contains Box} exp(-kappa_0*d_M(X, mod Omega^c)) <= K_0` |
| `dimockii.eq628.metric-tree-comparison` | Dimock II | `source_extracted` | 627, 628, 629, 630, 631, 632 | yes | normalized_formula | `d_M(X, mod Omega^c) >= tilde_ell_M(X intersect Omega) >= (1/2)*ell_M(X intersect Omega)` |
| `dimockii.eq205.normalization` | Dimock II | `source_extracted` | 201, 202, 205 | yes | normalized_formula | `Z_(k+1) = Z_k * N_(a,T^1_(M+N-k))^(-1) * (2*pi)^(\|T^0_(M+N-k)\|/2) * (det C_k)^(1/2)` |
| `dimockiii.eq224.final-h-bound` | Dimock III | `source_extracted` | 224, 225, 226 | yes | normalized_formula | `\|H(X)\| <= O(1)*lambda^(beta/2)*exp(-(kappa_prime-4*kappa0-4)*d_M(X))` |
| `dimockiii.eq225.stability` | Dimock III | `source_extracted` | 224, 225, 226 | yes | normalized_formula | `exp(-lambda^eta*Vol(T_M)) <= Z_(M,N)/Z_(M,N)(0) <= exp(lambda^eta*Vol(T_M))` |
| `dimockiii.eq20.e-bound` | Dimock III | `source_extracted` | 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25 | yes | normalized_formula | `\|E_k(X)\| <= lambda_k^beta * exp(-kappa*d_M(X))` |
| `dimockiii.eq22.r-bound` | Dimock III | `source_extracted` | 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25 | yes | normalized_formula | `\|R_(k,Pi)(X)\| <= lambda_k^n0 * exp(-kappa*d_M(X))` |
| `dimockiii.eq25.active-boundary-bound` | Dimock III | `source_extracted` | 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25 | yes | normalized_formula | `\|B_(k,Pi)(X)\| <= B0 * lambda_k^beta * exp(-kappa*d_M(X, mod Omega_k^c))` |
| `route.dimock.appendixf.hsharp` | Repo operational crosswalk | `lean_linked` | Dimock II Appendix F | no | normalized_formula | `\|H#(Y)\| <= O(1)*H0*exp(-(kappa-3*kappa0-3)*d_M(Y, mod Omega^c))` |
| `route.eq229.d-sum.target` | Repo operational crosswalk | `lean_linked` | CMP116 2.29, Cammarota Theorem 1 | no | normalized_formula | `sum_D prod_{Y in D} alpha6*exp(-delta*kappa*d_k(Y)) <= 1` |
| `route.eq231.membership-iff.target` | Repo operational crosswalk | `lean_linked` | CMP116 2.31, CMP109 2.17 | no | inferred | `P in BalabanPFamily(Z,D) <-> P subset gapCubes(Z,D) x Fin 4 and admissible(Z,D,P) = true` |
| `route.eq231.source-carrier-identification.target` | Repo operational crosswalk | `lean_linked` | CMP116 2.31, CMP109 2.17 | no | inferred | `BalabanEligibleCarrier(Z0,Y0) encodes into gapCubes(Z,D) x Fin 4; then \|gapCubes x Fin 4\| = 4*M^4*gapMass(Z,D)` |
| `route.eq237.fixed-z0prime.target` | Repo operational crosswalk | `lean_linked` | CMP116 2.37, CMP116 2.38 | no | inferred | `fixed_Z0_prime_bound * final_Z0_prime_sum -> CMP116PostPResidualSourceBound` |
| `route.frontier.dag` | Repo operational crosswalk | `lean_linked` | - | no | inferred | `sources -> dictionaries -> finite resummation boundaries -> activity estimate -> polymer-local R/H# -> flow/IR -> final consumers` |
| `route.flow.marginal-vs-irrelevant` | Repo operational crosswalk | `lean_linked` | CMP109 coupling recursion, CMP119 2.24 | no | inferred | `g_k marginal ~ 1/log(k) or 1/k-type control, while irrelevant remainder <= C*r^k requires separate scaling theorem` |
| `route.gaussian.root-map` | Repo operational crosswalk | `lean_linked` | CMP116 2.5-2.10, Dimock II 271-276 | no | inferred | `gaussian_pushforward + root_localization + wilson_hessian_identification + local_activity_construction + raw_pointwise_decay -> rawSource` |
| `route.r-operation.polymer-local` | Repo operational crosswalk | `lean_linked` | CMP119 2.31, CMP122-I 1.70, CMP122-II 1.98-1.100 | no | normalized_formula | `\|R^(j)(X,(U,J))\| <= g_j^kappa0*exp(-kappa*d_j(X)) and \|R'^(k)(X,(U,J))\| <= exp(-p0(g_k))*exp(-kappa*d_k(X))` |
