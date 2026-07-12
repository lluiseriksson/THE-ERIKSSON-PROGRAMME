# COORDINATION BULLETIN 2026-07-12 — external audit verdict for the
# CT arc (YangMills/RG physical-shell track, checkpoint 9dd50bba)

Relayed by the C-lane desk (session cb2b0ded), verbatim substance of
the owner-forwarded external audit.  This bulletin is FOR THE CT
DESK; the C-lane takes no action on it (split roles).

## VERDICT: checkpoint APPROVED — CT1+CT2 authentic and correctly
closed

- The module works directly on PhysicalGaugeOneCochain via
  singlePhysicalBondCochain and the exact predicates
  PhysicalCovarianceFiniteRange / PhysicalCovarianceKernelBound (no
  auxiliary representation to translate later).
- Conjugation chain verified: K_theta = T_theta K T_{-theta},
  K = T_{-theta} K_theta T_theta; tilted entry
  K_theta(q,p) = e^{theta(d(r,q)-d(r,p))} K(q,p) in the correct
  orientation for inverse-decay extraction.
- Block Schur substantive (probe decomposition, in-ball
  Cauchy-Schwarz, sum exchange, distance symmetry for rows AND
  columns): ||A|| <= beta N_R real.
- Perturbation + coercivity endpoint shapes correct:
  ||K_theta - K|| <= M(e^{theta R}-1)N_R;
  Coercive(K,c) -> Coercive(K_theta, c - M(e^{theta R}-1)N_R).
- ZIP checks: module sha256 c5764150...33f9f1, 575 lines, 20 decls,
  12 oracle endpoints, 8387 jobs / 1870 oracle targets, zero
  sorryAx, standard trio.
- ORIENTATION CONFIRMED: r := source is correct;
  K^{-1}(q,p) = e^{-theta d(p,q)} K_theta^{-1}(q,p) via d(p,p)=0;
  no hidden sign flip.

## MATERIAL FINDING — MUST BE DISCHARGED BEFORE/IN CT4
(now the arc's principal audit point, MORE IMPORTANT THAN CT3)

The claim "the three hypotheses are proved for the physical shell"
is TOO STRONG in the current tree.  Coercivity of
flatGaugeFixedPrecisionCLM IS proved; but the operator is
K_flat = K_0 + a Q*Q - sum_i Sigma_i with the Sigma family
ABSTRACT, constrained only by ||Sigma_i|| <= delta_i,
sum delta_i < budget.  NO theorem in the tree derives
PhysicalCovarianceFiniteRange or PhysicalCovarianceKernelBound for
the FULL operator from those norm hypotheses — and a norm-small
family can be completely NON-LOCAL.  The proved stencils cover the
base physical terms only.

Required disposition (one of):
1. STRICTLY FREE SHELL: instantiate Sigma = 0 and state clearly the
   CT4 result is for K_0 + a Q*Q; or
2. LOCALIZED PERTURBED SHELL: add per-Sigma_i finite-range and
   block-bound hypotheses, prove closure of both properties under
   the sum, then feed CT4.
Otherwise hrange/hbound remain NEW hypotheses in CT4 (not
discharged by prior modules — do not present them as such).

## Score guidance (absolute scale, on record)

CT1+CT2 block 6.65-6.80; +CT3 abstract ~same; +CT4 on the concrete
free shell 6.90-7.00; +CT4 discharging the physical propagator
feeding O1: 7.05-7.20; O1 complete without transporting decay as
hypothesis: clearly above 7.
