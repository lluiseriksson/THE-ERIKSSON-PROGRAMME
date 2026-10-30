# Which consumer is actually obstructed

Source anchor: e31b428917aa767b4a1aad097db5cf92fb9cd23e (PR96 merge).
This is a directed source audit, not a newly compiled Lean adapter.

The concrete flat CT base route matches the unit-spacing theorem:

| Component | Exact source | Observed contract |
| --- | --- | --- |
| Fine norm | PhysicalGaugeCochains.lean:97 | PhysicalGaugeOneCochain is PiLp2 over positive bonds, with Euclidean internal coordinates |
| Flat operator | PhysicalGaugeCochains.lean:482 | flatGaugeHodgeK0CLM is backgroundGaugeHodgeK0CLM at the trivial background; no refinement-squared multiplier |
| Fine/coarse domains | PhysicalGaugeCochains.lean:624,628 | Fine side L*Nprime; coarse side Nprime, independent of L |
| Measurement | PhysicalGaugeCochains.lean:644 | flatBlockConstraintQCLM is linear linAvg, viewed in the physical positive-bond counting space |
| Poincare gate | PhysicalGaugeHodgePoincare.lean:26 | CP>0 and every fine A obeys norm²<=CP*(actualK0energy+norm(QA)²) |
| Precision | PhysicalGaugeFixedPrecision.lean:35 | actual flat K0+aQ*Q-Sigma, with no physical-spacing multiplier inserted |
| CT endpoint | PhysicalShellCombesThomasEndpoint.lean:87 | fixed-volume covariance kernel estimate, c=min(1,a)/CP, with an explicit L-dependent tilt budget |

At fixed d,Nc,Nprime the coarse space has fixed finite dimension. For any family
of scalar normalizations or coefficients, C_L may be the changed linear Q_L,
Phi_L(y)=a_L*norm(y)², and V_L=0. This is within the already checked abstract
quantified wall on the ACTUAL flat Hodge operator. Its (L+1) indexing ranges
over every positive block side and matches the consumer by setting ell=L+1.
Consequently the full-space unscaled flat base route cannot gain a positive
uniform coercivity constant merely by changing scalar measurement normalization,
even if a_L varies with L. The conclusion is mathematical specialization of
the proved general theorem; no consumer-specific Lean adapter or new build is
claimed. The sector result needs an actual bounded-rank constraint, not an
unproved identification of an arbitrary quotient norm.

There is no contradiction with CT_fixedVolume. It supplies a positive constant
and rate separately at each finite volume; it never places a fixed positive c
before all L. Furthermore its locality radius3L, entry bound and ball-count
budget also vary with L. Solving a coercivity obstruction would not by itself
close a uniform CT-rate problem.

The hRpoly consumer is NOT this operator inequality. In CorrelatorBridge.lean:
107, physical_mass_gap_of_bridge accepts a scalar bound, for all t,k,
abs(B.Rsc t k)<=C2*exp(-c0*t)*g(k)^kappa0, together with a bridge decomposition
and IR/coupling hypotheses. No definitional equation there identifies that
remainder with the present K0 form or with its inverse. The physical precision
module also explicitly stops before Wilson-Hessian identification and hraw.
Thus this audit establishes a concrete CT-route specialization, not a refutation
of hRpoly, not a producer of it, and not elimination of physical bridge hypotheses.
PR29 remains20/41 andTermSource=0. Its changes/protections are untouched.

Legitimate changes requiring another analysis include a refinement-squared
operator multiplier, growing coarse dimension or repair rank, a changed sector
norm and a non-flat interacting Hessian. The statement ell²K0 has band upper
threshold4*pi²*d*R²/Nprime² at n=ell*Nprime; the present contradiction does not
force this below every c>0. An upper bound failing to shrink is not by itself a
positive lower bound or a physical gap theorem.

## Evidence and review context

All cited files were read at the pinned source anchor, and excerpts plus LF
hashes are preserved in the unit021 evidence. This audit is by the same Codex
agent preparing the manuscript, with prior programme context. It is not blind,
independent peer review or a named-model exact-PDF screening. The public prior
v1 was rechecked on30October2026: historical import, not assessed, canonical
PDF SHA25648b2b725422263a272d9862621fa723d3d82c9d186dd7151be39c6ff1e3ff2e7.
Primary record: https://airr.science/papers/ARR-2026-7EPM3V3DP796BBRR/versions/v1/.
Its source directory contains extracted text/metadata, not an exposed TeX file;
PROVENANCE.json declares the exact external PDF canonical. This does not show
that the author's original TeX is lost. Recover it before replacing the full
historical paper; retain the present consolidation as a separate candidate.
