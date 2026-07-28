# Corrected G5 lambda extension: band-0 witness

**Date:** 2026-07-21  
**State:** AUDITED_SCOPED_CANDIDATE (no gate promotion)

The historical lambda-extension probe reused the finite-tail prefactor
\(\exp(3/2)\) outside its registered endpoint.  That is not sound for
\(\lambda\in[3/2,8/5]\).  This successor recomputes the near-tail budget with
\(\exp(8/5)\), leaving the historical driver and transcripts untouched.

The seam
\[
  \beta\in[1629/16,1000/9]
\]
has
\[
  \delta=1/\beta\in[9/1000,16/1629]
  \subset [1/125,7/500],
\]
so only delta band 0 is load-bearing.  The five cells
\(\lambda\in[3/2,8/5]\) were run with the corrected budget, outward Arb
rounding, and an independent replay.  Both transcripts contain the same five
JSON rows exactly after parsing.  The worst strict lower margin is
\(0.023206136655062437\) at lambda cell 79.

The domain audit is limited to the finite five-family evaluator: its
central-chart shift satisfies
\[
  |\delta\,r\lambda/2|\le (1/30)(4/5)=2/75<3/80
\]
on the seam, and the tail prefactor is monotone in the registered endpoint,
so \(\exp(8/5)\) dominates every \(\lambda\le8/5\).  This does **not** prove
the missing scaled-bulk interval and does not promote G2, G5, or G6.

Artifacts:

- scripts/certify_surface_right_edge_five_family_finite_lambda16_corrected.py
- scripts/surface_right_edge_five_family_finite_tail_lambda16_candidate.py
- scripts/surface_right_edge_five_family_finite_lambda16_corrected_band0_production.txt
- scripts/surface_right_edge_five_family_finite_lambda16_corrected_band0_replay.txt
- scripts/validate_surface_right_edge_five_family_finite_lambda16_corrected.py
- run-records/legacy/surface-right-edge-five-family-lambda16-corrected-band0-20260721.json

The remaining finite-beta seam is a bulk obligation, not a G5 wedge
obligation: a certificate is still required on
\([1629/16,1000/9]\times[3/5,\pi-(8/5)/\beta]\).
