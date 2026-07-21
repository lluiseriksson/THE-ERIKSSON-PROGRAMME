# Positive remainder estimate for the angular Cauchy model — 2026-07-21

The diagnostic
`scripts/probe_surface_scaled_pair_cauchy_positive_remainder.py` (SHA-256
`B4CAFA120B47A0AD15382D59D1F949EDD089A2FAA78E3BD65FDFDC71AEFAAF28`)
uses order `p=50`, complex-circle radius `R=0.1`, angular displacement
`R*pi/64`, and a finite mode cutoff `M=220`.

At the beta centre `3259/32` it obtains:

* finite-mode positive derivative majorant: `4.9165e59`;
* ordered all-mode majorant with geometric tails: `1.0472e60`;
* corresponding all-mode angular remainder estimate: `1.1718e-124`.

The estimate is far below the observed circle Wronskian scale
`1.8e-79`.  It demonstrates that a high-order angular model can absorb a
positive derivative majorant without losing the cancellation.  It is still a
diagnostic: the complex Bessel derivative inequality, the geometric tail
contract, and the Cauchy-to-real-beta remainder splice need independent proof
and production/replay transcripts before any G2 promotion.

