# Incident: high-grid ratio seam timeout

**Date:** 2026-07-20  
**Scope:** isolated right-edge design diagnostic; no G5/G2/G6 promotion

The preregistered diagnostic for
`lambda=[2.32,2.325]`, with five delta bands and
`qgrid=160, rgrid=32, thetagrid=8, phigrid=8, Arb=200`, was run in a five-
worker process pool.  It exceeded the 300-second operational ceiling without
producing a JSON result or any terminal row.  No partial computation is
admitted as evidence.

The timeout is an engineering limitation of this high-resolution interval
representation, not a sign result.  The lower-resolution negative seam and
its earlier subdivisions remain unchanged.  Any future continuation needs a
new analytic/localized representation or a separately budgeted contract; this
diagnostic cannot extend the candidate union.

As a follow-up cost check, the single most adverse registered delta band
(`delta_index=3`) was run with the same high-grid settings in isolation.  It
also exceeded 300 seconds without returning a row.  This rules out merely
parallel-process contention as the explanation for the timeout; the current
high-grid representation itself is too expensive for this seam.
