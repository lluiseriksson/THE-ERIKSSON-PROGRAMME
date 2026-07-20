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
