# K4 medium-z candidate regeneration timeout

After the carrier extension in `9918f732`, a fresh production/replay attempt
for the registered t-box `delta=[1/25,81/2000]`, `t=[3,301/100]`, with the
unchanged 9,216-cell cap and 140 Arb bits, did not produce a transcript within
the 180-second execution budget.  No output was admitted and no old manifest
was modified.

The result is a route-cost diagnostic only.  The old candidate files remain
invalid under the new dependency hash, and K4/S1'''/S2'''/G6 receive no load.
Any continuation must be separately timed and must emit fresh production and
independent replay transcripts before an adjacency or fraction audit is
considered.
