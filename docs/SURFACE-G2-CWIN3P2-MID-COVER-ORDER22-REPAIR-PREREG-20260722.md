# G2 mid-order repair: Taylor order 22

**Status:** preregistered repair design; not a G2 promotion.

The fixed `CWIN=3/2`, beta order 22, `t` order 25, 180-bit Arb contract is a
repair for unit 32 of the quarter-width mid-order cover.  The original
order-20 contract reaches its registered minimum `t` width on unit 32; the
incident is recorded separately.  No mesh, width, endpoint, or stopping rule
is changed by this repair.  The only changed parameter is the beta Taylor
order, from 20 to 22.

The repair is admissible only if every unit is run in production and replay,
with byte-identical transcripts, exact beta adjacency, and the same minimum
width `1/100000`.  All resulting rows remain quarantined sign evidence: they
do not imply `H_tail`, and cannot promote G2 or G6 without a separate relay
proof.

The repair driver is
`scripts/run_surface_scaled_bulk_cwin3p2_mid_cover_order22_repair.py`.
