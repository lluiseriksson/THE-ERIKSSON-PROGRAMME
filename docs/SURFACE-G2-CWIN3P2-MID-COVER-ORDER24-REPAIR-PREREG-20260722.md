# G2 mid-order repair: Taylor order 24 at unit 57

**Status:** preregistered repair design; not a G2 promotion.

The order-22 repair reaches its minimum `t` width on unit 57,
`[125/2,251/4]`.  This isolated repair changes only the beta Taylor order
from 22 to 24.  It keeps `CWIN=3/2`, t order 25, 180-bit Arb precision,
quarter-width beta mesh, and minimum `t` width `1/100000` unchanged.

The repair is admissible only after fresh production and replay transcripts
pass byte equality and the independent validator.  The resulting rows remain
quarantined sign evidence and do not imply `H_tail`, G2, G6, K2, or K4.
