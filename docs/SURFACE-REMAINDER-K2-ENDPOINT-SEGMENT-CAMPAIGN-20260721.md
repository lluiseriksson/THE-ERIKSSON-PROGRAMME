# K2 endpoint-series campaign — scoped certificate

The registered endpoint lane `[0,1/1000]` was evaluated on all 158 born
`t` boxes from the K2 partition contract.  The fixed grid ladder was
`96,192`; no posterior mesh or endpoint was introduced.  Production and a
fresh independent replay use the same wrapper hash and agree row-for-row.

The executable validator checks:

* exactly the born indices `0..157`, with no overlaps or gaps;
* ordered rational `lo,hi` rows and the registered grid ladder;
* a strict positive lower endpoint for every recorded margin;
* exact production/replay equality for every row;
* wrapper-script provenance.

This certifies only the nominal endpoint-series brick.  It does not certify
the positive-delta lanes, the direct K2 union, the completion, G2, K4, G6,
or the manuscript theorem.  The global closure gates remain unchanged until
those separate obligations have their own terminal manifests and audits.
