# K4 candidate dependency invalidation after medium-z extension

The entire-series K4 carrier was extended from `z<=4` to `z<=20` in commit
`9918f732`.  The extension passes its independent value/sign regression and
the local K4 finiteness/oracle checks, but it changes the dependency hash of
`scripts/surface_remainder_centered_delta_carrier.py`.

Consequently, the previously stored K4 candidate manifests and transcripts
are not promotion-ready: their validators reject the old dependency hash.
This was observed on the centred t-box candidate union and on the positive
`0305--0500` candidate audit.  No hash was edited in place and no old
transcript was re-labelled as current.

The authoritative carrier was subsequently restored byte-for-byte.  The old
candidate manifests therefore retain their original dependency identity; the
isolated medium-z experiment is not allowed to borrow their evidence.  Any
future use of the extension must regenerate both production and independent
replay under a separately named dependency tree, then rerun the exact
adjacency, fraction, and manifest audits.  Until that happens the extension
carries no K4/S1'''/S2'''/G6 load.
