# K2 endpoint historical compatibility note

The archived endpoint transcript
`scripts/certify_surface_remainder_delta0_endpoint_transcript.txt` is pinned
to commit `46cdff0806cf07d2da87255cb40b813da0c0696b` and to the endpoint
driver hash
`7287efbc541adf7a5a18bef45c75f4598d895dd929f7bb648bdb40c273413c03`.

The current driver has hash
`01d2f44d3c62a0bf5af082bf2419f700d66471bf923acec55ca44322837d8e3f`.
The validator accepts this historical transcript only because it verifies,
mechanically, that the current bytes are obtained from the pinned historical
blob by the single provenance-only replacement
`git rev-parse HEAD` → `git -c safe.directory=... rev-parse HEAD`.
All mathematical code and all six dependency blobs remain byte-identical.

This compatibility is deliberately one-way: the transcript retains its
original hash and commit; future runs must record the current driver hash.
The check does not promote the endpoint beyond its existing scope
`[0,1/1000] x [0,pi]`, and it does not alter K2's global gate.

Validation executed on 2026-07-21:

```text
K2 endpoint transcript OK: 158 boxes
4 targeted tests passed
```
