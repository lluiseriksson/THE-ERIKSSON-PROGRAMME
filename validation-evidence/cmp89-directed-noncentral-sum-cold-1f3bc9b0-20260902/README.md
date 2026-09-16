# CMP89 directed noncentral alias sum cold seal

Fresh Colab Pro+ CPU/high-RAM validation of exact source
`1f3bc9b0bb85016d1ebb96514b4da54f5e32b754`, with no restoration of the
project `.lake/build` graph.

- focal: exit `0`, `1020.017 s`
- audit: exit `0`, `9.323 s`
- exact theorem axioms: two declarations use `{propext, Quot.sound}` and one
  uses `{propext, Classical.choice, Quot.sound}`
- runner transport SHA-256: `D16BA7B99C52889F9B8456903B3CE747EA668765AC785D3AB276A4CF73B4F60A`
- archived `evidence.json` SHA-256: `D6584E90FEB7D1E2173F11C7E6103FBA87929B82E93FB33D9CF028074BB98BE3`
- evidence archive SHA-256: `455D640025FE51B3035E929A9C01E2A0BD0FC5B0AD889B30676A6F0724347964`
- archive members: `1`
- manifest records: `16`
- source blobs: `2`
- queue stages: `2`

The fail-closed local verifier accepted the source pin, both Git-blob hashes,
the complete two-stage PASS queue, environment pins, axiom gate and archive
hash.

This seal does not move `20/41`, attain window 15, or instantiate a
`TermSource`; `TermSource = 0` remains exact.
