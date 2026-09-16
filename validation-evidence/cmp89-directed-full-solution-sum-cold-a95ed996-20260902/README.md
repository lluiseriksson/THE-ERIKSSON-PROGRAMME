# CMP89 complete directed Fourier sum cold seal

Fresh Colab Pro+ CPU/high-RAM validation of exact source
`a95ed996f0a60ed7101e7b99dbe8bf998da21c7d`, with no restoration of the
project `.lake/build` graph.

- focal: exit `0`, `1402.362 s`
- audit: exit `0`, `11.734 s`
- exact axiom gate: three declarations accepted
- runner transport SHA-256: `110A9C415BB464D34CC0CF50785DD523E0DF9EA216A1636C754D436551A45006`
- archived `evidence.json` SHA-256: `F20487D3B517B292286EFCF94FA0C50DE1FA57A46E2F28D135FDD5CD3F202E0A`
- evidence archive SHA-256: `6F4D70BBF16D35A3217F0441635D690F40A2497CC571E542DAA34FB31EB72934`
- archive members: `1`
- manifest records: `16`
- source blobs: `2`
- queue stages: `2`

The fail-closed local verifier accepted the source pin, both Git-blob hashes,
the complete two-stage PASS queue, environment pins, axiom gate and archive
hash.

This seal does not move `20/41`, attain window 15, or instantiate a
`TermSource`; `TermSource = 0` remains exact.
