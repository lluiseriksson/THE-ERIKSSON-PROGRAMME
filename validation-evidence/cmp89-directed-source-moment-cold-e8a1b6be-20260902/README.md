# CMP89 directed source moment cold seal

Fresh Colab Pro+ CPU/high-RAM validation of exact source
`e8a1b6be6862256a75cf34f55dae94a48b2e1a37`, with no restoration of the
project `.lake/build` graph.

- focal: `8509/8509`, exit `0`, `1294.027 s`
- audit: exit `0`, `8.651 s`
- exact theorem axioms: `{propext, Classical.choice, Quot.sound}`
- runner payload SHA-256: `D0DACC31DC5A527C692F6C4C8CC851FAD376D0AC23963A33FDB50AFB1FD01DC3`
- archived `evidence.json` SHA-256: `5BC7C13B61E799E5A2DAF37D87028B1F80FC42DA1C082E36345016D96E4E6BB7`
- evidence archive SHA-256: `FCFB5EE4DB11BB2B2E783EC38F26E2B8D3D7E1724FDF75182642765557BEE7BF`
- archive members: `16`
- manifest records: `16`
- source blobs: `2`
- queue stages: `2`

The fail-closed local verifier accepted the source pin, both Git-blob hashes,
the complete two-stage PASS queue, environment pins, axiom allowlist and
archive hash. The retained runtime was used only for the separately labelled
hot diagnostic of the next brick, then disconnected and deleted.

This seal does not move `20/41`, attain window 15, or instantiate a
`TermSource`; `TermSource = 0` remains exact.
