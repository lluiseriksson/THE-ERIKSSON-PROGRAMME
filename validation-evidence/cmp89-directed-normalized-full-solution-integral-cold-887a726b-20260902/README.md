# CMP89 normalized directed Fourier synthesis cold seal

Fresh Colab Pro+ CPU/high-RAM validation of exact source
`887a726b4dc2d79925a67d16e9be4db935139e4d`, with no restoration of the
project `.lake/build` graph.

- focal: exit `0`, `1390.672 s`, `8522` jobs
- audit: exit `0`, `11.809 s`
- exact axiom gate: two declarations, each
  `{propext, Classical.choice, Quot.sound}`
- runner transport SHA-256:
  `CCFCAF72ECA9E42CD9D099D01B6BEAE05C899B4A807EB63D9508D296A8C81C22`
- archived `evidence.json` SHA-256:
  `579087ACAF8DC2C5C257AF56D92669BB458FA0849E941B67DE05BA46282F9B84`
- evidence archive SHA-256:
  `DC5F0645D13F381B2EE27C41EE8590022AD476BA3FA6E4A8F7A59CB578944DE2`
- archive file members: `1`
- manifest records: `16`
- source blobs: `2`
- queue stages: `2`

The fail-closed local verifier accepted the source pin, both Git-blob hashes,
the complete two-stage PASS queue, environment pins, axiom gate and archive
hash.

This seal certifies synthesis only.  It does not identify the integral with
the physical generated Green, prove CMP89 (2.42), move `20/41`, attain window
15, or instantiate a `TermSource`; `TermSource = 0` remains exact.
