# CMP89 directed noncentral component cold seal

Fresh Colab Pro+ CPU/high-RAM validation of exact source
`b90a58ddc8893f081ffccb1b6ad8409226075972`, with no restoration of the
project `.lake/build` graph.

- focal: exit `0`, `1031.439 s`
- audit: exit `0`, `10.051 s`
- exact theorem axioms: `{propext, Classical.choice, Quot.sound}`
- runner transport SHA-256: `6701BB35D5C25263F525CC8985A6279F8C8C08AE17D6BEDBA449312EF8FD08B1`
- archived `evidence.json` SHA-256: `FA7F2A525B9469F17E492C933CE4A113FBDC86A6A86C4DBEA83CD07697C432E8`
- evidence archive SHA-256: `1FD7A474FFB503943AE9C12914EFBB240B0614660B137608E45975A1A87B8594`
- archive members: `1`
- manifest records: `16`
- source blobs: `2`
- queue stages: `2`

The fail-closed local verifier accepted the source pin, both Git-blob hashes,
the complete two-stage PASS queue, environment pins, axiom gate and archive
hash.

This seal does not move `20/41`, attain window 15, or instantiate a
`TermSource`; `TermSource = 0` remains exact.
