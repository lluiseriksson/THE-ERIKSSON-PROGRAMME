# CMP89 directed central component cold seal

Fresh Colab Pro+ CPU/high-RAM validation of exact source
`76b64ebc1307c1445136941bdcf1c01ace2f4995`, with no restoration of the
project `.lake/build` graph.

- focal: exit `0`, `1072.171 s`
- audit: exit `0`, `8.233 s`
- exact theorem axioms: `{propext, Classical.choice, Quot.sound}`
- runner transport SHA-256: `661E5A7229151DF2E7031D52DAFF440E962A40CA6E0B7D8369D5321F38850AE3`
- archived `evidence.json` SHA-256: `53AEF6664017D0E84B2391D3447EDEA736E709428CD837DAF582A20F0FF430F4`
- evidence archive SHA-256: `C6CB43993204335C5D4DD34F7FFE27C598793D18D846CCF77F14C226B1B0E02B`
- archive members: `2`
- manifest records: `16`
- source blobs: `2`
- queue stages: `2`

The fail-closed local verifier accepted the source pin, both Git-blob hashes,
the complete two-stage PASS queue, environment pins, axiom gate and archive
hash.  The retained runtime was used only for the separately labelled hot
diagnostic of the next brick, then disconnected and deleted.

This seal does not move `20/41`, attain window 15, or instantiate a
`TermSource`; `TermSource = 0` remains exact.
