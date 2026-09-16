# CMP89 directed endpoint/source-envelope cold seal

- runner revision: `cmp89-eq246-directed-endpoint-envelope-cold-v1`
- runner commit: `1428ffd8a8f7c576612d3f71a6a8d9cbcdad25d5`
- runner Git-blob SHA-256: `f8f2500dc9ecb72c4eb12ab17abdeec53d23732892cb817cac3f63c10576b501`
- notebook commit: `6d0a7e93830063dc186f9a3c3dfbc0c9c9c79b11`
- exact source: `06e6be132c5e7742bb60102e890814d4961b5d2a`
- result: `FINAL_STATUS=PASS`
- archive SHA-256: `76A4480CFF8F3061E00FB0DBACBBA11D3FED9AEECB4AE06B052F7A8DB86DAE87`
- runner payload SHA-256 (without the serialized trailing newline): `A3C3E64F2BA6F3AD04FDA5DE53CE95885F44F6B1A14169B056B1A5768768E451`
- archived `evidence.json` SHA-256 (including its one trailing newline): `4934889AFD8E8BD273534CE640B41002B25B03C12BBBE056858C1920D8A9C821`

The fail-closed verifier
`tmp/audit_cmp89_eq246_directed_endpoint_envelope_cold_evidence.py`
accepts the exact runner/source/toolchain/Mathlib fields, all four Git-blob
hashes, the complete four-stage queue with zero exits, and the stop gate.
The runtime was disconnected and deleted after local archive verification.

This seal certifies the directed endpoint phase algebra and the abstract
common source-envelope transport. It does not yet specialize the envelope
inside the joint directed source moment, construct the continuous Green,
prove CMP89 (2.42), produce uniform physical `B0`/`delta0`, attain window 15,
discharge rows 23--24, move `20/41`, or construct a `TermSource`.
