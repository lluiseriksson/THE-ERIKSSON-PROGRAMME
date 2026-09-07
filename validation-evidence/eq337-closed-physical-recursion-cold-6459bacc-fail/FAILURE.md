# Eq337 closed physical recursion — cold FAIL

- Status: `FAIL` (compiler evidence; not a mathematical seal)
- Source SHA: `6459baccb7d96ed40a0576a362d91a52c1f8888a`
- Runner revision: `eq337-closed-physical-recursion-promoted-cold-v1`
- Toolchain asset SHA-256: `bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e`
- Mathlib SHA: `07642720480157414db592fa85b626dafb71355b`
- Archive SHA-256: `99895547da366d72b15ab3219b2253a9e6d2f884b4c9efa83a76bf8530ea5e01`
- Opened UTC: `2026-08-26T03:15:42.021887+00:00`
- Closed UTC: `2026-08-26T03:39:51.158245+00:00`

Pinned dependencies materialized successfully in `1279.365` seconds. The first
focal target stopped after `5.305` seconds in
`BalabanCMP99Eq337ComplexClosedRadiusPhysicalBridge.lean`. The first error was
`Invalid argument name Nc`; the remaining diagnostics showed that the source
symbols from `BalabanCMP99ComplexUbarSmallFieldPropagation` were not in import
scope. No later focal target or audit ran.

The downloaded archive was verified byte-for-byte against the SHA printed by
Colab before the runtime was disconnected and deleted.
