# CMP89 physical Neumann Green insertion: cold evidence

- Exact source: `e4834fe7fda3a272391323030c3e8e2f7c13a0c8`.
- Cold origin: fresh Colab Pro+ CPU/high-RAM checkout, no restored project
  `.lake/build`.
- Seal authority: the same-checkout supplement archive.  It reverified HEAD,
  Mathlib and five source blobs, then recorded zero exits for both focals and
  both exact audits.
- The composite archive also retains the initial transcript and both
  instrumentation FAIL packages.  Those FAILs are not mathematical evidence.

SHA-256:

```text
CD3CD74497456FA6B64A27A2FE439814E41B8D5EE129124B929DEAD1CB07F3B5  composite-evidence.tar.gz
87547B8FB513F5F41925E01C31C922B8571A441B12EA30CAD57D5EC2FB197F0A  hrpoly-cmp89-physical-green-cold-e4834fe7-evidence.instrumentation-fail-cell.tar.gz
BF04205FC8C5F65A5A2F5A903DF2D596BD6D776E5898CA3E97EEB97F0CC3F6EA  hrpoly-cmp89-physical-green-cold-e4834fe7-evidence.tar.gz
0224D34C9F6E3BF619B6A2C3E3D3262EFC4D49B2A444321DDFF17B1D1C912290  hrpoly-cmp89-physical-green-cold-e4834fe7-same-checkout-supplement.tar.gz
B2A84A6C40AA00F071592206FC25924478FD1820428FEE1B915408E11A6872FB  hrpoly-cmp89-physical-green-cold-e4834fe7-transcript.log
```

The supplement manifest was rehashed locally with zero mismatches.  Its two
audit logs contain exactly twelve `#print axioms` headers, all within
`{propext, Classical.choice, Quot.sound}`, and no forbidden axiom token.
