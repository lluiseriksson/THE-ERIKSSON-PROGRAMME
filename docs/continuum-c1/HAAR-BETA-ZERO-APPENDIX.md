# Appendix: only β = 0; no statement about β > 0

This appendix is not part of the continuum no-go theorem. It concerns only
normalized Haar measure, equivalently the exactly uncoupled endpoint `β=0`.
It says nothing about a tuned weak-coupling law, any fixed `β>0`, or a
continuum trajectory.

For normalized Haar `U∈SU(N_c)` and `N_c≥2`, the checked identities
`|Re Tr U|≤N_c` and `E Re Tr U=0` imply

```text
P(a⁻⁴(N_c-Re Tr U) ≥ N_c/(2a⁴)) ≥ 1/3.
```

Indeed `X=N_c-Re Tr U` satisfies `0≤X≤2N_c` and `E X=N_c`. Splitting at
`N_c/2` gives

```text
N_c ≤ N_c/2 + (3N_c/2) P(X≥N_c/2).
```

The deterministic script `scripts/continuum_c1_tail_audit.py` checks only
this rational rearrangement and the rescaled threshold. It is classified
VERIFIED, not PROVED. Transport to a lattice plaquette would additionally
require an explicit Haar pushforward premise.
