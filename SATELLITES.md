# SATELLITES.md

Mother-repo governance table for the Eriksson ecosystem.

This file is maintained by the Revisor of `THE-ERIKSSON-PROGRAMME`.
Satellite repos may update only their own row, and only through the ritual
milestone PR described in the ecosystem master prompt.

| Hypothesis / need in mother repo | Satellite repo | Expected delivery to mother | Status | Pin |
|---|---|---|---|---|
| Gaussian primitives for hRpoly small-field estimates | `lean-gaussian-field` | `Interfaces.lean`: Isserlis/Wick, Gaussian moment bounds, finite-lattice GFF decay | active; T0 heartbeat/milestones expected | pending first `vM*` tag |
| Transfer-matrix gap/clustering bridge for M3 | `lean-transfer-matrix` | `Interfaces.lean`: finite-dimensional gap => clustering and converse lemmas | active; T0 heartbeat/milestones expected | pending first `vM*` tag |
| Formal OS/RP target language | `lean-os-positivity` | `Interfaces.lean`: reflection positivity, GNS/transfer operator target statements | active; T0 heartbeat/milestones expected | pending first `vM*` tag |
| Renormalization bookkeeping / tree Hopf algebra | `lean-connes-kreimer` | `Interfaces.lean`: rooted-tree Hopf/combinatorial renormalization primitives | active; T0 heartbeat/milestones expected | pending first `vM*` tag |
| Exactly-soluble 2D YM sandbox and Peter-Weyl benchmarks | `lean-2d-yang-mills` | `Interfaces.lean`: SU(2) heat-kernel/YM2 benchmark statements | active; T0 heartbeat/milestones expected | pending first `vM*` tag |
| Certified numerical constants and empirical lattice anchor | `ym-lattice-numerics` | `CONSTANTS.md` and versioned numerical evidence, no Lean interface unless needed | active; T0 heartbeat/milestones expected; exempt from Lean lock | pending first `vM*` tag |
| First external KP consumer / zero-free regions | `lean-zero-free-regions` | `Interfaces.lean` or dependency PRs consuming mother KP API without copying code | active; T0 heartbeat/milestones expected | pending first `vM*` tag |
| Parabolic/YM-flow toolbox | `lean-ym-flow` | `Interfaces.lean`: finite-dimensional YM-flow/gauge-covariance/smoothing primitives | active; T0 heartbeat/milestones expected | pending first `vM*` tag |
| KP rooted-tree combinatorics | `lean-rooted-tree-polymer-expansion` | Integrated Catalan/KP combinatorial payload already consumed by mother | active, no new agent | integrated; no live pin bump pending |
| Independent RH/resolvent program | `riemann-prime-resolvent` | Documentation/analogy only unless a concrete interface issue is opened | exempt from mother toolchain lock | no mother pin |
| Documentation graph | `Physmath-knowledge-tree` | Ecosystem documentation and dashboard context | no code agent | no mother pin |

## Revisor Notes

- The mother repo imports satellite work only through each satellite's
  `Interfaces.lean`.
- Any `Interfaces.lean` change requires an `interface-change` issue before a
  mother bump.
- Closing a satellite milestone means a `vM<k>` tag plus a PR touching exactly
  that satellite's row in this file.
- This table records governance state only. It is not theorem progress and does
  not discharge any mother frontier hypothesis by itself.
