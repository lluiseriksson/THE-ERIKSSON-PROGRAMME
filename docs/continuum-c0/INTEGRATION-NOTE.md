# CONTINUUM-C0 integration note

Branch: `codex/continuum-c0`

Branch base (the fetched `origin/main` tip at branch creation):
`81721890ad3e111d73cbe45074d42ec698ce07b2`.

Later fetched `origin/main`:
`1e6113a10c407ba2964af2713aef26c62bbd1157`.
The five-commit delta touches only `YangMills/OS/SpatialOS.lean`, the Paper
13 TeX/PDF, `DASHBOARD.md`, and the global `oracle_check.lean`.  This branch
does not rebase across or edit those excluded active lanes.

## Files owned by this branch

- `YangMills/Continuum/Scale.lean`
- `YangMills/Continuum/ObservableEmbedding.lean`
- `YangMills/Continuum/GibbsSequence.lean`
- `YangMills/Continuum/RegimeObstruction.lean`
- `YangMills/Continuum/CorrelationGeometry.lean`
- `YangMills/Continuum/TwoPointFactorization.lean`
- `YangMills/Continuum/WeakLimit.lean`
- `YangMills/Continuum/Example.lean`
- `YangMills/Continuum/Oracle.lean`
- `docs/continuum-c0/CHARTER.md`
- `docs/continuum-c0/SOURCES.md`
- `docs/continuum-c0/INTEGRATION-NOTE.md`
- `docs/continuum-c0/ORACLE-OUTPUT.md`
- `docs/continuum-c0/OPUS-AUDIT-PROMPT.md`
- `docs/continuum-c0/OPUS-AUDIT-PACKET.md`
- `docs/continuum-c0/EXTERNAL-AUDIT.md`

No `YangMills/RG/**`, Paper-13 OS file, root README, dashboard, ledger,
`project-state.json`, `YangMillsCore.lean`, or global oracle file is edited.

## Build-artifact provenance

To avoid recompiling the complete YangMills dependency graph, `.lake/build`
was copied read-only from
`C:\Users\lluis\AppData\Local\Temp\eriksson-push2` into this isolated
worktree.

- source clone HEAD:
  `7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a`;
- target branch base:
  `81721890ad3e111d73cbe45074d42ec698ce07b2`;
- `git diff --stat 81721890..7c6aaab2 -- YangMills/` is empty;
- both `lean-toolchain` files contain
  `leanprover/lean4:v4.29.0-rc6`;
- `robocopy` returned code `3`, its documented successful
  “files copied plus extra destination files” result.

The source clone had uncommitted changes in
`YangMills/OS/SpatialOS.lean`, `oracle_check.lean`, and the Paper 13 TeX
file.  No C0 module imports `YangMills/OS/**`; no OS or global-oracle
artifact is accepted as a C0 result.  Every new `YangMills/Continuum/**`
module and the local `Oracle.lean` are elaborated afresh in this worktree.

## Proposed later integration

The modules are deliberately not imported by `YangMillsCore.lean` in this
branch, because the task forbids editing that integration surface.  A later
integration owner may add the desired imports after the hRpoly and Paper-13
carriles are reconciled.

The local command is:

```powershell
lake build YangMills.Continuum.Oracle
```

The global core build remains a regression check only; CONTINUUM-C0 does not
change its job graph in this branch.

## Merge caveats

- `WeakLimitReflectionPositive` is a real test-algebra transport statement.
  Do not advertise it as the complex OS axiom.
- The `d=4`, `SU(2)` example includes both the minimal identity path and a
  canonical one-point cylinder translated by `⌊x/aₙ⌋`.  The latter converges
  by integer-translation invariance, but it still does not prove multipoint
  geometric compatibility or a physical continuum law.
- The exact `|β| < 1/8450` result is an obstruction on the current `d=4`,
  `B=2` KP state producer; it is not a no-go theorem for other constructions.
- The separated two-point lane is nested: first thermodynamic volume tends
  to infinity at fixed scale, then lattice spacing tends to zero.
  `TwoPointFactorization.lean` closes this lane for the canonical axis pair
  using exact semitorus distance, including a fully discharged SU(2),
  β=10⁻⁶ example.  Constructing the corresponding certificates uniformly for
  arbitrary floor-embedded multipoint tests remains an open producer.
- The measure-level law/tightness and positive-variance obligations remain
  open by construction.
- Clay distance remains ~0% (<0.1%).
