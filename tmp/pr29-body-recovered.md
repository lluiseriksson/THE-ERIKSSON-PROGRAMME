## hRpoly physical completion campaign

This draft PR carries the source-specific CMP89/CMP95/CMP99/CMP102/CMP116
route toward a literal physical `hRpoly` endpoint.  It keeps analytic,
geometric and scalar obligations visible and does not replace an open
obligation by a caller-supplied hypothesis with a new name.

### Hard status

- Terminal producers installed: **20/41**.
- `TermSource` inhabitants: **0**.
- Joint scalar regime: compatible; physical window 15 is **not attained**.
- Lemma-1 / CMP116 (1.36), regional `B0`, endpoint periodization and terminal
  paper-level assembly remain open.
- This PR remains **draft**.

### Canonical evidence index

The append-only, commit-addressed evidence is maintained in:

- `docs/VERIFICATION-LEDGER.md`
- `docs/HRPOLY-CMP102-CMP116-VERTICAL-SLICE.md`

Those files record every diagnostic failure, cold seal, source/audit blob
hash, workflow/run, artifact digest, deterministic archive hash, axiom gate
and exact negative scope.  A compiler seal requires a cold checkout with no
restoration or saving of `.lake/build`; diagnostic PASS alone does not remove
PRE-VALIDATION.

### Latest source-facing cold evidence

- **Mass-uniform CMP89 complex floor** — source
  `733ecbb60d43b72e04f9740eb825251b397503b8`, cold run
  [31880056149](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31880056149),
  literal `Build completed successfully (8441 jobs).`, focal/audit `0/0`,
  three exact standard axiom blocks, artifact `9245977306`, deterministic
  archive SHA-256
  `c74135fc37c5c95b37c18b6ad909f4916eeaf7ead0fee3b7271fffff222d601c`.
- **Generated physical Green endpoint (Gate 6)** — source
  `3078a38a710dfdb735b5ecdde65d7a014b9c83ef`, cold run
  [31863743950](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31863743950),
  literal `Build completed successfully (8645 jobs).`, four exact standard
  axiom blocks.
- **Physical stabilized denominator (Gate 5)** — source
  `c99e2bbd4d8b3c24462a59f68b4cbbc3b5ddad81`, cold run
  [31858189627](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31858189627),
  literal `Build completed successfully (8578 jobs).`, five exact standard
  axiom blocks.
- **Complete fine alias-fibre nonvanishing (Gate 4)** — source
  `a7131fdb05c32c4956a8cf1bba8f8e7b1d907f13`, cold run
  [31852173144](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31852173144),
  literal `Build completed successfully (8535 jobs).`, five exact standard
  axiom blocks.

The ledger contains the earlier cold chain (generated tower, adjoints,
precision, regional Green infrastructure, density/constructor and
PreEq136 producers) with its complete hashes and scopes.

### Active PRE-VALIDATION checkpoints — NOT compiler-verified

#### Centered alias residue reflection

- Source: `8ab6624c67ebbdba270c6a8bb1176000a9319ae3`.
- Runner: `1a61eede2a6df09b38aa2d8693551611b4523949`, Git-blob SHA-256
  `d1bdb943562a40ae6e86f2e78a07dce50bb8a51097ef3663b93cdace08442499`.
- Source/audit blob SHA-256:
  `fd91da6614c95a0b04a126f0f468d8f58c870f0174468d2aec41dfa9c5621047`,
  `b934a5e4618844cc747e70e40971e9057f5f3b66a7356ba015d3651648007082`.
- Scope: alias-carrier algebra and complete-sum reindexing only.  It does not
  claim a physical fixed-fibre reflection.

#### Periodic Fourier negation between coarse fibres

- Source: `91169e8014d8afcc42ace734480300f0fea3f31a`.
- Runner: `1f3301107367d6ceb8539aaf0a26ab8b9754ec57`, Git-blob SHA-256
  `e6d742c678fe9c08419b8d33ad62b2e4d3da66092bed174b64fda78f5fc64eb9`.
- Source/audit blob SHA-256:
  `4f79bf6e12a7d9c5dbdbe459cc889d766fdd036107d81cbe13e975529a59a32d`,
  `3cabe9895f86e647585b378c77f779f49e87254e7e64b6253ed563ad37beede0`.
- Scope: exact cross-fibre carrier equivalence only.  The affine quotient
  borrow/carry, endpoint phase, finite-to-continuous periodization, regional
  `B0`, window 15 and terminal fields remain open.

### Immediate route

1. Diagnose and cold-seal the centered alias reflection without changing its
   carrier-only scope.
2. Diagnose the independent cross-fibre Fourier-negation bridge.
3. Construct the coarse-residue-dependent quotient law: target quotient is
   `-q` when the coarse residue is zero and `-q-1` otherwise.
4. Prove the full coarse-plus-alias momentum and endpoint phase identities.
5. Continue to sampled-to-continuous periodization, regional `B0`, physical
   window-15 attainment and the remaining terminal producers.

No item above moves `20/41` until a literal terminal-field producer is
installed and cold-verified.
