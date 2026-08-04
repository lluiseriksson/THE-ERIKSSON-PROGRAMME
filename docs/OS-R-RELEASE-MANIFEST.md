# OS-R release manifest: finite reconstruction with one uniform mass

Date: 2026-08-04.  Status: frozen audit object, not a terminal
self-certification.

## Frozen body and claim

The Lean-bearing body is commit
`b5da95f33f5af32e992e0ba7c3084507d06f3a7c` on branch
`codex/os-reconstruction-uniform`.  That commit is the object compiled on the
sanctioned plane.  A later documentation-only manifest commit may point to it;
it does not replace the frozen Lean body.

The headline declaration is
`YangMills.OS.os_reconstruction_uniform_gap`.  For real `beta`, `gamma` and an
`alpha` satisfying

```
0 < alpha
alpha < 1
2 * tanh |beta| + 2 * tanh |gamma| <= alpha,
```

it produces one `mass > 0`, independent of every spatial extent `L`, together
with positive Perron data, the vacuum-transfer structure, projected operator
norm at most `exp (-mass)`, connected-correlation decay at the same rate, and
the exact intertwining between the OS-forced `transferOp` and the symmetric
weighted operator.  No Perron vector, vacuum, gap, mass, contraction or
clustering statement occurs among its hypotheses.

Four adjacent public declarations supply the finite OS side:
`os_ising_measure_gram_nonneg`, `os_ising_null_space_iff`,
`osIsingPhysicalEquiv`, and `os_ising_transfer_is_measure_sum`.

## Fresh-clone plane verification

The release test is a fresh detached clone of the full 40-hex body SHA, not an
injection into the older licence tree.  It uses Colab Pro+ CPU/high RAM
(50.99 GB), visible account `lluiseriksson@gmail.com`, Lean
`v4.29.0-rc6`, and Mathlib
`07642720480157414db592fa85b626dafb71355b`.

Final measured values, read only after the cell terminated:

- body SHA checked by stage 0:
  `b5da95f33f5af32e992e0ba7c3084507d06f3a7c`;
- six certifiers, normal and Python `-O`: all child sentinels zero; the
  OS-uniform judge reported 110/110 in each mode;
- eight named lane modules, including OS reconstruction: all child sentinels
  zero; the focal module completed 8191 jobs;
- complete `YangMillsCore` build: zero sentinel and
  `Build completed successfully (8482 jobs)`;
- complete `oracle_check.lean`: zero sentinel, 3015 `depends on axioms`
  reports, with each of the five new endpoints present exactly once;
- `sorryAx` occurrences: zero;
- terminal `/content/OSR_FINAL_DONE`: zero;
- final fresh runtime: opened approximately 19:51 CEST, cell closed 20:44
  CEST after 52 minutes; audit read at 20:46:22 CEST; runtime disconnected
  and deleted through the Colab UI at 20:50 CEST.

The pre-measurement predictions were 8481 core jobs and 3015 oracle reports.
The measured merged-tree totals were 8482 and 3015 respectively; the wrong
core prediction remains visible rather than being repaired after measurement.

## Adversarial tests

1. **No implication by loading the conclusion.**  The headline hypotheses
   are exactly the three scalar Dobrushin-window inequalities above.  Search
   of the declaration header finds no `VacuumTransfer`, eigenvector, mass,
   gap, norm or correlation hypothesis.  Those objects first appear after the
   existential quantifier in the conclusion.
2. **No empty parameter regime.**  `beta = gamma = 0` and, for example,
   `alpha = 1/2` satisfy the three hypotheses.  The theorem therefore is not
   an implication from an inconsistent antecedent.
3. **The OS operator is not chosen after the gap proof.**  The final clause is
   the exact `sqrtWeightEquiv` intertwining for the previously defined
   `transferOp`; `os_ising_transfer_is_measure_sum` separately identifies its
   matrix element with the reflected Gibbs sum.
4. **The quotient is not postulated.**  `os_ising_null_space_iff` identifies
   the null vectors with `ker collapseL`; `osIsingPhysicalEquiv` is the
   resulting quotient-to-boundary equivalence.
5. **Standard-cone Birkhoff route killed.**  The registered computation passed
   88/88 checks in both interpreter modes and gives projective diameter
   `Delta = 4 |beta| (L+1)`.  Hence the associated contraction bound tends to
   one with `L`; it cannot supply a volume-uniform gap.  No general Birkhoff
   theorem is claimed or revived.
6. **Historical-tree injection rejected.**  A targeted module build succeeded,
   but the subsequent injected core build used a current root importing
   `YangMills.OS.CongruenceSpectrum` against historical commit `c2723e7e`,
   where that file is absent.  Its nonzero result is recorded as an
   environment-mismatch attack, not release evidence.  The fresh-clone test
   above is the replacement.

## Cross-repository map and reuse

| Repository | Inspected HEAD | Role and reuse |
|---|---|---|
| `THE-ERIKSSON-PROGRAMME` | body `b5da95f33f5af32e992e0ba7c3084507d06f3a7c` | All Lean implementation and the exact composition theorem. |
| `lean-os-positivity` | `2ea7692fb7a60cac1b8f1deac5b1446c12557218` | OS vocabulary and comparison target; no code copied. |
| `lean-transfer-matrix` | `4e2366a4737f800ee03634a7f80b74fa2870781a` | Transfer-matrix vocabulary and comparison target; no code copied. |
| `lean-gaussian-field` | `53af447b622542735b5cd078a71a47667a4ac44d` | Gaussian contrast; no code copied. |
| `aqft-split-inclusion-series` | `078c39aefbd3b9a2e81ce1b02b2769f6f10716f1` | Noncommutative/AQFT contrast; no code copied. |
| `physmath-lean-lemmas` | `b26ce4c4ef95074e55375f3002c82c7bcff9b856` | General lemma inventory; no code copied. |

The classical “commutant plus bulk dissipation” reduction is precise but
finite and commutative: diagonal multiplication on the finite slice is
maximal abelian/self-commuting, the vacuum line is the scalar sector, and the
projected norm theorem uniformly dissipates its orthogonal complement.  This
is not advertised as a noncommutative commutant theorem.

## Body capture: bytes and EOL-normalised hashes

Capture method: at the clean body checkout, PowerShell/.NET
`File.ReadAllBytes`; SHA-256 on raw bytes; UTF-8 decode followed separately by
normalisation to LF and CRLF, encoded as UTF-8 without BOM.  The mixed-EOL raw
forms of the two large root files are therefore preserved rather than silently
identified with either normalisation.

| File | Raw bytes / SHA-256 | LF bytes / SHA-256 | CRLF bytes / SHA-256 |
|---|---|---|---|
| `YangMills/OS/OSReconstructionUniform.lean` | 5846 / `6b4f1c4fef881e19139f3cc6a3944716357b1269c51c015eb17f7a7725973dc1` | 5846 / `6b4f1c4fef881e19139f3cc6a3944716357b1269c51c015eb17f7a7725973dc1` | 5969 / `2cc30ffcdd8798f930b3b1919cabfc2df8a4e748c79118cf72bf13f3e9d7ccf3` |
| `YangMillsCore.lean` | 64776 / `c016a0ac96c073f9a4ab8e724bccbd85075e10be35a0e7285d76134fd0fdcfc6` | 63727 / `5c1a0a5cc19338ab200f48cf286e17c5b7163a21ff0650da5c8f4e279a1a5c6c` | 64785 / `e8319aed8fe494034b701e52a27794d942c095a6c7d9d18de829b25b719356e6` |
| `oracle_check.lean` | 238531 / `c84367b86383b87e3d6ea3e2ea399b7c6500e2bd51783b20380a5abc1bf1830b` | 235144 / `0ceb1309159ba124d0b61409ad8b86d7c4a7a5b5f1a544aa3d30d49d0eed89f3` | 238541 / `923bc36df56f362c766701c6189867e4de8c533250aa744b1e8f941d3d56d94e` |
| `scripts/colab_dobrushin_d4_runner.py` | 8224 / `ea6cf85f05f477262b0f8a9b5a16b55278fb86131bfb5fa1df52d281ee508834` | 8020 / `affb651fee7568e67a9208f0906895f1956b2f99c0e8bb51d125053a62caa078` | 8240 / `19d8582f3b94432ca6bf9ee271bd7874a97ab7d42269825b8bf03df1401aff0a` |
| `scripts/colab_osr_final_bootstrap.sh` | 1380 / `e32d8ad573bbc9bdba57a4adbdaeef6a18402a9cffaa2b04b31d2d2d4e77f77d` | 1380 / same | 1416 / `fe8046765f69d68606caaac9efb7a33e2b70f86e9d4e17f00ff498b593f73a05` |
| `papers/os-reconstruction-uniform/main.tex` | 20665 / `7f6c0056f93aa305266f51d82adb009425ae55b48848c3c435a598bd2caf689c` | 20665 / same | 21153 / `ea9a80f1e6438a52dbb1f609d6ee9cfc02f4bf01b686fa38551c89fc8d760329` |
| `output/pdf/os-reconstruction-uniform-gap.pdf` | 302174 / `7cb7463ec3b8280ccf61b64b3a6fc64ff8aa0f157adc6b4aec7679910046803b` | binary | binary |

The regenerated seven-page paper PDF has 302679 raw bytes and SHA-256
`c776e4dda627834b03091b34e8785aa3e220591b84ebfffb59c8ce140dbb8299`;
its TeX source has 20990 raw bytes and SHA-256
`7d88d02ac3f67ac3be45f07e855c8f3f6b4fcd5da2080c6449d0cdd0db1a1e9a`.
An external audit should reproduce the body SHA, inspect the complete logs and
issue the terminal verdict; this manifest deliberately stops at PASS
candidate.
