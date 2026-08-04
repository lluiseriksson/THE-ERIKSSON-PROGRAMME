# Final body freeze — audit 49 and paper v7

This manifest freezes the implementation-and-paper body offered for a later
independent terminal review.  It does not certify its own mathematics,
priority, or publication grade.

## Git identity

- Branch: `codex/audit-bessel-fractional-49`
- Frozen body commit: `04b086942cfdfce39856ef08a0c0ff830212cc5e`
- Frozen body tree: `e4e9f25814c9b4ec87e7cd36d2a722b26e8508ff`
- Parent: `d4ad6df30dc6f35c839cfcdcfa3e9646e086cbd3`
- Capture time: `2026-08-04T18:11:50+02:00`
- `origin/main` at capture: `04f87347`; `git merge --no-edit origin/main`
  reported `Already up to date`

The manifest itself is intentionally committed after the body commit so that
the referenced tree is immutable and self-reference is avoided.

## Capture method

Raw hashes are SHA-256 over the exact bytes in the worktree at the body commit.
For text files, the LF capture decodes as UTF-8, maps CRLF and bare CR to LF,
and re-encodes as UTF-8 without BOM.  The CRLF capture then maps each LF in
that normalized stream to CRLF.  Byte counts are included to make accidental
newline conversion visible.  The PDF is binary and therefore has only a raw
capture.

| File | Raw bytes | Raw SHA-256 | LF bytes | LF SHA-256 | CRLF bytes | CRLF SHA-256 |
|---|---:|---|---:|---|---:|---|
| `AmosClosure/FractionalOrder.lean` | 9263 | `7927a73629f246a75b0de6c9c8d9b541a1dc859be78d47ad984881bffc3a5639` | 9263 | `7927a73629f246a75b0de6c9c8d9b541a1dc859be78d47ad984881bffc3a5639` | 9484 | `4456f7f0ff58c2797a708ffe190d204eb9b4f8ae50e82e8ffaaef2087dc6d109` |
| `AmosClosure.lean` | 932 | `983b32d9b065bdb489378014ce7596f17aff25202d6e8c807da5724041f54d69` | 905 | `4a67fdb244bed68eddde7aeba5c91238ad8e46ff1e7bb83dd4c4284b94c5ac4f` | 934 | `d59cb03d70e7c510a76aeae7cbc5b39c40ac8385475b3bd9c945bfc3a8d6e06a` |
| `AmosClosure/Oracle.lean` | 9961 | `c2795bee33b75b808ff54bda4e34305e513d101f463f4c3b87e36475d63244f0` | 9754 | `296a61cb2b741a49427b46de1d6b7b656a918b7251babe16b166bb66eb28b209` | 9970 | `2d54fd3975a65cf3afe9ccdcf5c64320578859c58e31992a0ad542f83ab0c34d` |
| `papers/bessel-amos-fh/bessel_amos_fh.tex` | 26561 | `b36c3afa3241b20562d32e62606c899eb70f2549aea25c8e7d99efd239a65ae0` | 26213 | `9c40263c0b158d56df52689cfcea37db6db02cb4fd86a6b249b0e7ffcad3afd7` | 26871 | `cb09fa850974ae9e056c8dd158cb86c25ccf21bfd766621343cf55bdd7899811` |
| `papers/bessel-amos-fh/README.md` | 1892 | `d1972bd573b86ea1b04bbcea86bf23a105367852337e57e0e651fc6eef0be3d6` | 1892 | `d1972bd573b86ea1b04bbcea86bf23a105367852337e57e0e651fc6eef0be3d6` | 1927 | `104901d4a1a3c9971655726d86c93c02555c3ee81f887704c5abf4a6ed96c0ec` |
| `docs/BESSEL-FRACTIONAL-STEP-AUDIT-20260804.md` | 11578 | `f96557f24e1d3bdd0d571c842a83084a156a186413e6b09810ba6d136452c329` | 11578 | `f96557f24e1d3bdd0d571c842a83084a156a186413e6b09810ba6d136452c329` | 11872 | `115a3efe304d30a30402c8ce5b0edeab87a5ef709cd2e0427bd7de5bf84f64bb` |
| `scripts/audit49_fractional_bessel.py` | 2909 | `866cfe2c523f4221c1893ad2a5279c0bea681e8eba0dfdf5760439e75d85f161` | 2909 | `866cfe2c523f4221c1893ad2a5279c0bea681e8eba0dfdf5760439e75d85f161` | 3005 | `56dee61839d354cf8524f5d687e3954e2fbe59dc4b28d5f62010b8505228b7cc` |
| `docs/audit-artifacts/bessel-fractional-step-49/COLAB-LEAN-VERIFICATION.md` | 1359 | `bc9ea7189d5447394cd54e560a32774b8f89794018fe1321141fd57ef40eabc5` | 1359 | `bc9ea7189d5447394cd54e560a32774b8f89794018fe1321141fd57ef40eabc5` | 1397 | `749c4e0f9767291427470360eb6ab294921217260120832db3b4281fe1789917` |

Binary artifact:

| File | Raw bytes | Raw SHA-256 |
|---|---:|---|
| `papers/bessel-amos-fh/bessel_amos_fh.pdf` | 360161 | `d0987ce2a56907d3bf9dd3232f9358df0ebbdc0296c3713fcf8c3cac6764a866` |

## Recorded checks and disposition offered to the external reviewer

- Literal all-real statement: **FAIL**.  Frozen witness
  `(mu,nu,x)=(-0.8,-0.4,10)` gives
  `rho_mu-rho_nu = 0.042682961675102858... > 0.04`.
- Adjusted mathematical statement: the lower inequality holds for
  `-1 < mu < nu`, and the upper inequality holds for every `x>0` exactly
  when `mu+nu >= 0`.  The Lean body deliberately formalizes the publication's
  nonnegative-order core `0 <= mu < nu`.
- Priority: the nonnegative theorem and first-contact mechanism are not
  claimed as new; Freitas--Laugesen Lemma 10 has priority.  The optimal
  negative-order boundary and the formalization are presented only as
  novelty candidates pending external review.
- Local numerical rerun: 800 seeded adversarial cases passed in the valid
  domain and the unrestricted witness above was reproduced.
- Remote Lean record: all three Lean commands succeeded, the `.olean` was
  materialized, and all five oracle reports used only
  `[propext, Classical.choice, Quot.sound]`.
- PDF QA: two clean `pdflatex` passes, 9 pages, no undefined references or
  overfull/underfull boxes; all pages were rendered and inspected, with the
  final changed page rendered again at 150 dpi.

Suggested independent attacks: replay the frozen counterexample at higher
precision; challenge the `mu+nu=0` connection-formula/Wronskian argument;
inspect the `sInf` first-contact formalization; rebuild from a clean pinned
environment; and redo the Freitas--Laugesen/Segura priority comparison from
the cited primary sources.
