# Handoff — paper 14 (O lane, spatial OS reconstruction)

Written for whoever picks this up. Nothing here is a recommendation to publish.
Read §1 before anything else.

## 1. The single most important fact

**None of the mathematics added after `27bda084` has ever been elaborated.**

Confirmed green, on the sanctioned Colab Linux plane, fresh clone:

| SHA | what was green |
|---|---|
| `27bda084` | site bridge, definiteness, uniqueness, `transferOpL`, similarity, eigenvalue-set equality, quotient. `lake env lean` on both modules, exit 0, 0 errors |
| `28d772e9` | **full terminal run**: 15 children all zero — recogniser self-test in both interpreter modes, three judges in both modes, direct `lake env lean` elaboration of both sources, `lake build YangMillsCore`, oracle. **8469 jobs, delta 0, 2911 oracle reports, distinct axioms exactly `{propext, Classical.choice, Quot.sound}`, 0 `sorryAx`, 0 errors** |

Everything from `996a2627` onwards — the sharp contraction bound, the norm
inequality, coercivity, injectivity, the isomorphism, the normalised operator —
is **source only**. It was written, oracle rows were added, the prose guard
passes, but **no Lean compiler has ever seen it**. Treat every such claim as a
candidate, not a result.

The last elaboration attempt I ran (`996a2627`) came back with **5 tactic
errors**, which I then fixed blind. Those fixes are unverified.

## 2. State of the branches

* `origin/paper14-clean` = `c917b096` — **contaminated**. Despite the name it
  carries a concurrent lane's work: `DobrushinComparison`, `DobrushinConditional`,
  `DobrushinGibbs`, `DobrushinIsing` added, `DobrushinGruss`, `DobrushinOscillation`
  modified, plus their runners, judges, papers and ledger entries.
* Local `paper14-clean` ref is **stale** at `a6855202`.
* Root cause: after creating the clean branch I kept committing from the
  **shared working tree** (`d3-closure`) and pushing with `HEAD:paper14-clean`.
  Selective `git add` does not help, because `oracle_check.lean` and
  `YangMillsCore.lean` are aggregators the other lane edits too.
* Campaign base: `345479fa` (measured 8468 jobs).
* v1.0 published anchor: `c90dc745` (measured 8469 jobs).

## 3. What paper 14 actually owns

```
YangMills/OS/SpatialOS.lean              (site bridge added to an existing module)
YangMills/OS/SpatialReconstruction.lean  (new module)
YangMillsCore.lean                       (ONE new import + a comment)
oracle_check.lean                        (rows for the OS declarations only)
papers/spatial-reconstruction/           (tex, pdf, measurements.json)
scripts/judge_site_bridge.py             pre-registered gate, blob bcfb0363…
scripts/judge_os_reconstruction.py       pre-registered gate, blob 3e236e54…
scripts/oracle_counters.py
scripts/lean_decls.py
scripts/check_no_control_bytes.py
scripts/fill_p14.py
scripts/verify_p14_links.py
scripts/verify_prereg_blobs.py
scripts/colab_sblock_runner.py
scripts/colab_bootstrap.sh
scripts/check_module_prose.py            (shared, but I edited it)
```

Everything else in the diff belongs to the other lane.

## 4. Blocking items, in order

1. **Rebuild the replay in an isolated `git worktree`**, from `345479fa`, with
   only the files in §3. Do not build it from the shared tree — that is exactly
   how the contamination happened twice.
   * `YangMillsCore.lean` must equal the base blob plus the single
     `import YangMills.OS.SpatialReconstruction`.
   * `oracle_check.lean` must be regenerated: take the base, remove every row
     naming a declaration of `SpatialOS`/`SpatialReconstruction`, require the
     remainder to be byte-identical to the base's remainder, then add exactly
     the current rows. Checking for the absence of the string "Dobrushin" is
     not enough.
   * `docs/VERIFICATION-LEDGER.md` = base + addendum 580 only.
2. **Elaborate.** `lake env lean` on both modules first — with warm `.lake`
   artefacts a green `lake build` cannot distinguish re-elaboration from a
   matching olean. Expect errors in the unverified blocks.
3. **Measure once** at the final SHA: core, oracle, counters.
4. **Generate `measurements.json` from the run**, not by hand. The committed one
   is v1.0's and the filler will refuse it (missing keys, wrong anchor).
5. **Run `scripts/fill_p14.py <sha> <json>`**, then compile the PDF, then
   `scripts/verify_p14_links.py <sha>`.

## 5. What the instruments already enforce

`fill_p14.py` is fail-closed and refuses to write unless: the tree is clean;
`HEAD` is the requested anchor; the measurement declares that anchor; the three
SHA-256 digests match the **anchor's blobs** (not the checkout); the baseline is
`c90dc745`/8469 and the campaign base is `345479fa`/8468; the job absolute is
8469 with delta 0; every declaration of **both** modules is in the oracle; no
non-standard axiom; no `sorryAx`; no control bytes; every `\osline` resolves.
Schema and JSON errors are checked refusals, not crashes.

`check_no_control_bytes.py --self-test` has ten fixtures. It exists because a
manuscript section acquired 13 BACKSPACE and 4 CR bytes from a heredoc; it later
caught the same class again in `fill_p14.py` itself.

`verify_prereg_blobs.py` certifies the pre-registration chronology by original
commits **plus blob identity**, because the replay deliberately is not a
descendant of the gate commits.

## 6. Honest assessment

An external reviewer scored the published v1.0 at **2.10/10** on a scale where
10 is a Millennium problem, and the current source at **~3.55/10 once green**.
The mathematics is classical — reflection positivity for Ising-type measures,
Osterwalder–Schrader, Osterwalder–Seiler, Fröhlich–Israel–Lieb–Simon — and the
contribution is the machine checking. There is no Hamiltonian, no functional
calculus, no spectral gap for `T`, no thermodynamic limit, no continuum, no
gauge theory. Nothing here is progress on Yang–Mills.

The owner has judged the paper not worth continuing. This document exists so
that judgement can be acted on with the facts, including the unverified parts.
