# JC — machine verification, Colab run of 2026-08-01

Charter `docs/CONGRUENCE-CHARTER.md` (`49311bad`).  JC was pre-registered there
as: *zero errors, zero `sorry`, every declaration on the standard axiom triple,
and the merged-core job count +1 exactly.*

**Verdict: JC parts 1 and 2 PASS.  Part 3 NOT RUN.**

## Environment

Per the environment rule of 2026-08-01, nothing here ran on the owner's desktop.

| | |
|---|---|
| Plane | Google Colab Pro+, opened by this desk |
| Runtime | **CPU, high-RAM** (`Mycket RAM-minne`) — never GPU |
| GPU check | `nvidia-smi: command not found` → refused-if-present gate passed |
| Google account | `lluiseriksson@gmail.com` |
| Toolchain | `leanprover/lean4:v4.29.0-rc6` |
| Mathlib pin | `07642720480157414db592fa85b626dafb71355b` |
| Mathlib cache | 8142 oleans, `lake exe cache get`, ~1 min |
| Runtime state | **disconnected on completion** |

## What was verified, and against which bytes

    commit                            17d6ed29
    YangMills/OS/CongruenceSpectrum.lean
    sha256  d663b3fe251d9f0a96f50e1a65057291955afd221b3adedd69e34c73d52b8417

The same hash was computed independently on the desktop (LF-normalised) and in
Colab (`sha256sum`, native LF).  They agree, so the elaboration and the oracle
below refer to the same bytes as the source in this repository.

## Part 1 — elaboration

    ELABORATE SENTINEL: 0
    === LOG ===
    === end ===

Empty log: zero errors, zero warnings, zero `sorry`.

## Part 2 — axiom oracle, 19/19

    BUILD SENTINEL:  0
    ORACLE SENTINEL: 0

Every one of the nineteen declarations printed exactly
`[propext, Classical.choice, Quot.sound]`:

`quad_diagonal_congr`, `scale_ne_zero`, `quad_pos_congr_iff`,
`quad_neg_congr_iff`, `bond_mulVec_sym`, `bond_mulVec_anti`, `bond_ratio`,
`bond_top_pos`, `sgn_self`, `sgn_zero_one`, `sgn_one_zero`,
`tensorKernel_plus_plus`, `tensorKernel_plus_minus`, `antipodal_block_eq_bond`,
`one_sub_tanh_le`, `tanh_lt_tanh_of_lt`, `exists_extension_exceeding`,
`fused_gt_unfused`, `fused_nondegenerate`.

    grep -c sorryAx  ->  0

No project axioms, no `sorryAx`, nothing outside the standard triple.

## Part 3 — the job count — NOT RUN, and why

The module is **not imported into `YangMillsCore`** on this branch, so there is
no increment to measure yet.  Measuring it honestly means building the core
twice in the same tree — baseline and with — and `lake exe cache get` does not
cover the `YangMills` tree, so both builds compile ~8000 jobs from source.  That
is hours of Colab compute units.

It is therefore **left undone and reported as undone**, not quietly dropped and
not replaced by a delta against a number measured in somebody else's tree.  That
substitution is exactly what commit `4b65ef97` already had to correct once.

**JC is not fully discharged until part 3 runs.**  The paper says so.

## What took three iterations, recorded because it is the reusable part

Nine errors on the first run, three on the second, zero on the third — 40 s per
elaboration once the cache was warm.  Two of the nine were not typos:

* **`decide` on `sgn 0 1 = -1` cannot work in principle.**  `sgn` lands in `ℝ`,
  whose equality has no constructive decision procedure, so reduction gets stuck
  on `Classical.choice`.  The *index* comparison is decidable; discharge that and
  let `if_neg` finish.
* **`Real.tanh_lt_tanh` does not exist in this pin.**  I invented it.  The pin
  carries no `tanh` monotonicity at all, so it is now proved here from
  `Real.sinh_sub`, and the wall is routed through an explicit
  `one_sub_tanh_le : 1 - tanh x ≤ exp (-x)` rather than a limit lemma — which
  also keeps the constant visible, as the charter wanted.

Both were me asserting an API I had not checked, in a file I could not compile
locally.  The greps that settled them cost seconds and should have come first.
