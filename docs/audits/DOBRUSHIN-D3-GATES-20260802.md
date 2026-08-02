# D-3 GATES — run record, 2026-08-02

The charter registers J8, J9 and J10 **before** any Lean of this rung, and names
J9 as *"the gate that can kill the rung before Lean is written"*.  The script was
committed on time.  **Its result was not.**  Under the house rule that a
transcript does not exist until it is committed, the gate licensing D-3c had no
outcome in the repository.  This record closes that.

Artifacts: `docs/audits/d3-gates-20260802/`, with `MANIFEST.sha256`.

---

## 1. What produced these transcripts

```
script      scripts/judge_dobrushin_d3.py
blob        45109cf69dcc3f69c7891b41f8fd1ee76fac9b7f
sha256      fe867232d82198d4ca44f68833d8d85b2fb235f8fc6b480d75cb8959c6d618f8
interpreter CPython 3.12.6
host        Windows 11, owner desktop
```

**The script bytes named above carry a defective J9 legend**, corrected in the
same commit that adds this record — see §5.  The transcripts are preserved **as
run**, by those bytes, rather than regenerated to look tidy.  The acceptance rule
was not touched, so the verdict is unaffected.

## 2. Local-light contract — measured, not presumed

The standing rule presumes a script heavy without reliable prior measurement of
all three limits.  Measured here, by polling the process while it ran:

| limit | rule | normal | optimized |
| --- | --- | --- | --- |
| wall time | ≤ 30 s | **16.29 s** | **15.87 s** |
| peak RSS | ≤ 512 MiB | **12.1 MiB** | **12.6 MiB** |
| processes / pool | 1, none | **1, none** | **1, none** |

Imports are `sys`, `itertools`, `math` — standard library only, no pool, no
native extension.  A first attempt read `PeakWorkingSet64` **after** the process
exited and returned 0 MiB; that figure was discarded rather than reported, and
the measurement redone by sampling every 100 ms during the run (137 and 135
samples).

## 3. Certifier compliance

The charter forbids acceptance decisions that depend on Python `assert`, because
`python -O` removes them and two repository certifiers consequently emitted false
`PASS`.

```
assert statements in the script            0
acceptance decided by                      explicit counter + failure list
                                           (CHECKS < EXPECTED_CHECKS -> FAIL)
exit code, normal mode                     0
exit code, optimized mode (python -O)      0
stdout, normal vs optimized                BYTE-IDENTICAL
                                           sha256 731c4ef7…  for both
stderr, both modes                         empty (0 bytes, attested)
```

Both modes were run with the real script, not a stub.  The byte-identity of the
two transcripts is attested by the manifest rather than asserted in prose.

## 4. The verdict, transcribed

```
J8  |sum_s (p_s - q_s) g_s| <= TV(p,q) * osc(g), and attained
    TV=0.300000 osc=1.000000 lhs=0.300000 rhs=0.300000 ratio=1.000000000000
    TV=0.800000 osc=4.000000 lhs=3.200000 rhs=3.200000 ratio=1.000000000000
    TV=1.000000 osc=1.000000 lhs=1.000000 rhs=1.000000 ratio=1.000000000000
    -> worst ratio 1.000000000000 (must be <= 1, and = 1 somewhere)

J9  delta_k(E_i f) <= delta_k(f) + C[i][k] * delta_i(f),  and
    delta_i(E_i f) = 0.  Exhaustive over ALL Boolean observables.
    n=2 beta=0.4: 16 observables, violations=0, worst(lhs-rhs)=+0.000e+00
    n=3 beta=0.3: 256 observables, violations=0, worst(lhs-rhs)=+0.000e+00
    n=3 beta=0.9: 256 observables, violations=0, worst(lhs-rhs)=+1.110e-16

J10 |Cov_mu(f,g)| <= sum_ij delta_i(f) D_ij delta_j(g),  D = sum_n C^n
    n=3 beta=0.2: alpha=0.379949, worst |Cov|/bound = 0.240260746
    n=3 beta=0.35: alpha=0.604368, worst |Cov|/bound = 0.221712873

checks performed: 11 (expected 11)
VERDICT: PASS
```

**What each gate bought, stated at its real strength:**

* **J8 is attained at ratio exactly `1.000000000000` on three cells.**  A bound
  that is never attained would mean the constant is not the constant.  This is
  the numerical counterpart of `signed_bound_attained`, already formalised in
  D-3a — and note the direction of support: the Lean theorem is the authority,
  the gate is the pre-registration that predicted it.
* **J9 did not kill the rung.**  Zero violations across 16 + 256 + 256 Boolean
  observables at three cells, including `beta = 0.9`, well outside the window
  where the chain closes.  **This is a passed test on small systems, not a
  proof**: `|S| = 2`, `|iota| <= 3`, one explicit kernel.  D-3c remains
  unproved.
* **J10 held with room**: worst covariance ratio `0.240` and `0.222` against a
  bound of 1.  The comparison estimate as formulated is not wrong on the
  registered cells.

## 5. DEFECT FOUND IN THE GATE'S OWN NARRATION

J9 printed:

```
    -> worst (lhs - rhs) over everything: +1.110223e-16 (a POSITIVE value refutes D-3c)
```

and then passed.  **The legend is false as written.**  The pre-registered
acceptance rule is

```python
if lhs > rhs + 1e-12:
    nviol += 1
```

so the gate accepts positive slack up to `1e-12`, and `+1.11e-16` is machine
epsilon in the `tanh`/sum arithmetic.  A reader of the committed transcript would
see a positive number under a legend declaring positives to be refutations, and
would conclude either that the gate is broken or that its narration should be
ignored.  Both readings are corrosive, and the second is worse.

**What was changed, and what was not.**  Only the printed sentence.  The
tolerance `1e-12` was pre-registered in the committed script before any run and
is **untouched** — weakening or tightening a decision rule after seeing its
result is precisely the move this lane has forbidden itself, and reading the
result first does not create an exception for a repair that looks harmless.  The
transcripts above were produced by the pre-fix bytes and are kept that way, so
the defect is visible in the evidence instead of erased by a re-run.

New wording:

```
    -> worst (lhs - rhs) over everything: … (refutes D-3c only ABOVE the 1e-12
       tolerance; anything at 1e-16 is machine epsilon in the tanh/sum arithmetic)
```

**And it is the same class again**, now in a judge rather than a paper or an
audit record: the artifact was right and the sentence describing it was not.
The gate decided correctly; only its account of what it had decided was wrong.

## 6. What this does NOT establish

J9 passing is a licence to attempt D-3c, nothing more.  It tests `|S| = 2` and
`|iota| <= 3` with one explicit kernel; the key lemma is quantified over all
finite systems and all real observables.  **D-3c is unproved and unwritten.**
Popoviciu remains `SOURCE, NOT RESULT`.  The global comparison estimate and the
finite-time operator interface remain open, and charter prohibition 4 stands.
