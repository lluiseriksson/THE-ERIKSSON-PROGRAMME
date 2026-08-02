# Pre-registration — discharging `SpectralInterface`

Registered **before** any line of the new module was written, 2026-08-02.
Owner-approved scope: open the interface bridge now, leave Birkhoff–Hopf for
later.

## What is being attempted

`congruenceRatio_isLUB_of_birkhoff_of_spectralInterface` currently takes two
external hypotheses. This work removes the second one by *proving*
`SpectralInterface r` for a concrete, total `r : Matrix n n ℝ → ℝ`, leaving a
corollary that carries only `BirkhoffInterface`.

## Checkpoint 0 — λ independence, required before defining anything total

The risk named at review is that `Classical.choose` could hide a real drift: a
total `r` must not depend on *which* positive eigenvector is chosen. This is
**not** solved by proof irrelevance, which only kills the dependence on the
symmetry proof.

**Result: already a theorem in the tree, and it does not need symmetry.**

```
pos_eigenvector_unique {A} (hA : ∀ i j, 0 < A i j) {v w} (hv : ∀ i, 0 < v i)
    (hw : ∀ i, 0 < w i) {lam mu} (hvE …) (hwE …) :
  lam = mu ∧ ∃ c, 0 < c ∧ ∀ i, w i = c * v i
```

`YangMills/OS/PerronKernel.lean:148`. The bridge will still expose this as its
own named endpoint against the chosen value, because a lemma that exists is not
the same as a lemma that is applied.

## Death criteria (pre-registered, stop at the first failure)

1. **`SpatialSpectral.lean` is not modified.** The published module stays
   byte-identical; the bridge only adds a new file above it.
2. **No new spectral decomposition and no Courant–Fischer is formalised.** If
   `norm_act_le_specGap` does not suffice, stop and re-assess rather than start
   building spectral theory.
3. **The finished `IsLUB` corollary must not carry `hSpec`.** If it still does,
   the bridge has not closed, whatever else was proved.
4. **The Perron value must be proved independent of the choice**, via a named
   endpoint, not described as canonical.
5. **The old non-symmetric counterexample must fall outside the domain by
   construction**, and a symmetric positive `2×2` must instantiate the interface
   non-vacuously — the premises satisfiable, not merely the conclusion
   non-trivial. This is the vacuity test at the level where it bites, which is
   the level the previous version got wrong.

## Judged, not negotiable afterwards

If criterion 3 fails the work is recorded as a measured failure with its
diagnosis and the paper keeps two hypotheses. No relabelling of a partial
result as a discharge.
