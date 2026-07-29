# O lane — continuation after the spatial-extent freeze (2026-07-28)

> **Outcome update (2026-07-29).**  The S-1 wall brick below was completed,
> strengthened through two-sided blindness and spectral-radius domination at
> `L=2`, written as *Blind to the Coupling: a Second Machine-Checked
> Obstruction at Spatial Extent*, and submitted by the owner.  The public
> identifier is pending.  Frozen paper commit: `3d313d92`; formal anchor:
> `a70426f4`; submission record:
> [`O-LANE-SUBMISSION-SPATIAL-BIRKHOFF-20260729.md`](O-LANE-SUBMISSION-SPATIAL-BIRKHOFF-20260729.md).
> S-2 subsequently closed in the separate Perron paper at Lean anchor
> `08a90502` and paper commit `316648e2`: a normalized Perron vacuum now exists
> at every finite extent.  Paper 8 then closes strict peripheral separation
> for the whole finite spectrum at Lean anchor `ac897963` and paper commit
> `b03766bd`; it was submitted by the owner on 2026-07-29 with public ID
> pending.  This is strict pointwise-in-extent separation only: S-3 remains
> open and must carry an explicit regime hypothesis.  This file remains the
> preregistered design record; its original ladder is historical, not a claim
> made by the submitted papers.

Status of the predecessor: **frozen and submitted**, v1.3, paper commit
`959076f2`, freeze declared in ledger Addendum 524.  Nothing below modifies it.

The frozen paper ends by naming two honest continuations — a Perron–Frobenius
route to the vacuum at spatial extent, or a statement that the elementary
methods end here — and declines to estimate which.  This document is the
**design pass** that turns that fork into a ladder, and it exists because a
half-hour numerical probe found something that changes the target.

Everything here is labelled by the house tricotomy.  **Nothing in this document
is proved**; `verified` means measured numerically at design level.

---

## The finding that reorders the ladder (VERIFIED, numeric, design-only)

Probe: `scripts/probe_spatial_birkhoff.py`
(sha256 `a484769864e9ecae9adc6a83378dd1933bd5d5a839211d3dc389c40659e9cf1c`),
transcript `docs/O-LANE-PROBE-TRANSCRIPT-20260728.txt`
(sha256 `9967225371401aedab3e20c83fb4a078fb60ed63bf2bbf1526cd51bed3690244`),
numpy 2.3.5, CPython 3.12.6.  Grid: `beta ∈ {0.3, 0.8}`, `gamma ∈ {0, 0.4, 1.2}`,
`L ∈ {2, 3, 4}`, exact dense diagonalisation of the `2^L × 2^L` kernels.

**A volume-uniform gap for the coupled kernel at ALL `(beta, gamma)` is FALSE.**
The measured `|lambda_2 / lambda_1|` of the coupled kernel rises towards 1 with
`L` over much of the grid — e.g. `beta = 0.8, gamma = 1.2` gives
`0.908 → 0.977 → 0.994` at `L = 2, 3, 4`.  The coupled kernel of the frozen
paper is (up to orientation) the two-dimensional Ising transfer matrix, and the
rows where the ratio stays bounded away from 1 are the rows with
`sinh(2·beta)·sinh(2·gamma) < 1` — the Kramers–Wannier disordered region.  That
identification is **literature, not proved here**, and the numbers are a
four-point grid, not a certificate.

**Consequence for the campaign, and it is the whole point of running the probe:**
any target of the form *"volume-uniform gap for the coupled system"* stated
without an explicit smallness hypothesis is attempting to prove something false.
The next analytic target must carry its region of validity in the statement.

## The second finding (VERIFIED numerically; expected to be EXACT and cheap to prove)

The natural elementary replacement for row-sum normalisation — the Hilbert
projective metric and the Birkhoff contraction coefficient — **cannot see the
interaction at all**:

* `Delta(K_gamma) = Delta(K)` in every row of the grid.  The reason is the
  frozen paper's own structural lemma: `w_gamma` depends on the **source only**,
  so it cancels identically in the projective cross-ratio
  `A(s,t)A(s',t') / (A(s,t')A(s',t))`.  A two-line argument.
* `Delta(K) = 4·beta·L` exactly in every row, so the contraction coefficient is
  `tanh(Delta/4) = tanh(beta·L) → 1`.
* And the bound is provably **not tight**: for the decoupled kernel the true
  ratio is `tanh beta` at every `L` — which is already a *theorem* of the frozen
  paper — against a Birkhoff bound of `tanh(beta·L)`.

So this route is both **`gamma`-blind** and **volume-degenerate**, and we can
demonstrate the degeneracy is the method's fault in the one case where the truth
is known.

---

## The ladder

**S-0 — PREREQUISITE, cheap, must be answered before anything is scheduled.**
Does the pinned mathlib contain Perron–Frobenius for positive/irreducible
matrices?  This could not be settled from the push clone (its mathlib checkout
is partial).  Answer it in the build clone.  It is the single largest cost
driver: if PF is absent, *"the vacuum exists"* is a campaign, not a brick.

**S-1 — THE WALL BRICK.  Recommended next paper.  Risk: low.  Scale: weeks.**
Formalise the two exact statements above: `Delta(K_gamma) = Delta(K)` (source-only
cancellation) and `Delta(K) = 4·beta·L`, hence a contraction bound `tanh(beta·L)`
that is `gamma`-blind and degenerates in the volume, against the frozen paper's
own `tanh beta` as the witness that it is not tight.  This is a **theorem either
way** and it is the same shape the lane already does well — an exact obstruction
with a short witness, in the family of the Poincaré wall.  It answers the frozen
paper's own fork with the second horn, and it answers it *by proof*.

**S-2 — EXISTENCE.  Risk: gated entirely by S-0.**
Perron vector of the coupled kernel: existence, uniqueness, strict positivity at
every `L`, every `beta`, `gamma`.  Deliberately no bound — this is the object the
frozen paper says the elementary normalisation stopped handing us.

**S-3 — THE REAL ANALYTIC TARGET.  Risk: high.  Scale: months.  Owner decision.**
A volume-uniform gap **in an explicit region**, which per the finding above is
mandatory and not a convenience.  The honest tool is a Dobrushin/high-temperature
argument, and the lane already owns cluster machinery (sharp KP, Mayer–Ursell)
from the Yang–Mills programme that has never been pointed at this kernel.

**Not on the ladder:** the exact solution.  The coupled kernel is the 2D Ising
transfer matrix, whose spectrum is known by Onsager's free-fermion method.
Formalising that is a multi-year project of a different character, and it would
prove a theorem of 1944 rather than advance this lane.

---

## What is claimed by this document

Nothing, mathematically.  It records one measured design finding that makes a
plausible next target provably wrong to aim at, one algebraic observation that
looks cheap and decisive, and a cost gate.  The tricotomy labels above are the
claim.
