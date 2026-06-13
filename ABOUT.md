# Repository description (GitHub "About") — recommended text

The GitHub **About** field and any external description should not imply
an unconditional or continuum Clay proof.  The current/old text

> "A rigorous Lean 4 formalization aiming to computationally verify the
> unconditional proof of the Yang–Mills mass gap (a Clay Millennium Prize
> Problem) using the Balaban Renormalization Group."

**overstates** the project: there is no unconditional proof, no continuum
limit, no OS/Wightman reconstruction, and the distance to the Clay
problem is ~0% (<0.1%).

## Recommended About text (≤ 350 chars, copy into GitHub settings)

> Lean 4 formalization of lattice SU(N) Yang–Mills: machine-verified
> strong-coupling results (Wilson-loop area law, exponential clustering)
> and a conditional Bałaban renormalization-group infrastructure toward
> the mass-gap program. Zero `sorry`, zero project axioms. No continuum
> limit and no Clay-problem proof are claimed (distance ~0%).

### Shorter variant (one line)

> Lean 4 formalization of lattice Yang–Mills strong-coupling results and
> conditional Bałaban-RG infrastructure toward the mass-gap program; no
> continuum Clay proof claimed.

## Recommended GitHub topics

`lean4`, `mathlib`, `formal-verification`, `mathematical-physics`,
`lattice-gauge-theory`, `yang-mills`, `renormalization-group`,
`constructive-qft`.

## What the description must keep accurate

* **verified core only** — `YangMillsCore`, no `sorry`, no project axioms;
* **lattice / strong-coupling** results are theorems; the **Bałaban-RG /
  UV** material is **conditional** (carried hypotheses, never axioms);
* **no** continuum limit, OS/Wightman reconstruction, or continuum mass
  gap; **Clay distance ~0% (<0.1%)**;
* legacy/vacuous material is **excluded** from the core (see `README.md`,
  `HYPOTHESIS_FRONTIER.md`, `FOUNDATIONS.md`).
