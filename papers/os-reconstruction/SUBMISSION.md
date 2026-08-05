# SUBMISSION MANIFEST — os_reconstruction_uniform

**Why this file exists.**  The archive errata of this programme (E1–E5) all
trace to the same root cause: there was no manifest, so metadata was retyped
by hand at each submission and each replacement.  This file is the single
source of truth for what goes into the form.  **Copy from here; do not
retype.**  If anything is edited later, edit it here first, then re-copy.

---

## Artefact

| field | value |
|---|---|
| PDF | `papers/os-reconstruction/os_reconstruction_uniform.pdf` |
| source | `papers/os-reconstruction/os_reconstruction_uniform.tex` |
| pages | 13 |
| module anchor | `7230b97b286775781728952d71720902b6e78073` |
| verification anchor (fresh clone) | `813658de4a1ac5f4365611c444ebf1785ed679cc` |
| Lean module | `YangMills/OS/OSReconstructionUniform.lean`, sha256 `b60120d38d0632d7088b34ddeec8ba004f81cb473751347a8cda67c0421efb43`, 70 976 bytes |
| toolchain | `leanprover/lean4:v4.29.0-rc6`, Mathlib pinned `07642720480157414db592fa85b626dafb71355b` |
| measured | core 8481 jobs; oracle 3055 reports; 0 `sorryAx`; judges 110/110 normal and `-O`; fresh clone bit-identical |

---

## TITLE (paste verbatim)

```
The Reconstructed Theory Has One Mass: a Machine-Checked Volume-Uniform Spectral Gap with Exact Identification Against the Gibbs Sums
```

## AUTHORS (paste verbatim)

```
Lluis Eriksson
```

## CATEGORY

```
Mathematical Physics
```

## ABSTRACT (plain text, paste verbatim)

```
For the spatial Z_2 (Ising-slice) system inside the Dobrushin window
2 tanh|beta| + 2 tanh|gamma| <= alpha < 1, we machine-check in Lean 4 an
end-to-end chain from the Gibbs measure to the spectrum of the reconstructed
transfer operator.

(i) The Osterwalder-Schrader (site-form) reconstruction of the transfer
operator is unitarily conjugate, by the explicit sqrt(w) boundary dressing, to
the symmetrised Dobrushin kernel. (ii) The unnormalised Gibbs sums themselves
are exact matrix elements of that operator's powers: gibbsPathSum(w,beta,N,A,B)
= lambda^N <T^N QA, QB>, with the partition function the same shape at the
dressed constant. These are identities, not bounds, and they hold at every real
beta and every positive weight. (iii) There is one mass m > 0 such that for
every spatial extent L the projected operator norm is at most e^{-m} and every
mixed connected correlator obeys |<u, T^n v> - <Omega,u><Omega,v>| <=
||u|| ||v|| (e^{-m})^n, the zero-time case included. (iv) The connected
two-point function of the normalised Gibbs measure decays at that same rate
with a constant independent of the time depth; dividing by the partition
function is licensed by a denominator floor uniform in N, which the positive
cone supplies and the spectrum does not, since the spectral route controls only
the even powers. (v) The N -> infinity limit state exists, is the vacuum state
of the reconstructed operator, and does not depend on the strictly positive
observable terminating the chain. (vi) The reconstructed operator is a
reversible Markov chain -- stochastic and in detailed balance for pi = Omega^2,
both proved -- and in that stationary state the connected correlator of bounded
observables obeys |E_pi[f P^N g] - E_pi[f] E_pi[g]| <= K_f K_g (e^{-m})^N, with
quantifier order "there exists m, for all L": no factor depending on the
spatial extent. Summing over time separations gives a susceptibility bound
K_f K_g / (1 - e^{-m}), independent of the cut-off and of the extent. The
window is non-empty at an interacting point (beta = gamma = 1/10, alpha = 1/2),
machine-checked, so none of these conditionals is vacuous.

The analytic input is inherited: the mass is the one the Dobrushin corollary
already produced, and the window is not widened. What the reconstruction
contributes is the identification, the exact identities, and the normalisation
in which both the rate and the constant lose their dependence on the volume.

We do not claim an infinite-volume transfer operator, an L -> infinity state
(the constants are extent-free; the limit is not constructed -- there are no
inclusion maps and no compatibility between pi_L and pi_{L+1}), boundary
independence beyond strictly positive time-terminations, a continuum limit, a
Wightman theory, SU(N), or any consequence for the Yang-Mills mass gap.

All statements are theorems in Lean 4 with no sorry and no project axioms;
every headline depends on exactly [propext, Classical.choice, Quot.sound].
Toolchain leanprover/lean4:v4.29.0-rc6, Mathlib pinned 0764272048...; the
repository, the anchors and the reproduction scripts are given in the paper.
```

## COMMENTS FIELD (paste verbatim)

```
13 pages. All results are machine-checked in Lean 4 (no sorry, no project
axioms; headlines depend on exactly [propext, Classical.choice, Quot.sound]).
Toolchain leanprover/lean4:v4.29.0-rc6, Mathlib pinned to
07642720480157414db592fa85b626dafb71355b. Source and verification scripts:
https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME, branch d3-closure,
module anchor 7230b97b286775781728952d71720902b6e78073, fresh-clone
verification anchor 813658de4a1ac5f4365611c444ebf1785ed679cc. Measured on a
clean clone: core build 8481 jobs, oracle 3055 reports, 0 sorryAx, judges
110/110 in both normal and optimised modes, module sha256
b60120d38d0632d7088b34ddeec8ba004f81cb473751347a8cda67c0421efb43.
```

---

## PROCEDURE AND KNOWN TRAPS (from this programme's own errata)

1. **The id is assigned at moderation, not at submission.**  Nothing is
   "published" the moment the form is sent.  Do not call it published, and do
   not cite an id that does not exist yet.
2. **A replacement rewrites the WHOLE record**, not just the file.  If a
   replacement is ever needed, re-paste every field from this manifest, or the
   untouched fields will be silently retyped wrong — that is exactly how
   errata E1–E5 happened.
3. **Do not resend anything pending.**  The 13 replacements sent 2026-08-01
   are still awaiting an administrator; resending duplicates them.
4. After the id arrives, record it **here** and in the ledger, and only then
   cite it anywhere else.

## AFTER-SUBMISSION SLOTS (fill when the id arrives)

| field | value |
|---|---|
| viXra id | *(pending — assigned at moderation)* |
| submission date | *(pending)* |
| version | v1 |
