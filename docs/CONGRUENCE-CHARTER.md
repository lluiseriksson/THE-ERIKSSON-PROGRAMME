# CONGRUENCE CHARTER — what a positive weight can and cannot change
# in the spectrum of a positive transfer kernel.
#
# Registered 2026-08-01, BEFORE any Lean of this lane.
# Branch: claude/congruence-spectrum, in its own worktree.

## Why this lane exists, and why it is NOT the Dobrushin lane

The S block's coupled kernel is

    T_L(σ,τ) = √(w_γ(σ)) · K_β(σ,τ) · √(w_γ(τ)),     i.e.   T_L = D K_β D,
    D = diag(√w_γ)  positive diagonal, invertible.

So **the spatial weight acts by CONGRUENCE, not by similarity.**  Similarity
preserves the whole spectrum; congruence preserves much less — and much more
than nothing.  This lane asks exactly what.

It neither uses nor produces D-1…D-5 of `docs/DOBRUSHIN-CHARTER.md`.  The two
lanes share an object and share nothing else.  Any later result of this lane
that depends on that one must say so at the point of use.

## EVIDENCE ALREADY IN HAND — MEASUREMENTS, NOT JUDGES

Registered honestly, because the alternative is worse.  The three probes below
were computed **before this charter existed**.  Under the gate rule of
2026-08-01 they therefore **cannot serve as this lane's judges**: I know their
verdicts and their margins, and adopting a gate whose verdict you already know
is choosing the referee after the match.  They are design evidence, they are
cited as evidence, and they license nothing.

* **E1 — the three limits.**  (scratch `probe_congruence.py`)
  `β = 0 ⟹ r = 0` for every γ and L (max 1.0e-15 over 25 cells);
  `γ = 0 ⟹ r = tanh β` for every L (max 1.8e-15);
  `γ → ∞ at fixed L ⟹ r → tanh(βL)` (max 4.9e-15 over 12 cells).
* **E2 — the supremum is not beaten on the hypercube.**  (`probe_sharpness_light.py`)
  Over random + Nelder–Mead ascent on positive diagonals, 9/9 cells land on
  `tanh(βL)` to ≤1.0e-15 and none exceed it.  Contract measured: 0.69 s, 73 MiB,
  one process.
* **E3 — the general principle survives an adversarial sweep.**
  (`probe_general.py`, `probe_general_adversarial.py`)  For symmetric positive
  definite `M` with unit diagonal and positive entries,
  `sup_D r(D M D) = (1-μ)/(1+μ)` with `μ = min_{i≠j} M_ij`, to ≤1.0e-15 across
  full-rank, near-singular (cond 6.4e6), near-exchangeable, isolated-argmin,
  entries-near-1, and exactly exchangeable families.

E3's first run reported `REFUTED` when the only thing that had failed was its
own positive-definiteness **precondition** on one family.  A precondition that
was never met says nothing about the claim; the script now separates the two
and returns a distinct `INCONCLUSIVE` code.  Recorded because it is the same
defect class this desk had just finished auditing elsewhere.

## THE CLAIMS

**Invariant under `K ↦ D K D`, `D > 0` diagonal.**  Rank; inertia (Sylvester,
1852); entrywise positivity; hence the *existence* of a strict Perron gap at
every finite size.

**Fragile.**  The *value* of the spectral ratio `r = |λ₁|/|λ₀|`.  On the
hypercube kernel `K_β = k_β^{⊗L}` the weight moves `r` over at least
`[tanh β, tanh(βL))` — the lower end at `γ = 0`, the upper end approached as
`γ → ∞` and never attained.

**The mechanism, in one line.**  As `γ → ∞` the weight concentrates on the two
ferromagnetic configurations, and congruence by a concentrating diagonal
**restricts** the kernel to their support.  The surviving 2×2 block is
`[[e^{βL}, e^{−βL}], [e^{−βL}, e^{βL}]]` — a single Ising bond of coupling `βL`.
**The weight fuses the L sites into one effective site with L times the
coupling.**

**The consequence, and it is the whole point.**  Volume-uniformity of the gap
is **not** a congruence invariant, and the obstruction is exactly
`tanh(βL) → 1`.  This explains why the S block's uniformity question is hard.
**It does not answer it**, and no wording in this lane may suggest that it does.

## PRE-REGISTERED JUDGES — none of these has been computed

Each predicts a NUMBER, exits non-zero on failure, and is separate: no judge
bundles a theorem with its witness.

* **JA — the convergence exponent.**  The deficit `tanh(βL) − r(T_L(β,γ))`
  must decay like `C·e^{−pγ}`.  Mechanism: the best non-ferromagnetic
  configurations carry one domain wall, weight ratio `e^{−2γ}`, hence diagonal
  ratio `e^{−γ}`, hence a second-order shift of order `e^{−2γ}`.
  **PREDICTION: p = 2.** Fitted log-slope must lie in `[−2.10, −1.90]` in every
  pre-registered cell.  If p is not 2, my account of the mechanism is wrong even
  though the limit is right, and the paper's explanatory claim must be withdrawn.
* **JB — the positive-definiteness hypothesis is load-bearing.**  For a
  pre-registered family of twelve **indefinite** symmetric `M` with unit
  diagonal and strictly positive entries, **PREDICTION: at least 1 of the 12
  exceeds `(1-μ)/(1+μ)`.**  A sweep in which none exceeds it means I do not
  know why I am assuming positive definiteness, and the hypothesis must be
  either dropped or justified before it goes to ink.
* **JC — the Lean lands where predicted.**  The module elaborates with zero
  errors and zero `sorry`; every declaration prints exactly
  `[propext, Classical.choice, Quot.sound]` or a subset; and the merged-core job
  count increments by **exactly +1** over this branch's own measured baseline.
  If the increment is not +1 it is reported as measured, never justified.

## PROHIBITIONS (registered before any fabrication)

1. **Sylvester's law of inertia is classical (1852), and Ostrowski's
   quantitative form is classical too.**  Nothing on the invariant side is new
   mathematics.  What is new is the mechanisation and the use.
2. **The `γ → ∞` limit is elementary.**  `tanh(βL)` is never to be presented as
   deep.  Its value is that it is *sharp* and that it *locates* a wall this
   corpus registered as open.
3. **The upper bound is a CONJECTURE.**  `sup_D r(DMD) = (1-μ)/(1+μ)` has
   strong certified numerics (E2, E3) and **no proof**.  The attainability
   (lower) direction is provable and is what the consequence rests on.  The
   words "sharp", "exactly", and "classification" may be used of the conjecture
   only with the word "conjecturally" attached in the same sentence.
4. **No claim that this settles S-block uniformity.**  It explains the
   difficulty; it does not resolve it.
5. **No Yang–Mills consequence** is stated, suggested, or implied.
6. **Ostrowski gives `r(DAD) ≤ κ(D²)·r(A)`, which diverges as `D` degenerates.**
   Any claim that this lane improves on Ostrowski must show the divergence and
   the finite substitute side by side, or not be made.

## ROLES

This session **FABRICATES**.  It does not audit itself.  The five-role audit
and any external verdict are a different desk, per CLAUDE.md Part I §4.  This
desk audited the Dobrushin lane earlier today; that does not license it to
audit this one.

## ENVIRONMENT (2026-08-01 rule)

Compilation, oracle and job count run on **Colab CPU / high-RAM**, opened by
this desk, never GPU, disconnected on completion.  Nothing heavier than the
light-script contract (≤30 s, one process, ≤512 MiB, all three measured) runs
on the owner's Windows desktop.  Artifacts return to the desktop and are
hash-verified before any commit.

## STAGING

Explicit paths only.  This lane lives in its own worktree
(`eriksson-congruence`, branch `claude/congruence-spectrum`) precisely so that
`davinci/dobrushin-uniform` is never disturbed; `git add -A` is forbidden.
