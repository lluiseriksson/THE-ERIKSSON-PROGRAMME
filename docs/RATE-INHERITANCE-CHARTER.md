# RATE-INHERITANCE CHARTER — the commuting collapse of Conjecture 1 [REGISTERED]

Registered 2026-08-04 on branch d3-closure (hash in the registering
commit's first line).  Fabricator of the design: this desk.  Adversarial
audit of the collapse argument: an INDEPENDENT Fable 5 session (pen and
paper, all load-bearing computations reproduced in its report), which
CONFIRMED (C1)-(C2), found three repairable holes in (C3), one missed
corollary, and one backwards physical gloss — all folded in below and
recorded in §8 as measured failures of the draft.  Judges must PASS
before any analytic fabrication beyond this charter is licensed.

## 0. Provenance and honesty frame

Origin: Conjecture 1 of ai.viXra:2512.0064v2 ("The Heisenberg Cut as a
Resource Boundary", §6, tex line 493) — rate inheritance through an
interacting gapped buffer, ‖L_S‖ ≤ poly(ε)e^{−ε/ξ*} + O(e^{−Δ/k_BT}) —
restricted to COMMUTING finite-range interactions.

Finding of this charter: that restriction is DEGENERATE, and the honest
deliverable is a collapse/decoupling theorem that RESOLVES the commuting
case and relocates the conjecture's content to the non-commuting case
(or to commuting buffers with BULK dissipation, a refinement the paper
should state as the corrected conjecture).

Non-goals: no claim about the non-commuting case beyond what the
collapse implies about where the conjecture's content lives; no new
quantum-Dobrushin theory; no YM/Clay/measurement-problem connection.
Importance is not inherited by thematic proximity.

## 1. THE COLLAPSE THEOREM (corrected statement, post-audit)

Setting: buffer H_B = Σ_j h_j on sites 1..ε, pairwise commuting
[h_i,h_j] = 0, each supp h_j of diameter ≤ R, unique gapped ground
state (gap Δ, uniform in ε).  Sink: Lindblad jump operators supported
at distance > R from supp B.  Probe S coupled at strength g via S⊗B,
supp B near site 1, Bohr frequencies of S in (−Δ+δ, Δ−δ).

(1) STRICT CONE + SINK BLINDNESS (audited: CONFIRMED, airtight).
    e^{t𝓛†}(B) = e^{itH_near} B e^{−itH_near} exactly, with
    H_near = Σ_{supp h_j ∩ supp B ≠ ∅} h_j.  Far factors commute and
    cancel; the dissipator annihilates operators of disjoint support
    (D†(X) = L†XL − ½{L†L,X} = 0); finite-dimensional ODE uniqueness
    closes it.  COROLLARY (the auditor's, missed by the draft): the
    buffer+sink Lindbladian is NON-ERGODIC — every spectral projector
    of a far term is strictly conserved, the stationary manifold is
    degenerate (dim ≥ 2), and the reduced dynamics of the region at
    distance > R from the sink is exactly closed and unitary.  The
    boundary sink can never thermalize a commuting chain.

(2) LOCALITY OF THE KERNEL.  For ANY initial medium state ρ, the
    quantum-regression correlator C(t) = Tr[B e^{t𝓛}(Bρ)] equals (by
    exact duality — the suspected Heisenberg/Schrödinger bookkeeping
    error was checked and is NOT there) a finite trigonometric sum
    with frequencies in the difference spectrum of H_near and weights
    w(m,n) = B_{mn}(Bρ)_{nm}, depending ONLY on ρ restricted to
    B_{2R}(supp B).  Independent of ε and of the sink entirely.

(3) RATES.  The Davies limit does not exist in the standard sense
    (atomic C(t), no mixing) — the honest O(g²) statement is
    time-averaged: the sub-gap decoherence rate equals the total
    weight of atoms exactly resonant with the probe's Bohr
    frequencies, and satisfies
      γ_sub ≤ c‖B‖²·√(w_exc),
    with w_exc the excited spectral weight of the LOCAL state.  The
    √ is tight for pure superpositions (coherences enter at FIRST
    order — the draft's linear-in-population floor was WRONG); it
    improves to linear iff [ρ_loc, H_near] = 0 (e.g. thermal
    preparation, giving the e^{−Δ/k_BT} floor); for ground-state
    preparation γ_sub = 0 EXACTLY (gap argument via uniqueness ⟹ Ω
    is a joint eigenstate; far quantum numbers preserved; connected
    ω = 0 weight exactly zero).

(4) THE CORRECTED GLOSS (the draft had it backwards): commutativity
    does not give ξ* = ∞; it kills the CHANNEL — the transport
    contribution is identically zero, the degenerate limit is
    morally ξ* → 0.  In the quasi-free law κ(ε) = P(ε)e^{−2q(ω_b)ε}
    the exponent is carried by the sub-gap evanescent decay of the
    damped single-particle resolvent (a Green-function property),
    not by operator spreading; commuting buffers simply have no
    site-1-to-sink amplitude at any frequency.  Hence the commuting
    case sits OUTSIDE the mixing regime Conjecture 1 presupposes:
    every floor is a PREPARATION floor the sink can neither create
    nor relax ("ρ_ss" does not refer — stationarity is non-unique;
    thermal preparation must be a HYPOTHESIS, and then it is stable).

(5) THE ONE TRUE ε-EXPONENTIAL LEFT: the local restriction of the
    full-chain Gibbs preparation carries boundary corrections
    O(e^{−ε/ξ_th}) (thermal correlation length) — a correction to
    the preparation floor, NOT the conjectured transport exponential.
    Stated as a proposition with the commuting/classical reduction;
    its classical shadow is exactly the D-6 Dobrushin decay.

## 2. Paper shape (fabrication licensed only after §4 gates)

Short paper (target ~10-14 pp): the collapse theorem (1)-(4), the
preparation-floor proposition (5), the corrected restatement of
Conjecture 1 (non-commuting, or commuting + bulk dissipation), exact
numerics on the cluster chain as verification (not evidence), and an
honest limits section (exact commutativity is rigid — nothing survives
a non-commuting perturbation; finite dimensions; O(g²) time-averaged
claim only, O(g⁴) irreversibility not covered).  Venue and title:
owner's call when the manuscript exists.

## 3. Brick ladder (strict order)

- RI-0  JUDGES (§4) — gates run and read BEFORE RI-1.
- RI-1  Cone + blindness + non-ergodicity corollary, full proofs.
- RI-2  Kernel locality (2) with the QRT duality identity spelled out.
- RI-3  Rates (3): resonant-atom time-averaged statement with domain
        hypotheses; √ floor by Cauchy–Schwarz; gap argument; thermal
        linear case; ground-state zero case.
- RI-4  Gloss + corrected conjecture (4) and the preparation-floor
        proposition (5) with its commuting/classical reduction.
- RI-5  Manuscript assembly; every constant derived; numerics cited
        as verification only (tricotomy labels throughout).

## 4. Judges (registered BEFORE fabrication; two-stage tolerance freeze)

Tolerance protocol: gate STRUCTURE is frozen here; a DESIGN-ONLY pilot
(labeled, non-load-bearing, ghost-#23 discipline: benches calibrate)
measures magnitudes; final numeric tolerances are then frozen by editing
ONLY the bracketed numbers below in a commit that precedes the certified
run.  Witness model for all gates: cluster chain
H = −Σ Z_{i−1}X_iZ_{i+1} (commuting, gapped Δ = 2, genuinely quantum,
not quasi-free), probe qubit at site 1 (sub-gap detuning), sink at
site ε.  Second witness for (5): Ising ZZ+Z chain (its sub-gap atom at
2−2h vs gap 2+2h is the auditor's closed-form example).

- J-RI-2 (runs FIRST, kill-test): support weight of e^{t𝓛†}(B) outside
  B_R(supp B) at ε = 4, t ∈ [0, T_max], plus the frequency-resolved
  w_{>d}(ω) diagnostic of 2512.0070v2 (whose measured warning — ω≈0
  weight ~90% beyond the coupling site in a NON-commuting chain at
  N=6 — is the foil).  Commuting prediction: zero to integrator error.
  GATE: max relative weight ≤ [1e-8 provisional].
- GATE A (J-RI-1): induced sub-gap probe rate at ε = 4..8, γ=0
  baseline subtracted, FIXED absolute windows (0064v2 §4 methodology
  binding: no co-moving windows; gap-removed control run).  Corrected
  prediction (sharper than the draft's): the rate depends only on the
  local restriction of the preparation ⟹ exactly ε-INDEPENDENT for
  fixed local preparation.  GATE: relative spread across ε within
  [1e-6 provisional] when above the numerical floor [1e-12
  provisional]; all-below-floor passes as the exact-zero branch
  (ground preparation).
- J-RI-3 (√ vs linear floor): pure-superposition preparation at small
  excitation p — measured sub-gap weight must scale as √p (slope 1/2
  in log-log within [±0.05 provisional]); thermal preparation must
  scale linearly (slope 1 within [±0.05 provisional]).  This is the
  gate on the CORRECTED floor — the draft's linear floor would FAIL it.
- J-RI-4 (frozen sink): local excitation density at site 1 vs waiting
  time under a hot sink at site ε — prediction now ANALYTIC (the
  non-ergodicity corollary): frozen at the preparation value, no
  relaxation, no heating.  Plus the (5) measurement: boundary
  correction of the Gibbs local restriction vs ε, expected slope
  −1/ξ_th.  Measurement-labeled (verified level), never cited as
  evidence for inked claims.

## 5. Execution plane

All numerics on thread-owned Colab Pro+ Linux runtimes (owner rule
2026-08-01).  Windows: editing, git, hashes only.  Judge scripts follow
the sentinel protocol (one line, real decimal exit code, atomic) and run
in normal AND -O modes; PASS only from explicit checks and counters,
never from a Python assert.  Deterministic integrators, provenance
header (script sha256, versions, parameters), iteration caps.

## 6. Relation to the existing corpus (audit of 2026-08-04 folded in)

- aqft-split-inclusion-series (AUDITED 5/10): the campaign's source.
  Conjecture 1 verbatim (0064v2 tex:493).  Citable as proved AFTER
  re-deriving their short proofs: 0061 thm:sigma + prop:freebaseline
  (maintenance package; stroboscopic finite-d model with its
  stationarity/autonomy conditions), 0064 lem:rate (the plug from a
  rate bound to a Ċ_loss/power statement), 0060 thm:main + cor:expdecay
  (quasi-free only), 0064 res:main (the quasi-free exact law = the
  non-commuting foil).  Conditional interfaces only: 0070 thm:nogo,
  the MLSI-shaped floor hypothesis.  Binding measured warnings: 0070
  secular delocalization (J-RI-2's foil) and the ceiling/floor lesson
  (every bound proved against the correct envelope).  Its Python
  verification is print-based diagnostics — NOT certifiers under this
  repo's rules; never cite its logs as certificates.  No Lean there;
  brick_P45_combes_thomas.md is a formalization-ready note only.
- THE-ERIKSSON-PROGRAMME: D-6 chain = classical shadow of the (5)
  preparation-floor proposition's reduction; papers 7-14 lane =
  substrate for a later Lean pass of RI-1 (finite matrices only).
- lean-2d-yang-mills (AUDITED 5/10): exact non-Ising witness for the
  abstract transport theorem (heat-kernel transfer operator, gap
  1 − e^{−3t/4} closed form) — recorded for D-7, not RI.
- ym-lattice-numerics (AUDITED 3/10): transfer_gap_oracle.py = 4-decimal
  gap⇔clustering dictionary (1D Gaussian chain), quasi-free template;
  its 2602.0041/0032 scripts touch the log-Sobolev lane under
  retraction sweep — cross-check before citing.
- lean-os-positivity (AUDITED 4/10): PairingForm.lean = start point for
  the half-chain GNS construction (paper 12's missing piece);
  unrelated to RI; certificate theorems are field projections — never
  cite as verified RP.
- Remaining 12 repos: audited, nothing ≥6, no RI-relevant content;
  defects recorded in ledger Addendum 606 (notably PrimeResolventData
  trivially inhabited — riemann-resolvent-programme Program.lean:67 —
  and the never-opened Mathlib PlaneTree PR).

## 7. Failure recording

Every dead brick gets its corpse committed with diagnosis.  Named death
sites: J-RI-2 (a channel the cone argument misses — would resurrect the
conjecture's commuting content and be worth MORE than the collapse) and
RI-3 (the time-averaged statement cannot be made honest without
hypotheses so strong it goes vacuous).

## 8. Measured failures of the draft (recorded, not deleted)

The draft charter (superseded by this file, same path, git history holds
it) claimed: (i) a well-defined ρ_ss with a thermal floor — WRONG,
stationarity is provably non-unique and thermalization must be a
hypothesis; (ii) a linear-in-population floor — WRONG, coherences enter
at first order, the correct floor is √(excited weight) (Cauchy–Schwarz,
tight for pure superpositions); (iii) the Davies generator with these
rates — inapplicable (atomic C(t)), restated as time-averaged
golden-rule at resonant atoms; (iv) the gloss ξ* = ∞ — BACKWARDS, the
channel dies (ξ* → 0) and the commuting case exits the conjecture's
mixing regime.  All four found by the independent adversarial audit,
none by the fabricating desk.  The split-roles rule bought exactly what
it was written to buy.
