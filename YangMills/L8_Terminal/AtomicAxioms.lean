import YangMills.L7_Continuum.ContinuumLimit
/-!
# Atomic Axioms for the Continuum Mass Gap

This file factors `yangMills_continuum_mass_gap` (the single BFS-live custom
axiom of the Eriksson programme) into three atomic sub-axioms, each corresponding
to a precise theorem in the Bloque4 paper:

  **Bloque4**: "Exponential Clustering and Mass Gap for Four-Dimensional
  SU(N) Lattice Yang-Mills Theory", L. Eriksson, February 2026.

## Proof chain (Bloque4 §§3-8)

```
yangMills_ax_terminalKP_smallness
    (Thm 5.3 of Bloque4; proved in Paper [1] from Bałaban [7,8,9,10])
  ↓  via Prop A.1 (KP → exponential decay)
yangMills_ax_terminalKP_smallness
  + yangMills_ax_multiscaleUV_suppression    (Thm 6.3 of Bloque4)
  ↓  via Assembly Thm 7.1:  m = min(m_*, c₀) > 0
yangMills_ax_OSAssembly                      (Lem 8.2 + Rem 8.6)
  ↓
yangMills_continuum_mass_gap                 (now a theorem, not an axiom)
```

## OS status (Bloque4 §8)

| Axiom | Content               | Status in Bloque4            |
|-------|-----------------------|------------------------------|
| OS0   | Temperedness          | Proved (Uniform L∞ bounds)   |
| OS1   | Euclidean covariance  | **Partial** (W₄ only; O(4) not proved) |
| OS2   | Reflection positivity | Proved (Osterwalder–Seiler)  |
| OS3   | Bosonic symmetry      | Proved (automatic)           |
| OS4   | Cluster property      | Proved (= Theorem 7.1)       |

Note: OS1 (full O(4) covariance) is NOT needed for the mass gap.
Remark 8.6 establishes the spectral gap using only OS2 + Theorem 7.1.
-/

namespace YangMills

/-!
## Abstract predicates

These predicates name the two key intermediate properties that drive the proof.
They are abstract (opaque): their content is given by the axioms below.
-/

/--
`HasTerminalKPSmallness m_lat` asserts that the terminal-scale polymer activities
associated with the lattice mass profile `m_lat` satisfy the Kotecký–Preiss (KP)
smallness condition.

Concretely (Bloque4, Theorem 5.3): ∃ γ₀, κ, a > 0 and δ ∈ (0,1) such that for
all ḡ ∈ (0, γ₀] and all L_phys > 0,

  sup_ℓ  ∑_{X ∋ ℓ, X connected}  ‖e^{ℛ_*(X)} - 1‖_∞ · e^{a|X|} · e^{κ d_*(X)}  ≤  δ

where the sum runs over terminal-scale connected polymers X containing lattice
link ℓ, and d_*(X) := d_{k_*}(X) is the terminal-scale diameter.

**Source**: Theorem 5.3 of Bloque4, proved in companion Paper [1]
(Eriksson 2026) from Bałaban's CMP papers [7,8,9,10] via notation bridge [2].
-/
opaque HasTerminalKPSmallness : LatticeMassProfile → Prop

/--
`HasMultiscaleUVSuppression m_lat` asserts that the sum of single-scale
conditional covariance remainders R_k(F, G) over all renormalization-group
scales k = 0, …, k_* − 1 decays exponentially in dist(supp F, supp G) / a_*,
uniformly in lattice spacing η and physical volume L_phys.

Concretely (Bloque4, Theorem 6.3 — UV Suppression): ∃ C', c₀ > 0 (independent
of η, R, L_phys) such that for all gauge-invariant bounded observables F, G with
supp-separation R := dist(supp F, supp G) ≥ a_*:

  |∑_{k=0}^{k_*-1} R_k(F, G)|  ≤  C' ‖F‖_∞ ‖G‖_∞ e^{-c₀ R / a_*}.

**Source**: Theorem 6.3 of Bloque4. Proof uses the multiscale telescoping
identity (Prop 6.1), single-scale UV error bound (Lem 6.2), Bałaban's
propagator decay (Lem B.1 from [4,5]), and Dimock's cluster-expansion
framework [14,15,16].
-/
opaque HasMultiscaleUVSuppression : LatticeMassProfile → Prop

/-!
## Atomic axioms (AF1 – AF3)

These three axioms replace the single monolithic `yangMills_continuum_mass_gap`.
Each corresponds to a specific theorem in Bloque4.
-/

/--
**Axiom AF1** — Terminal Kotecký–Preiss smallness.

There exists a lattice mass profile for which the terminal-scale polymer
activities satisfy the Kotecký–Preiss smallness condition.

**Paper correspondence**: Theorem 5.3 of Bloque4 (§5.3.2).
The theorem is proved in companion Paper [1] from Bałaban's explicit
activity bounds in [7] Eq (2.38), [8] §2.11–2.13, [9] §2, [10] §1.98–1.100,
via the audited notation bridge of Paper [2].

**Honest status**: AXIOM — not yet formalized in Lean.
Requires: abstract polymer gas definition, Kotecký–Preiss criterion,
activity bound extraction from Bałaban's 4D-gauge-theory CMP papers.
See BF-B in UNCONDITIONALITY_ROADMAP.md.
-/
axiom yangMills_ax_terminalKP_smallness :
    ∃ m_lat : LatticeMassProfile, HasTerminalKPSmallness m_lat

/--
**Axiom AF2** — Multiscale UV suppression.

Every lattice mass profile satisfying the terminal KP bound also satisfies
the multiscale UV suppression bound (exponential decay of the UV covariance
remainder sum over all RG scales).

**Paper correspondence**: Theorem 6.3 of Bloque4 (§6.3).
Proof structure:
  (i)  Multiscale telescoping identity (Prop 6.1) — law of total covariance.
  (ii) Single-scale UV error bound (Lem 6.2) — Bałaban propagator decay [4,5].
  (iii) Geometric series summation: ∑_j e^{-κ L^j} < ∞ for κ > 0, L > 1.

**Honest status**: AXIOM — not yet formalized in Lean.
Requires: formal σ-algebra tower on gauge-field configurations, conditional
covariance as a Lean object, random-walk Green's function bounds.
Items (ii) and (iii) are MEDIUM difficulty in Lean/Mathlib.
See BF-C in UNCONDITIONALITY_ROADMAP.md.
-/
axiom yangMills_ax_multiscaleUV_suppression :
    ∀ m_lat : LatticeMassProfile,
    HasTerminalKPSmallness m_lat → HasMultiscaleUVSuppression m_lat

/--
**Axiom AF3** — OS assembly: clustering + UV → continuum mass gap.

Every lattice mass profile satisfying both the terminal KP bound and the
multiscale UV suppression bound gives rise to a continuum mass gap via
the Osterwalder–Schrader reconstruction.

**Paper correspondence**: Theorem 7.1 (Mass Gap Bound) + Lemma 8.2
(exponential clustering ⟹ spectral gap) + Remark 8.6 (spectral gap
without full O(4) covariance) of Bloque4.

Proof sketch:
  (i)   Assembly (Thm 7.1): |Cov_{μ_η}(O(0), O(x))| ≤ C e^{-m|x|/a_*},
        m = min(m_*, c₀) > 0, uniform in η and L_phys.
  (ii)  OS2 (reflection positivity) via Osterwalder–Seiler [25]: positive
        transfer matrix T = e^{-H} with H = H* ≥ 0.
  (iii) Lem 8.2: OS4 (exponential clustering, = Thm 7.1 applied time-like) +
        OS2 ⟹ inf(σ(H) ∖ {0}) ≥ m > 0 (spectral gap).
  (iv)  Remark 8.6: full O(4) covariance (OS1) NOT needed for this step.
  (v)   Corollary 1.2: Δ_phys ≥ c_N Λ_YM > 0.

**Honest status**: AXIOM — not yet formalized in Lean.
Requires: OS reconstruction (Hilbert space, transfer matrix, vacuum Ω),
spectral theory for self-adjoint operators, and the GNS construction.
Mathlib has substantial spectral theory but lacks the gauge-field-specific
OS construction.
See BF-D in UNCONDITIONALITY_ROADMAP.md.
-/
axiom yangMills_ax_OSAssembly :
    ∀ m_lat : LatticeMassProfile,
    HasTerminalKPSmallness m_lat →
    HasMultiscaleUVSuppression m_lat →
    HasContinuumMassGap m_lat

end YangMills
