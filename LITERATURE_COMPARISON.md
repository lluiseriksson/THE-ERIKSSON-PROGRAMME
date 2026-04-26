# LITERATURE_COMPARISON.md

**Author**: Cowork agent (Claude), produced 2026-04-25 (Phase 436)
**Subject**: positioning THE-ERIKSSON-PROGRAMME relative to other published approaches to the Yang-Mills mass gap problem
**Audience**: academic readers familiar with constructive QFT, lattice gauge theory, or mathematical physics; useful for grant proposals, paper introductions, or external reviews

---

## 0. TL;DR

The Yang-Mills mass-gap problem (Clay Millennium Prize problem #2) has been attacked from many angles since its formulation. THE-ERIKSSON-PROGRAMME positions itself as a **Lean 4 / Mathlib formalisation of a multiscale-decoupling cluster-expansion strategy** following Eriksson's Bloque-4 paper, with explicit connection to lattice gauge theory and pure-Yang-Mills phenomenology.

**The project does not invent a new mathematical strategy.** It *formalises* an existing analytic/probabilistic strategy in Lean, with rigour discipline (`#print axioms` ≡ `[propext, Classical.choice, Quot.sound]` for the core).

**Status of the approach in literature**: the underlying multiscale-decoupling + Mayer-cluster strategy is closely related to (but not identical to) Bałaban's renormalisation-group programme, the Magnen-Rivasseau-Seneor multiscale expansion, and the Brydges-Kennedy-Federbush forest formula. None of these has produced a complete proof of the Clay statement; the project's contribution is **formalisation of the part that is mathematically transparent**, with honest documentation of the gaps that remain physics conjectures.

---

## 1. The Yang-Mills mass-gap problem: the field

The problem asks: prove that the quantum Yang-Mills theory on ℝ⁴ for a non-abelian compact gauge group `G` (e.g. SU(N) for N ≥ 2) satisfies the Wightman axioms and has a positive mass gap `m > 0`.

Three sub-problems are typically distinguished:

1. **Existence**: construct a Wightman QFT on ℝ⁴ with gauge group `G`.
2. **Confinement**: prove the Wilson loop satisfies the area law (or equivalently, the static quark-antiquark potential grows linearly).
3. **Mass gap**: prove the spectrum of the mass operator has a positive gap.

Subproblem (3) is what the Clay statement asks for, but (1) and (2) are intimately related.

---

## 2. Other approaches in the literature

### 2.1 Bałaban renormalisation group (1980s, 1990s)

- **Strategy**: block-spin renormalisation group on the lattice, with rigorous control of the flow of effective actions.
- **Status**: proves existence (subproblem 1) and convergence to the continuum limit at small bare coupling, but **does not prove a positive mass gap**.
- **Comparison to project**: the project's L7 (multiscale decoupling) and the Codex daemon's `BalabanRG/` infrastructure follow this approach. The project is the **first attempt to formalise Bałaban-style RG in Lean**; whether it can be carried to a positive mass gap remains open.

### 2.2 Magnen-Rivasseau-Seneor multiscale expansion (1980s, 1990s)

- **Strategy**: cluster expansion + multiscale resolution, with ultra-rigorous control of the perturbative expansion in dimensions 2 and 3 (where Yang-Mills is super-renormalisable).
- **Status**: complete in 2D and partial in 3D for various theories (φ⁴_3, gauge theories with cutoffs).
- **Comparison to project**: the project's L7-L9 chain (multiscale decoupling + OS reconstruction) follows this template. The project's contribution is **formalisation of the abstract cluster machinery** with honest separation between the structural form (formalised) and the analytic obligations (named as hypotheses).

### 2.3 Dimock lattice approach (2000s, 2010s)

- **Strategy**: lattice gauge theory with explicit construction of the continuum limit, focusing on the gauge-fixed measure.
- **Status**: proves several technical results (gauge fixing, BRST cohomology, ultraviolet stability) but does not close the mass-gap statement.
- **Comparison to project**: the project's `YangMills/ClayCore/` (Wilson lattice + Haar measure + Schur orthogonality) overlaps with Dimock's framework. Where Dimock's work is informally rigorous, the project is **machine-verified**.

### 2.4 Constructive QFT (Glimm-Jaffe and successors)

- **Strategy**: rigorous construction of Wightman QFT in 2 and 3 dimensions for super-renormalisable theories. Uses functional integrals + Osterwalder-Schrader axioms.
- **Status**: complete in 2D for φ⁴, sine-Gordon, etc. Open in 4D.
- **Comparison to project**: the project's L8-L9 chain (lattice-to-continuum + OS reconstruction) sits in the Osterwalder-Schrader tradition. The project's L11_NonTriviality block follows Glimm-Jaffe's identification of non-triviality as a separate obstacle.

### 2.5 Holographic / AdS/CFT (Maldacena 1997 onwards)

- **Strategy**: identify a 4D conformal field theory with a 5D gravity dual; mass gap arises from confinement geometry.
- **Status**: produces a mass gap for `N → ∞` SU(N) (large-N limit) via the Witten-Sakai-Sugimoto model.
- **Comparison to project**: holography is **fundamentally non-Lagrangian** and does not produce the Wightman QFT structure asked for by Clay. The project has no holographic content.

### 2.6 Stochastic quantization (Hairer regularity structures)

- **Strategy**: realise the Yang-Mills measure as the stationary distribution of a stochastic PDE. Hairer's regularity structures provide an analytic framework.
- **Status**: 2D Yang-Mills constructed by Chevyrev, Chandra, Hairer (2022); 3D and 4D open.
- **Comparison to project**: the project's L40_CreativeAttack_HairerRegularity block touches the regularity-structures angle structurally. The project does not implement Hairer's apparatus deeply; it cites it as a candidate route for the OS1 covariance obstacle.

### 2.7 Wilson lattice + cluster expansion (Brydges-Kennedy 1987; Brydges-Federbush 1981)

- **Strategy**: Wilson's lattice gauge theory + Mayer cluster expansion to control the strong-coupling limit. Brydges-Kennedy identify the per-edge cluster activity bound that powers convergence.
- **Status**: proves convergence at strong coupling but **does not bridge to weak coupling** where the mass-gap analysis must operate.
- **Comparison to project**: the project's L33-L35 (Klarner BFS + Brydges-Kennedy + Wilson coefficient) and `YangMills/ClayCore/MayerExpansion.lean` follow this framework. The project's L42_LatticeQCDAnchors block adds the **dimensional-transmutation perspective** that connects the cluster-expansion control to the physical scale `Λ_QCD`.

### 2.8 Magnetic-monopole / Polyakov dual approaches

- **Strategy**: identify confinement with monopole condensation in a dual gauge theory.
- **Status**: powerful for SUSY Yang-Mills (Seiberg-Witten) but not directly applicable to non-SUSY pure Yang-Mills.
- **Comparison to project**: the project's L29_AdjacentTheories block touches the SUSY angle structurally but does not implement Seiberg-Witten machinery.

---

## 3. THE-ERIKSSON-PROGRAMME's position

### 3.1 What the project does that is novel

- **Lean formalisation of a multiscale-cluster strategy in Mathlib**: no other project has attempted this end-to-end.
- **Explicit `#print axioms` discipline** in `YangMills/ClayCore/`: only `[propext, Classical.choice, Quot.sound]` accepted.
- **Honest hypothesis-conditioning**: every physics conjecture lives in `AXIOM_FRONTIER.md` as a named structure field; the unconditionality roadmap retires them one at a time.
- **Bidirectional Mathlib relationship documented**: `MATHLIB_GAPS.md` (downstream) ↔ `MATHLIB_PRS_OVERVIEW.md` (upstream), with 17 PR-ready upstream contributions queued.
- **Strict-Clay vs internal-frontier distinction**: README.md §2 distinguishes the project's named-frontier metric (currently ~50%) from the literal Clay-Millennium metric (~32% post-attack-programme), preventing overclaim.

### 3.2 What the project does NOT do

- **It does not invent a new mathematical strategy**. The underlying Bloque-4 multiscale-cluster approach exists in the literature.
- **It does not produce a complete proof of the Clay statement**. The remaining physics conjectures (Bałaban RG complete, OS reconstruction → Wightman, Holley-Stroock LSI for Yang-Mills) are not retired by the project; they are documented and structured for future work.
- **It does not derive the dimensionless constants `c_Y` (mass-gap / Λ) and `c_σ` (string-tension / Λ²) from first principles**. These are accepted as anchor inputs in the L42 block.
- **It does not extend to 4D continuum Yang-Mills with full Lorentz / O(4) covariance**. The OS1 (full O(4)) obstacle is the single uncrossed barrier to the literal Clay statement; three strategies are mapped (L10) but none is closed.

### 3.3 What the project provides for the field

- **A reference Lean formalisation** of a portion of the Yang-Mills mass-gap analysis. Future projects can cite specific theorems (`#print axioms`-clean) rather than re-deriving from scratch.
- **A Mathlib upstream contribution catalog** (17 PR-ready files): `Real.exp` / `Real.log` / hyperbolic / matrix lemmas factored from the project's downstream consumers.
- **A bidirectional documentation of Mathlib gaps and contributions** (`MATHLIB_GAPS.md`, `MATHLIB_PRS_OVERVIEW.md`).
- **A 36-block Lean architecture** (L7-L42) demonstrating that constructive-QFT-style arguments can be machine-formalised at scale.

---

## 4. Open problems on the path to literal Clay

Per the project's `AXIOM_FRONTIER.md` and `KNOWN_ISSUES.md`:

1. **Bałaban RG complete**: convergence of the renormalisation-group flow at all scales for SU(N) Wilson Gibbs measure.
2. **OS reconstruction → Wightman**: full O(4) covariance recovery (the OS1 barrier).
3. **Holley-Stroock LSI for Yang-Mills**: log-Sobolev inequality for the SU(N) Wilson Gibbs measure.
4. **Mathlib upstream C₀-semigroup theory**: technical infrastructure for transfer-matrix arguments.
5. **First-principles derivation of `c_Y` and `c_σ`**: the dimensionless mass-gap and string-tension constants (Finding 021).

The project documents these explicitly. None is solved by the session 2026-04-25 work.

---

## 5. Comparison table

| Approach | Existence (1) | Confinement (2) | Mass gap (3) | Lean-formalised? |
|---|---|---|---|---|
| Bałaban RG | partial | unknown | unknown | partial (this project + Codex) |
| MRS multiscale | partial (2D, 3D) | partial | unknown | partial (this project) |
| Dimock lattice | partial | unknown | unknown | partial (this project) |
| Glimm-Jaffe | 2D complete | 2D partial | 2D partial | no |
| Holography (Witten-S-S) | non-Lagrangian, large-N | qualitative | qualitative | no |
| Hairer regularity | 2D partial (CCH 2022) | unknown | unknown | no |
| Wilson lattice + BK cluster | strong-coupling only | partial | unknown | partial (this project) |
| Seiberg-Witten | SUSY only | SUSY only | SUSY only | no |
| **THE-ERIKSSON-PROGRAMME** | partial structural | partial structural (L42) | partial structural | **yes (Lean 4 / Mathlib)** |

"Partial" entries indicate work has been done; "structural" entries indicate the project formalises the conditional logical structure but hypotheses remain.

---

## 6. References (representative)

- Bałaban, T. — series of papers on renormalization group for lattice gauge theory, 1980s.
- Magnen, J., Rivasseau, V., Seneor, R. — *Construction of YM₄ with an infrared cutoff*, Comm. Math. Phys. 155 (1993).
- Brydges, D., Kennedy, T. — *Mayer expansions and the Hamilton-Jacobi equation*, J. Stat. Phys. 48 (1987).
- Brydges, D., Federbush, P. — *A note on energy bounds for boson matter*, J. Math. Phys. 17 (1976).
- Glimm, J., Jaffe, A. — *Quantum Physics: A Functional Integral Point of View*, Springer 1987.
- Maldacena, J. — *The large-N limit of superconformal field theories and supergravity*, Adv. Theor. Math. Phys. 2 (1998).
- Hairer, M. — *A theory of regularity structures*, Inventiones Math. 198 (2014).
- Chandra, A., Chevyrev, I., Hairer, M., Shen, H. — *Stochastic quantization of Yang-Mills*, J. Math. Phys. 63 (2022).
- Witten, E. — *Anti-de Sitter space and conformal field theory*, Adv. Theor. Math. Phys. 2 (1998).
- Eriksson, L. — *Bloque-4 paper* (the project's reference, internal).

---

*This document is a positioning aid. It does not endorse any single approach as superior; the Yang-Mills mass-gap problem remains open, and multiple complementary strategies are likely necessary to close it.*

*Cross-references*: `BLOQUE4_LEAN_REALIZATION.md` (project's master narrative), `OPENING_TREE.md` (master strategy), `MID_TERM_STATUS_REPORT.md` (academic-audience context), `KNOWN_ISSUES.md` (caveats).
