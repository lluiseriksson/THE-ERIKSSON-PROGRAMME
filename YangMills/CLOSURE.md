# Yang–Mills Programme — Archival Closure & 2027 Handoff Guide

**Archival date:** 2026-11-22  
**Archival release tag:** `yang-mills-archive-v1.0`  
**Canonical Lean core contract:** [`project-state.json`](../project-state.json)  
**Citation metadata:** [`CITATION.cff`](../CITATION.cff) · [`.zenodo.json`](../.zenodo.json)  
**Companion preprint archive:** [airr.science](https://airr.science/)

---

## 1. Purpose of this archival closure

This document closes the active exploratory phase of the **Yang–Mills** formalization inside **The Eriksson Programme** in a clean, citable, and directly resumable form for mathematical physicists, formal-verification researchers, and next-generation automated theorem provers.

Every claim in this archive adheres to the repository's strict epistemic boundary:

* **Verified core (`YangMillsCore`):** compiles in GitHub Actions (`.github/workflows/lean-build.yml` + `.github/workflows/ci.yml`) against pinned Lean `v4.29.0-rc6` and pinned Mathlib `07642720480157414db592fa85b626dafb71355b`, with **zero `sorry`**, **zero project-specific axioms**, and every headline `#print axioms` readout in `oracle_check.lean` restricted to `[propext, Classical.choice, Quot.sound]`.
* **Honest Clay scope:** **no four-dimensional continuum limit, no Osterwalder–Schrader / Wightman reconstruction, and no Clay Millennium Prize solution is claimed.** The repository's historical Clay-distance shorthand remains **~0% (<0.1%)**.

---

## 2. What is proved and reusable today (verified core & standalone results)

Researchers or provers resuming this work do **not** need to rebuild the following layers from scratch:

| Layer / Module | Verified Scope | Primary Entry Points |
|---|---|---|
| **KP / Mayer polymer engine** | Mayer–Ursell inversion ($\Xi = \exp(\text{clusterSum})$), Penrose tree-graph inequality, polymer reconstruction $Z = \Xi$, Kotecký–Preiss convergence, and zero-free polydiscs. | [`YangMills/KP/`](KP/), [`YangMillsCore.lean`](../YangMillsCore.lean) |
| **Strong-coupling Wilson-loop area laws & IR clustering** | Finite-volume and volume-uniform Wilson-loop area laws (linearized and exact activity); unconditional exponential decay of truncated plaquette correlations for $\mathrm{SU}(N)$ in an explicit non-empty strong-coupling window **without Peter–Weyl**; fixed-spacing thermodynamic limit on integer coordinates. | [`YangMills/L1_GibbsMeasure/`](L1_GibbsMeasure/), [`paper/area-law/`](../paper/area-law/) |
| **$\mathrm{SU}(N)$ / $\mathrm{U}(1)$ Haar & centre symmetry** | Exact centre-symmetry vanishing engine, $N$-ality selection rules for interacting Wilson loops at any coupling $\beta$, fundamental Schur orthogonality, $\mathrm{U}(1)$ character orthogonality, and explicit certification of $\mathrm{SU}(1)$ degeneracy. | [`YangMills/ClayCore/`](ClayCore/) (see [`CLAY_CORE_STATUS.md`](ClayCore/CLAY_CORE_STATUS.md)) |
| **Source-grounded conditional RG substrates** | Block-spin averaging with gauge covariance and $\ell^2$ contraction, Gaussian pushforwards, exponential-decay kernel calculus, marginal-coupling 4D summability (`MarginalUVMassGap.lean`), error-budget adapters (`YMActivityBudget`), and certified obstruction theorems (volume-uniform Poincaré walls, flat lattice Hodge rank walls). | [`YangMills/RG/`](RG/), [`YangMills/Paper/`](Paper/) |
| **Modified Bessel / Amos ratio calculus & 2D surface monotonicity** | Machine-checked Amos-type bounds (integer and real order), crossing classification, Turán-type monotonicity, Wronskian reduction, and global ratio monotonicity for killed von Mises bridges. | [`AmosClosure/`](../AmosClosure/), [`MarkedRootedClosure/`](../MarkedRootedClosure/), [`papers/surface-complete/`](../papers/surface-complete/) |
| **Lattice reflection positivity & transfer-operator chains ($\mathbb{Z}_2$ / $\mathbb{Z}_N$)** | Complete machine-checked Osterwalder–Seiler chain for the $\mathbb{Z}_2$ lattice gauge chain, GNS quotient with degenerate reflection pairings, Perron theorem for strictly positive kernels, spatial coupling obstructions, and congruence spectrum rigidity. | [`YangMills/OS/`](OS/) |
| **Finite $\mathrm{SU}(2)$ Wilson cylinder (R1/R2, Sept 2026)** | Four-vertex, six-link, two-plaquette $\mathrm{SU}(2)$ cylinder geometry, normalized product-Haar Gibbs measure, and exact reflection/Fubini identities (outside `YangMillsCore`; positivity and transfer remain open). | [`docs/evidence/physical-cylinder-r2-20260906/README.md`](../docs/evidence/physical-cylinder-r2-20260906/README.md) |

---

## 3. Open frontiers — exact resumption map for future work

Anyone continuing this programme should start from [`HORIZON.md`](../HORIZON.md) and [`HYPOTHESIS_FRONTIER.md`](../HYPOTHESIS_FRONTIER.md). The three major open fronts are:

1. **Physical UV activity estimate (`hRpoly`) — frozen in [draft PR #29](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/29):**
   * *What is missing:* Uniform physical `(B0, delta0)` decay bounds and regional transport (F5) for the actual Balaban/Dimock gauge RG operator (cluster expansion with holes).
   * *Frozen checkpoint:* 20/41 terminal `PreEq136` producers recorded; `TermSource = 0`; physical window 15 compatible but not attained. See [`docs/HRPOLY-STATUS.md`](../docs/HRPOLY-STATUS.md).
2. **Physical $\mathrm{SU}(N)$ reflection positivity and transfer-operator gap at fixed spacing:**
   * *What is missing:* Extending R1/R2 finite-cylinder geometry/measure to genuine complex Gram-matrix positivity with all crossing plaquette weights, a strictly positive centered norm, and a transfer-operator spectral gap for $\mathrm{SU}(2)$ and general $\mathrm{SU}(N)$.
   * *Entry audit:* [`docs/POST-HRPOLY-CONTINUUM-AUDIT-20260906.md`](../docs/POST-HRPOLY-CONTINUUM-AUDIT-20260906.md).
3. **Four-dimensional continuum limit ($a \to 0$) and OS/Wightman reconstruction (M4–M5, the literal Clay problem):**
   * *What is missing:* Full constructive 4D continuum QFT construction, non-perturbative IR mass gap surviving $a \to 0$, and Osterwalder–Schrader / Wightman reconstruction in Lean 4 / Mathlib.
4. **Open late-2026 research branches preserved on GitHub (not merged into `YangMillsCore`):**
   * Flat lattice Hodge / concentric integer-shell energy bounds & obstructions: PRs `#180`, `#181`, `#182`, `#187`, `#188`, `#189`, `#190` (Nov 2026).
   * Boolean Doob chain retention / stationary tail criteria: PRs `#292`, `#299` (Nov 2026).
   * External companion/satellite repositories (AQFT split-inclusion series & numerical bridge oracles): [`aqft-split-inclusion-series`](https://github.com/lluiseriksson/aqft-split-inclusion-series), [`ym-lattice-numerics`](https://github.com/lluiseriksson/ym-lattice-numerics), and the satellite fleet cataloged in [`SATELLITES.md`](../SATELLITES.md).

---

## 4. Curated catalog of Yang–Mills & mathematical-physics manuscripts

> **Repository scope note (November 2026):** In mid-November 2026, several unrelated empirical/audit manuscripts (e.g., `caidp-rank-sensitivity`, `neso-price-order`, `nyc-zoning-event-dates`, `mangrove-monitoring`, `phoenix-peak-coincidence`, `acquisition-cost-certificates`, `capital-source-omissions`, `prompt-order-certificates`) were added under `papers/` in this repository. They are **not** part of the Yang–Mills programme. The table below isolates the **Yang–Mills and mathematical-physics corpus**.

### A. Core Lattice Gauge Theory, Cluster Expansions & RG Obstructions (5 compiled PDFs)
* [`paper/area-law/`](../paper/area-law/) — *A Machine-Checked Volume-Uniform Wilson-Loop Area Law via a Formalized Cluster Expansion*
* [`papers/c1-rooted-tree-majorants/`](../papers/c1-rooted-tree-majorants/) — *Machine-checked rooted-tree majorants for polymer expansions with holes*
* [`papers/c6-rg-interface/`](../papers/c6-rg-interface/) — *A Mechanized, Non-Circular Renormalization-Group Interface for Wilson Lattice Gauge Correlators*
* [`papers/poincare-wall/`](../papers/poincare-wall/) — *The Volume-Uniform Poincaré Walls: Machine-Checked Obstructions for Flat and Fluctuation-Sector Block-Poincaré Routes to Combes–Thomas Coercivity in Lattice Yang–Mills*
* [`papers/flat-coarse-rank/`](../papers/flat-coarse-rank/) — *Coarse information and finite rank obstructions for flat lattice Hodge forms* (expanded revision dossier; see `papers/flat-coarse-rank/README.md` for exact formal anchor split)

### B. Modified Bessel / Amos Bounds & 2D Surface Expansion Suite (9 compiled PDFs)
* [`papers/bessel-amos-fh/`](../papers/bessel-amos-fh/) — *An Elementary Recurrence–Amos Proof of the Unit-Step Order-Monotonicity of $(\log I_\nu)'$, with a Feynman–Hellmann Application to 2D LGT*
* [`papers/c2-amos-closure/`](../papers/c2-amos-closure/) — *One Amos bound, three consumer sites: machine-checked Bessel-ratio calculus for lattice gauge expansions*
* [`papers/c3-amos-proof/`](../papers/c3-amos-proof/) — *A machine-checked proof of the Amos bound for modified Bessel function ratios*
* [`papers/c4-amos-real/`](../papers/c4-amos-real/) — *A machine-checked proof of an Amos-type bound for modified Bessel ratios at real order*
* [`papers/c5-crossing/`](../papers/c5-crossing/) — *The diagonal Amos-type family at real order: a machine-checked quantitative crossing classification*
* [`papers/phi-lemma/`](../papers/phi-lemma/) — *A Weighted Turán-Type Monotonicity Lemma for Modified Bessel Functions via the Calibrated Amos Bound*
* [`papers/surface-theorem/`](../papers/surface-theorem/) — *Ratio Monotonicity for a Killed von Mises Bridge: exact bridge structure, certified negative results, a single-Bessel reduction, and a two-scale closure map*
* [`papers/surface-complete/`](../papers/surface-complete/) — *Global Ratio Monotonicity for a Killed von Mises Bridge*
* [`papers/wronskian-reduction/`](../papers/wronskian-reduction/) — *A Wronskian Identity for Antisymmetrized Sine Sums*

### C. Reflection Positivity, Osterwalder–Seiler Chains & Transfer Operators (13 compiled PDFs)
* [`papers/o-bridge/`](../papers/o-bridge/) — *Clustering and the Transfer-Operator Gap: A Machine-Checked Dense-Family Criterion*
* [`papers/reflection-positivity/`](../papers/reflection-positivity/) — *A Machine-Checked Reflection-Positivity Framework for $\mathbb{Z}_N$ Lattice Gauge Theory, with the $\mathbb{Z}_2$ Wilson Instance*
* [`papers/os-chain-z2/`](../papers/os-chain-z2/) — *From the Gibbs Weight to the Spectral Gap: A Complete Machine-Checked Osterwalder–Seiler Chain for the $\mathbb{Z}_2$ Lattice Gauge Chain*
* [`papers/os-quotient/`](../papers/os-quotient/) — *The Quotient That Is Not the Identity: A Machine-Checked Degenerate Reflection Pairing and Its GNS Quotient*
* [`papers/perron-kernel/`](../papers/perron-kernel/) — *The Vacuum Was Never Absent: A Machine-Checked Perron Theorem for Strictly Positive Kernels*
* [`papers/perron-gap/`](../papers/perron-gap/) — *Strict but Not Uniform: a Machine-Checked Spectral Gap at Every Finite Extent of the Coupled Slice*
* [`papers/spatial-extent/`](../papers/spatial-extent/) — *Where the Elementary Reconstruction Stops: Spatial Coupling Breaks the Uniform Vacuum, Machine-Checked*
* [`papers/spatial-birkhoff/`](../papers/spatial-birkhoff/) — *Blind to the Coupling: a Second Machine-Checked Obstruction at Spatial Extent*
* [`papers/spatial-gibbs/`](../papers/spatial-gibbs/) — *The Measure the Spectral Results Were About: a Machine-Checked Transfer Bridge for the Spatial $\mathbb{Z}_2$ Slice*
* [`papers/spatial-reflection/`](../papers/spatial-reflection/) — *The Weight That Could Not Break It: Machine-Checked Endpoint Reflection Positivity for the Coupled $\mathbb{Z}_2$ Slice*
* [`papers/spatial-os/`](../papers/spatial-os/) — *The Collapse: Machine-Checked Bond Reflection Positivity and a Site Reflection Form for the Coupled $\mathbb{Z}_2$ Slice*
* [`papers/spatial-spectral/`](../papers/spatial-spectral/) — *The Modulus: a Machine-Checked Operator Bound on the Fluctuation Sector of the Coupled $\mathbb{Z}_2$ Slice*
* [`papers/spatial-uniform/`](../papers/spatial-uniform/) — *The Rate Without the Extent: a Machine-Checked Extent-Independent Spectral Rate for the Decoupled $\mathbb{Z}_2$ Slice*
* [`papers/congruence-spectrum/`](../papers/congruence-spectrum/) — *Congruence Rigidity and the Fusion Bound: what a positive weight can and cannot do to the spectrum of a transfer kernel*

### D. Decoupling, Boolean Doob Kernels & Supporting Dossiers (1 PDF + TeX/audit dossiers)
* [`papers/parity-barriers/`](../papers/parity-barriers/) — *Parity Barriers for Decoupling Inequalities* (PDF + TeX)
* [`papers/stationary-doob347/`](../papers/stationary-doob347/) — *Stationary marginals and bottleneck restrictions for Boolean Doob kernels* (TeX dossier)
* [`papers/stationary-weighting354/`](../papers/stationary-weighting354/) — *Stationary-to-weighting moment transfer and spectral rigidity for Boolean Doob kernels* (TeX dossier)
* [`papers/marginal-transfer/`](../papers/marginal-transfer/) — multi-file TeX workspace and audit snapshots
* [`papers/su2-crossing-compensated/`](../papers/su2-crossing-compensated/) — $\mathrm{SU}(2)$ crossing differential descent audit & source bundle
* [`papers/thermodynamic-limit-kp/`](../papers/thermodynamic-limit-kp/) — paper generator script (`generate_paper.py`)

---

## 5. Reproducing and citing this archive

### Clone and verify locally

On **Windows**, enable long paths during clone (nested historical audit paths under `papers/marginal-transfer/` exceed the 260-character legacy MAX\_PATH limit):

```bash
git clone -c core.longpaths=true https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git
cd THE-ERIKSSON-PROGRAMME
lake exe cache get
lake build YangMillsCore
lake env lean oracle_check.lean
python scripts/check_consistency.py
```

Full pin and verification instructions live in [`REPRODUCIBILITY.md`](../REPRODUCIBILITY.md).

### How to cite

Use GitHub's *Cite this repository* button (backed by [`CITATION.cff`](../CITATION.cff)) or the BibTeX entry below:

```bibtex
@software{eriksson_2026_yangmills_archive,
  author       = {Eriksson, Lluis},
  title        = {The Eriksson Programme: Machine-Checked Lattice Yang--Mills Foundations and Open Frontier in Lean 4},
  year         = {2026},
  month        = nov,
  version      = {yang-mills-archive-v1.0},
  url          = {https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/tree/main/YangMills},
  license      = {AGPL-3.0-or-later}
}
```
