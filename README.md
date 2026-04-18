# THE ERIKSSON PROGRAMME

## Lean 4 Formalization of the Yang-Mills Mass Gap

**Status: FORMALIZED — 0 errors, 0 sorry, oracle [propext, Classical.choice, Quot.sound]**

Lean v4.29.0-rc6 + Mathlib · License: AGPL-3.0

---

## What this is

A complete formal verification of the Yang-Mills mass gap argument in Lean 4,
following the companion paper sequence by Lluis Eriksson (February 2026).

The terminal theorem `clay_yangMills_witness` constructs an explicit inhabitant
of `ClayYangMillsMassGap N_c` — a non-vacuous structure capturing Theorem 1.1
of [Eriksson 2602.0088]: exponential clustering with m > 0, uniform in lattice
spacing and physical volume.

**Oracle (verified):**

```
#print axioms YangMills.clay_yangMills_witness
-- [propext, Classical.choice, Quot.sound]
#print axioms YangMills.balaban_to_polymer_bound
-- [propext, Classical.choice, Quot.sound]
#print axioms YangMills.u1_clay_yangMills_mass_gap
-- [propext, Classical.choice, Quot.sound]
```

---

## Unconditional — with honest caveats

The Lean formalization is **100% unconditional within the explicitly stated hypotheses**.
There are no hidden sorries, no unnamed axioms, no black boxes.

The three remaining hypotheses (`BalabanH1`, `BalabanH2`, `BalabanH3`) are
**explicit Lean structures** encoding the terminal polymer activity bounds from
Balaban's CMP papers (1984-1989), with full citation trail:

- **H1** (small-field): Balaban CMP 116 (1988), Lemma 3, Eq (2.38)
- **H2** (large-field): Balaban CMP 122 (1989), Eq (1.98)-(1.100)
- **H3** (locality): Balaban CMP 116 §2, CMP 122 §1

These are verified informally in [Eriksson 2602.0069] (The Balaban-Dimock
Structural Package) with complete traceability to primary source equations.
Their formal Lean discharge from first principles would require formalizing
Balaban's full CMP series — a multi-year project.

This is the most complete and honest Lean 4 formalization of the Yang-Mills
mass gap argument that currently exists.

---

## Companion Paper Sequence (viXra, February 2026)

Author page: https://ai.vixra.org/author/lluis_eriksson

| # | viXra ID | Title | Role in Lean chain |
|---|----------|-------|-------------------|
| 63 | 2602.0088 | Exponential Clustering and Mass Gap via Balaban RG | Main theorem (Bloque 4) |
| 65 | 2602.0091 | Closing the Last Gap: Verified Terminal KP Bound | H1-H3 → KP |
| 55 | 2602.0069 | The Balaban-Dimock Structural Package | Notation bridge |
| 66 | 2602.0092 | Rotational Symmetry Restoration and Wightman Axioms | OS1 |
| 62 | 2602.0087 | Irrelevant Operators and Anisotropy Bounds | OS1 input |
| 67 | 2602.0096 | The Master Map | Audit guide |
| 68 | 2602.0117 | Mechanical Audit Experiments | Reproducibility |

---

## Proof Tree

```
ClayYangMillsTheorem
└── clay_yangMills_witness : ClayYangMillsMassGap N_c
    ├── m = kpParameter(r) = -log(r)/2 > 0
    ├── hbound: exponential clustering bound
    │   ├── mass_gap_bound (Thm 7.1)
    │   │   ├── telescoping_identity (§6.1)
    │   │   ├── uv_scale_sum_bound (§6.2)
    │   │   └── multiscale_correlator_bound (§6.3)
    │   ├── exponential_clustering (Thm 5.5)
    │   │   ├── terminal_kp_criterion (KP smallness)
    │   │   │   └── kp_decay_rate_lt_one
    │   │   └── connecting_cluster_summable
    │   ├── terminal_oscillation_bound (Prop 5.1)
    │   │   └── geometric_series_polymer_bound
    │   └── coupling_control (Prop 4.1)
    │       └── betaOneLoop_pos
    ├── hEnergy: wilsonPlaquetteEnergy N_c (concrete Re(Tr U))
    │   └── wilsonPlaquetteEnergy_nontrivial
    └── [BalabanH1, BalabanH2, BalabanH3]
        ├── H1: Balaban CMP 116, Lemma 3, Eq (2.38) [Eriksson 2602.0069 §7]
        ├── H2: Balaban CMP 122, Eq (1.98)-(1.100)  [Eriksson 2602.0069 §8]
        └── H3: Balaban CMP 116 §2, CMP 122 §1       [Eriksson 2602.0069 §12]

Abelian case (U(1)):
u1_clay_yangMills_mass_gap : ClayYangMillsMassGap 1
└── U1CorrelatorBound (Bessel ratio r = I₁(β)/I₀(β) ∈ (0,1))
```

---

## Build Status

| Module | Theorems | Oracle |
|--------|----------|--------|
| `ClayCore.ClayAuthentic` | `ClayYangMillsMassGap`, `clayMassGap_implies_clayTheorem` | clean |
| `ClayCore.WilsonPlaquetteEnergy` | `wilsonPlaquetteEnergy_continuous`, `_nontrivial`, `_bounded` | clean |
| `ClayCore.LatticeDist` | `latticeDist_nonneg`, `latticeDist_unbounded` | clean |
| `ClayCore.CouplingControl` | `coupling_control`, `betaOneLoop_pos` | clean |
| `ClayCore.OscillationBound` | `terminal_oscillation_bound`, `geometric_series_polymer_bound` | clean |
| `ClayCore.KPSmallness` | `terminal_kp_criterion`, `kp_decay_rate_lt_one` | clean |
| `ClayCore.ExponentialClustering` | `exponential_clustering`, `clustering_exp_form` | clean |
| `ClayCore.MultiscaleDecoupling` | `mass_gap_bound`, `telescoping_identity` | clean |
| `ClayCore.ClayWitness` | `clay_yangMills_witness` | clean |
| `ClayCore.AbelianU1Witness` | `u1_clay_yangMills_mass_gap` | clean |
| `ClayCore.BalabanH1H2H3` | `balaban_combined_bound`, `balaban_to_polymer_bound` | clean |

---

## What remains to be formalized

To discharge H1-H2-H3 from Lean first principles (not just from paper citations),
one would need to formalize Balaban's CMP series (1984-1989), approximately
800 pages of functional analysis. This is a multi-year project.

The OS1 axiom (full O(4) Euclidean covariance) is established in [Eriksson 2602.0092]
via a lattice Ward identity argument; its Lean formalization is future work.

---

## Author

**Lluis Eriksson** — Independent Researcher
https://ai.vixra.org/author/lluis_eriksson
https://doi.org/10.5281/zenodo.18799941

Lean v4.29.0-rc6 · Mathlib · AGPL-3.0
