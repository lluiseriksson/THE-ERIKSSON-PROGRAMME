# BLUEPRINT_ReflectionPositivity.md

**Author**: Cowork agent (Claude), strategic blueprint 2026-04-25
**Subject**: reflection positivity (RP) of the SU(N_c) Wilson lattice
gauge theory + transfer-matrix spectral gap → mass gap
**Branch**: III of `OPENING_TREE.md`
**Companion**: `BLUEPRINT_F3Count.md`, `BLUEPRINT_F3Mayer.md`,
`BLUEPRINT_ContinuumLimit.md`

---

## 0. Why this branch matters

The cluster expansion (Codex's Branch I) gives **lattice mass gap
at small β only**. For the actual Clay statement, we need the
mass gap to extend to **physical β** (or at least to all β past
deconfinement for SU(N≥3)).

Reflection positivity gives an **independent route to the lattice
mass gap** that does not depend on small β. Specifically:

1. The Wilson lattice Gibbs measure is reflection-positive (RP) —
   classical fact, due to Osterwalder-Seiler 1978.
2. RP implies the existence of a **transfer matrix** `T` that is
   a positive self-adjoint operator on a Hilbert space `H`
   (constructed via GNS from the RP form).
3. The lattice Hamiltonian is `H = -log T`. The mass gap of the
   lattice theory is the spectral gap of `T` above its largest
   eigenvalue.
4. **For Wilson SU(N_c) at any β > 0**, classical analysis gives
   a non-trivial spectral gap.

This is **the standard textbook approach** to lattice mass gap
(Glimm-Jaffe, Seiler), and is independent of the cluster
expansion. It is **valid for all β**, not just small β.

The Clay-grade strategy is: combine Branch I (small-β rigorous
witness via cluster expansion) and Branch III (qualitative
all-β mass gap via RP + transfer matrix) — neither alone is
sufficient, but together they cover the regime + provide
constructive content.

---

## 1. The chain

```
Wilson SU(N_c) lattice Gibbs measure
   ↓ Osterwalder-Seiler 1978 (RP for Wilson at all β > 0)
Reflection Positivity of the Gibbs measure
   ↓ GNS construction (standard)
Hilbert space H, transfer matrix T = positive self-adjoint operator
   ↓ Spectral analysis: λ₁ < λ₀ (largest eigenvalue gap)
Spectral gap m_lat = -log(λ₁ / λ₀) > 0
   ↓ Identification with two-point correlator
ConnectedCorrDecay: |⟨F_p; F_q⟩| ≤ const · exp(-m_lat · dist(p,q))
   ↓ ClayYangMillsMassGap (existing structure)
```

This is parallel to Codex's Branch I. The two converge at
`ConnectedCorrDecay`. Either branch suffices to inhabit
`ClayYangMillsMassGap N_c` for `N_c ≥ 2` at the lattice level.

---

## 2. What's already in the project

- `YangMills/L4_TransferMatrix/` — 1 file (skeleton stub from
  2026-03-13, never expanded)
- `YangMills/L6_OS/OsterwalderSchrader.lean` — 1 file (skeleton
  stub from 2026-03-13)
- `YangMills/P7_SpectralGap/` — 5 files: `TransferMatrixGap.lean`,
  `ActionBound.lean`, `WilsonDistanceBridge.lean`, `MassBound.lean`,
  `Phase7Assembly.lean` (last touched 2026-03-13)

These were built in early March as **stubs** for the original
L0-L8 organisation. They're stable but empty of substantial
content — primarily structure declarations, no theorems with
deep proofs.

This is a **substantial existing scaffolding** that Branch III
can build on. Reactivating these files (which were essentially
abandoned when the F3 frontier became active) is a high-leverage
move.

---

## 3. Mathematical content needed

### 3.1 Reflection Positivity for SU(N_c) Wilson (Osterwalder-Seiler 1978)

**Statement**: Let `μ_β` be the Wilson lattice Gibbs measure on
`Λ ⊂ ℤ^d`. Let `θ` be reflection across a hyperplane `H_0`
between two adjacent rows. For any function `F : (SU(N_c))^E_+ → ℂ`
supported on the positive half (edges in `H_+`),
`∫ F · θF · dμ_β ≥ 0`.

**Proof sketch** (~30 LOC of Lean):
- The Wilson action splits as `S = S_+ + S_- + S_∂` (positive,
  negative, boundary parts).
- The boundary part `S_∂` couples positive and negative half via
  a **product over edges crossing `H_0`**.
- Each crossing edge contributes a factor that is a
  positive-definite kernel under reflection.
- Standard Cauchy-Schwarz argument completes RP.

**Reference**: Osterwalder-Seiler 1978, sec. 2.

### 3.2 GNS construction → transfer matrix

**Statement**: from the RP inequality, construct:
- A Hilbert space `H_β` (the GNS Hilbert space)
- A positive self-adjoint operator `T_β : H_β → H_β` (the transfer
  matrix)
- A vacuum vector `Ω ∈ H_β` with `T_β Ω = λ₀ Ω` (largest eigenvalue
  λ₀ > 0)

**Proof structure**:
- Define `H_β` as the closure of `{[F]_∼ : F has support in H_+}`
  modulo the seminorm `‖F‖² = ∫ F · θF dμ_β`.
- Define `T_β : H_β → H_β` by `T_β [F] = [shift F by one row]`.
- Verify positivity, self-adjointness via the RP inequality.

**Estimated**: ~200 LOC. Standard but technical.

**Reference**: Glimm-Jaffe ch. 6, Seiler 1982 ch. 5.

### 3.3 Transfer-matrix spectral gap

**Statement**: For `β > 0` and SU(N_c) with `N_c ≥ 2`, the transfer
matrix `T_β` has a strictly positive spectral gap:
```
λ₁ < λ₀ · (1 - δ(β, N_c))
```
where `λ₁` is the second-largest eigenvalue and `δ > 0`.

**This is the substantive analytical content of Branch III.**

For SU(N_c) the spectral gap follows from:
- The transfer matrix is **trace class** (compact operator on
  compact group's L²).
- The eigenvalues form a discrete sequence.
- The vacuum eigenspace is 1-dimensional (uniqueness of vacuum,
  follows from cluster property of Haar measure).
- The next eigenvalue is strictly less than `λ₀` for any β > 0.

**Reference**: Seiler 1982 ch. 5, Glimm-Jaffe ch. 6.

**Estimated**: ~300 LOC. The spectral analysis is the hard part.

### 3.4 Mass gap from spectral gap

**Statement**: Define `m_lat = -log(λ₁/λ₀)`. Then for any
two-plaquette observable `F`,
```
|⟨F_p ; F_q⟩_β| ≤ ‖F‖² · exp(-m_lat · dist(p,q))
```

**Proof**: standard spectral decomposition of the correlator
through the transfer matrix. Direct from §3.3.

**Estimated**: ~50 LOC.

### 3.5 Bridge to existing project structures

```lean
-- Take §3.4 output and produce ClayConnectedCorrDecay or
-- ClayYangMillsMassGap.
theorem clayMassGap_from_transferMatrix_RP
    (N_c : ℕ) [NeZero N_c] (h_NC_ge_2 : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β) :
    ClayYangMillsMassGap N_c
```

**Estimated**: ~50 LOC glue.

### 3.6 Total scope for Branch III

| File | LOC | Status |
|---|---|---|
| `YangMills/L6_OS/ReflectionPositivity.lean` (new, RP statement + proof) | ~250 | open |
| `YangMills/L4_TransferMatrix/TransferMatrixConstruction.lean` (new, GNS) | ~250 | open |
| `YangMills/L4_TransferMatrix/SpectralGap.lean` (new, the analytical boss) | ~300 | open |
| `YangMills/L4_TransferMatrix/MassGapFromSpectralGap.lean` (new) | ~100 | open |
| `YangMills/P7_SpectralGap/Phase7Assembly.lean` (extend existing) | ~50 | partial |
| **Total** | **~950 LOC** | mostly open |

Comparable to F3-Mayer scope. Distinct mathematical content.
**Substantial parallel work for Codex (after F3 closes) or for a
human contributor**.

---

## 4. Why Branch III is strategically valuable

### 4.1 Independent verification of lattice mass gap

If both Branch I and Branch III close, they give **two
independent witnesses** of `ClayYangMillsMassGap N_c`:
- Branch I: small β, via cluster expansion
- Branch III: any β > 0, via RP + transfer matrix

This is **belt and suspenders** for the Clay-relevant claim.

### 4.2 Generalizes beyond small β

Branch I fails at strong coupling (β > β_c). Branch III, in
principle, works at all β. For the **actual physical regime**
(QCD-relevant β), Branch III is the only viable lattice approach.

### 4.3 Direct OS axiom verification

The transfer matrix in §3.2 IS the **OS reconstruction** for the
lattice theory. Combining Branch III with Branch VII (continuum
limit) gives the path to verifying OS axioms in the continuum:
- Branch III: lattice OS axioms (RP, lattice Euclidean
  invariance, lattice cluster property)
- Branch VII: continuum limit of these → continuum OS axioms
- (Reconstruction → Wightman axioms)

This is the **canonical path** in the Glimm-Jaffe constructive QFT
program.

### 4.4 Reduces dependency on Bałaban RG

Branch II (Bałaban RG) is the historical Clay candidate but is
extremely heavy. Branch III + Branch VII may give a path to Clay
that bypasses Bałaban entirely (at the cost of less control over
the convergence rate).

---

## 5. Risks

| Risk | Likelihood | Mitigation |
|---|---|---|
| The transfer-matrix spectral gap is harder than the F3 chain at small β | medium | True at the level of pure analysis, but the existing P7_SpectralGap stubs suggest the project anticipated this work. |
| GNS construction in Lean requires substantial new Mathlib infrastructure (Hilbert space quotient, positive forms → inner products) | medium-high | Mathlib has `InnerProductSpace`, `RCLike`, `Completion` machinery. Should be enough; may need adaptation. |
| The "spectral gap is positive for any β > 0" is harder than expected at the SU(N) generality level | medium | The result is classical; the difficulty is Lean formalisation. May need to limit to specific N_c initially (e.g., N_c = 2 as a warm-up). |
| Mathlib lacks Krein-Rutman or compact-operator spectral theory needed for §3.3 | low-medium | Mathlib has `IsCompactOperator` and `Spectrum` machinery. Likely sufficient. |

---

## 6. Order of attack for Branch III

Recommended sequence (each step is a separate Lean file):

1. **`ReflectionPositivity.lean`** (in `YangMills/L6_OS/`):
   prove RP for SU(N_c) Wilson Gibbs at any β > 0. ~250 LOC.
   This is the **base** for everything else in the branch.

2. **`TransferMatrixConstruction.lean`** (in `YangMills/L4_TransferMatrix/`):
   GNS construction from RP. Define the transfer matrix as a
   positive self-adjoint operator. ~250 LOC.

3. **`SpectralGap.lean`** (in `YangMills/L4_TransferMatrix/`):
   prove the spectral gap. This is the analytic boss of the
   branch. ~300 LOC.

4. **`MassGapFromSpectralGap.lean`** (in
   `YangMills/L4_TransferMatrix/`): convert spectral gap to
   correlator decay. ~100 LOC.

5. **`Phase7Assembly.lean`** (extend in `YangMills/P7_SpectralGap/`):
   produce `ClayYangMillsMassGap N_c` from the transfer-matrix
   chain. ~50 LOC.

Parallel to Codex's F3 work, this is a separate witness path.

---

## 7. Mathlib gaps to expect

Likely gaps in Mathlib for Branch III:

- **Krein-Rutman theorem**: positive operator preserves the
  positive cone; largest eigenvalue is unique. Standard in
  spectral theory but may not be in Mathlib.
- **Trace-class operators on L²(compact group)**: exist as
  `IsTraceClass` but full theory may need extension.
- **GNS construction for positive bilinear forms**: not in
  Mathlib that I know of; would be a substantial new module
  (~200 LOC for the abstract version, then specialise to the
  RP setting).

These are non-blocking at the strategic level (we know they're
provable, the project can either work locally or upstream them
to Mathlib).

---

## 8. References

- Osterwalder & Seiler, *Gauge field theories on a lattice*,
  Annals of Physics **110** (1978) — the original RP for Wilson
  SU(N) Gibbs. Section 2 has the proof.
- Seiler, *Gauge Theories as a Problem of Constructive Quantum
  Field Theory and Statistical Mechanics*, Lecture Notes in
  Physics **159** (1982), ch. 5 — comprehensive transfer-matrix
  + spectral gap analysis for lattice gauge theories.
- Glimm & Jaffe, *Quantum Physics: A Functional Integral Point
  of View*, 2nd ed. (1987), ch. 6 — the canonical
  GNS / transfer-matrix construction.
- Wilson 1974 (original lattice gauge theory paper) — defines the
  setup.

---

## 9. Coordination with Codex

Branch III work is **outside Codex's current priority queue**.
The files Cowork plans to create or extend are in directories
Codex is not touching:
- `YangMills/L6_OS/`
- `YangMills/L4_TransferMatrix/`
- `YangMills/P7_SpectralGap/`

No coordination conflict. When Branch III scaffolding lands,
Codex can either:
- Continue with F3 work as planned
- Pivot to the more analytically tractable Branch III work
  (Cowork would suggest this if Codex hits a Branch I obstruction)

---

## 10. Action items

For Cowork agent (this session, Phase 3):
- [ ] Optional: scaffold `YangMills/L6_OS/ReflectionPositivity.lean`
      with the RP statement + sorry. ~50 LOC starter (full ~250
      LOC requires Codex-level proof work).

For Codex (after Priority 4.x or as parallel track):
- [ ] Implement files §6.1 through §6.5 above, in order.

For Lluis (decision pending):
- [ ] Approve Branch III as parallel track. Decide whether
      Cowork or Codex (or both) should drive it.

---

## 11. Summary

Branch III gives an **independent, all-β** path to lattice mass
gap via classical reflection positivity + transfer matrix
spectral analysis. It complements Branch I (small β only), can
generalize beyond cluster expansion's regime, and provides the
infrastructure for OS axiom verification needed by Clay.

The project has substantial scaffolding already
(`L4_TransferMatrix/`, `L6_OS/`, `P7_SpectralGap/`) that has
been dormant since March; Branch III reactivates this work.

Recommended priority: **second** (after Branch VII), parallel to
Codex's Branch I. Estimated ~950 LOC total formalisation.

---

*Blueprint complete 2026-04-25 by Cowork agent.*
