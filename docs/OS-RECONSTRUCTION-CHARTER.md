# OS-R CHARTER — volume-uniform machine-checked OS reconstruction [REGISTERED]

Registered 2026-08-04 on branch d3-closure (hash in the registering
commit's first line).  Chosen by the owner from the 28-paper idea sweep
(ledger Add. 607): the 6.5-band low-risk composition.  Judges (§5) must
PASS on the sanctioned plane before any fabrication.

## 0. Target and honesty frame

TARGET THEOREM (os_reconstruction_uniform_gap, name provisional): for
all β, γ with 0 < α < 1 and 2·tanh|β| + 2·tanh|γ| ≤ α, with β ≥ 0
(reflection positivity's half-plane), there exists ONE m > 0 such that
for EVERY spatial extent L and every depth:
  (i)   the OS pairing of half-strip observables is positive
        semidefinite (papers 12/13, existing theorems);
  (ii)  the physical Hilbert space = boundary vectors with the site
        form = the GNS quotient by the null space (paper 14, existing:
        physicalEquiv, mem_ker_collapseL_iff);
  (iii) the forced transfer operator T_L (paper 14, existing:
        transferOp_unique) with its Perron normalisation carries
        VacuumTransfer data, and
  (iv)  ‖projected (T_L/λ_L)‖ ≤ e^{−m}, the SAME m for every L —
        via unitary transport onto the operator D-6 already bounds;
  (v)   consequently every reconstructed connected correlator of
        half-strip observables decays at rate e^{−m}, uniformly in L,
        with per-observable constants (n-step identification against
        the MEASURE, so the statement is about Gibbs expectations, not
        about a form standing in for them).

External claim (to be collated before ink): first machine-checked OS
reconstruction in any prover.  Internal honesty: the internal headline
is already spent (os-chain-z2 did the complete chain at extent zero);
this campaign's delta is SPATIAL EXTENT + VOLUME UNIFORMITY + the D-6
feed.  Mathematics: classical (Osterwalder–Seiler 1978, FILS 1978); the
value is mechanization + the volume-uniform composition.

Non-goals: no thermodynamic limit (that is D-7, unchartered), no
Hamiltonian/functional calculus, no continuum, no Z_N (N>2), no YM
consequence.  Importance is not inherited by proximity.

## 1. The alignment discovered at design time (grounded in the files)

Read from the sources on 2026-08-04 (not from memory — memory had the
site-form weight WRONG, it is 1/w not w):

- Site form (SpatialReconstruction.siteForm): ⟨u,v⟩_site carries the
  weight 1/w (the shared slice's weight is double-counted by the two
  halves and divided out once).  Bond form carries the bare temporal
  kernel K = spatialKernel β.
- Forced operator: (T v)(σ) = w σ · Σ_τ K(σ,τ) v(τ)  (= D_w K).
- THE UNITARY: Q : Euclidean → site, (Q u) = √w · u.  Then
  ⟨Qu, Qv⟩_site = ⟨u,v⟩_eucl exactly, and Q⁻¹ ∘ T ∘ Q = √w·K·√w = the
  S-lane symmetrised kernel S_w.
- THE FEED: DobrushinTilt.tiltKernel w β lam = symWeighted w β / lam,
  i.e. D-6's corollary (dobrushin_ising_uniform_gap, DobrushinCorollary
  :700) bounds ‖projectedTransfer (opOf (S_w/λ)) (vacOf Om)‖ ≤ e^{−m}
  for w = sliceW γ L on slices Fin (L+1) → Fin 2, ∀L, ONE m.  The
  operator D-6 bounds IS the unitary transport of T_L/λ_L.  No spectral
  transport theorem, no diagonal-similarity argument, no complexified
  norm theory is needed for (iv): one unitary, one instance.
- Slice-type alignment: papers 12/13/14 quantify over arbitrary slice
  count L' and arbitrary positive w; instantiate L' := L+1,
  w := sliceW γ L.  Domain overlap: the window ∩ {β ≥ 0} is nonempty
  (β = γ = 0.2 gives 2tanh+2tanh ≈ 0.790 ≤ 0.8 < 1) — non-vacuity
  witness, judged in G6.
- ℝ/ℂ boundary: D-6's side is EuclideanSpace ℝ; the OS forms are ℂ.
  Route chosen (cheapest honest one): state (iv) on the real side via
  the transport, and derive (v) for complex observables by splitting
  into real and imaginary parts (SpatialOS.complexQuad_eq pattern) —
  per-observable constants absorb the factor.  NO complexification
  theory is attempted (Mathlib has none; o-bridge recorded that
  boundary).

## 2. Brick ladder (strict order, one oracle per brick)

- OS-R-0  JUDGES (§5) on the plane, both modes, BEFORE fabrication.
- OS-R-1  Module OSReconstructionUniform.lean, part A — the unitary:
          Q as a LinearIsometryEquiv (EuclideanSpace ℝ/ℂ conf) ≃
          (boundary vectors, site form) — or the elementary matrix-
          element identities if the packaged isometry fights the pin
          (fallback recorded: identities ⟨Qu, T (Qv)⟩_site =
          ⟨u, S_w v⟩_eucl proved pointwise suffice for (iv)-(v); no
          instance machinery is load-bearing).
- OS-R-2  Part B — n-step identification at extent: reconstructed
          pairing at separation n = dressed matrix element of S_w^n =
          Gibbs two-point sum (consume SpatialGibbs.gibbsWeight_eq_
          dressed + pathSum_eq_iterate — the generic bridge already in
          the tree for ANY symmetric kernel — plus paper 14's one-step
          osPairing_transfer_gibbsSum as base; induction only if
          consumption fails).  Both parities (site/bond separations)
          stated; the odd/even alternation is a named risk (§4).
- OS-R-3  Part C — the endpoint: instantiate dobrushin_ising_uniform_
          gap, transport through Q, package VacuumTransfer
          (TransferGap), conclude (iv)+(v); complex corollary by
          splitting.  Every quantifier in the statement, none in prose.
- OS-R-4  Wire into YangMillsCore + oracle_check additions; predict
          BOTH counts before the plane run (house discipline: the
          latest measured baseline is core 8480 / oracle 3010 at
          c7b870b05 — predictions stated in the fabrication commit);
          fresh-clone verification on the Colab plane (runner pattern
          of scripts/colab_dobrushin_d4_runner.py extended with the new
          module and this charter's judge).
- OS-R-5  Paper (papers/os-reconstruction/): the reconstructed theory
          has one mass.  Ink only what the oracle carries; tricotomy
          labels; the external-priority claim collated against
          Lean/Coq/Isabelle literature BEFORE the abstract claims it.

## 3. What is consumed as-is (no refabrication)

SpatialOS: osPairingBond/Site_eq, _nonneg, _gram_nonneg, complexQuad_eq,
collapse machinery.  SpatialReconstruction: siteForm/bondForm_collapse,
transferOp (+_unique, _selfAdjoint, _nonneg), transferOp_le_perron,
_perron_attained, _perron_eigen, normalisedTransferOpL, collapseL_
surjective, mem_ker_collapseL_iff, physicalEquiv, osPairing_transfer_
gibbsSum.  SpatialGibbs: gibbsWeight_eq_dressed, pathSum_eq_iterate.
TransferGap: VacuumTransfer, projectedTransfer, clustering_of_gap,
connCorr_eq.  DobrushinCorollary: dobrushin_ising_uniform_gap, sliceW.
DobrushinTilt: tiltKernel(_apply, _symm).  DobrushinTransport: opOf,
vacOf + their lemmas.

## 4. Named risks and death sites

R1 (top): definitional friction at the instantiation seams — the
corollary's slices are Fin (L+1) → Fin 2, papers 12-14's are
Fin L' → Fin 2; spatialKernel vs the OS lane's bond kernel must be THE
SAME declaration or proved equal pointwise; symWeighted w β must equal
√w·spatialKernel·√w definitionally.  G2-G4 pin every formula
numerically before fabrication; if any mismatch appears, FULL STOP,
record, redesign.  R2: the odd/even (bond/site) alternation in the
n-step identification — the induction may need separate even/odd
statements; a parity mistake here fabricates a false identification
that the numeric judge G5 would catch, so G5 tests BOTH parities.
R3: Lean packaging of the isometry on the site form (a non-standard
inner product on a function type) — fallback in OS-R-1 is stated and
sufficient.  R4: the external-priority claim — a collation failure
does not kill the theorem, only the abstract's framing.  Expected
death site: none mathematical; the campaign is plumbing-risk only,
which is precisely why it was chosen.

## 5. Judges (pre-registered; runner stage-1 on the plane, normal AND -O)

scripts/judge_os_uniform.py — NOTE the name: judge_os_reconstruction.py
already exists and belongs to paper 14's pre-registered gate (commit
7e744e6a8, another desk); it is not touched.  Independent Python
implementations (from THIS charter's formulas, no Lean parsing), slice
sizes S ∈ {2,3}, depths ≤ 4, parameters in and out of the window,
deterministic (no RNG), tolerance 1e-9 relative, explicit PASS counter,
sentinel protocol, no load-bearing assert:

- G1  collapse factorisation: brute-force half-summation bond/site
      pairings = collapse-factored forms (both parities, whole-half
      observables, not just boundary ones).
- G2  the forced operator: T = D_w K solves site(u,Tv) = bond(u,v) on
      a basis; site-self-adjoint at EVERY β (including β < 0); site-PSD
      for β ≥ 0.
- G3  the unitary: ⟨Qu,Qv⟩_site = ⟨u,v⟩_eucl; Q⁻¹TQ = √wK√w entrywise;
      spectra equal.
- G4  the feed alignment: tiltKernel (sliceW γ L) β λ = √wK√w/λ
      entrywise with λ = its Perron eigenvalue; Perron condition
      Σ tiltKernel·Om = Om; projected norm = second singular value.
- G5  n-step identification, BOTH parities: raw Gibbs two-point sums =
      dressed matrix elements of S_w^n = site-form elements of (T/λ)^n
      through Q; connected correlator bounded by ‖·‖²·r^n with
      r = the projected ratio, checked at n = 1..4.
- G6  window ∩ RP non-vacuity: β = γ = 0.2 in-window with β ≥ 0;
      projected ratio < 1 at S = 2,3 there (gate r ≤ 0.999 — sanity
      against the D-6 conclusion, not a substitute for it).

Gate structure frozen HERE; the numbers above (tolerances, sizes,
parameters) are final, not provisional — this campaign's judges are
exact-arithmetic-scale, no pilot needed.

## 6. Roles

Design + fabrication: this desk, in the D-6 cadence (judges on plane →
fabrication passes with count predictions → fresh-clone verification →
paper → external evaluation with its own scales).  The independent
audit of the paper is the external reading, as for D-6.  RI campaign
(RATE-INHERITANCE-CHARTER.md) stays REGISTERED and parked; its judges
have not run; nothing there is licensed meanwhile.
