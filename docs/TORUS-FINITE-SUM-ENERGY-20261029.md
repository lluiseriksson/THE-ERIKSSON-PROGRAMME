# Explicit finite-sum energy for individual torus characters

Formal source `251401e4de885dd0d70905e32da01bf5ba40cffd`, based on the
dimension construction from PR88. This module uses the actual finite sums

    mass(f) = sum_x ||f(x)||^2,
    E_plus(f,a) = sum_x ||f(x+a)-f(x)||^2,
    E_minus(f,a) = sum_x ||f(x)-f(x-a)||^2.

There is no hypothesis identifying the ambient function-space norm with L2.
Reindexing the finite group by x -> x-a proves E_minus=E_plus. For an actual
additive character chi, the homomorphism law gives

    chi(x+a)-chi(x) = (chi(a)-1) chi(x),
    E_plus(chi,a) = ||chi(a)-1||^2 mass(chi).

The explicitly defined one-component stencil adds transverse forward energies
to the longitudinal backward energy. The reindexing identity makes it equal
to the sum of forward energies in all directions. On the finite product torus,
the steps are the actual coordinate unit vectors and the character is the one
constructed in `TorusFourierBandDimension.lean`. Its stencil energy is exactly
the sum of squared character multipliers times the actual counting-L2 mass.
The same formula works for any finite abelian group and finite step family.

This is a construction step, not the complete low-energy subspace theorem.
The statement presently concerns individual characters, not arbitrary linear
combinations in the band. Orthogonality/Parseval, a quantitative multiplier
bound, the embedding of complex values as a real internal plane and the
identification with the actual physical cochain operator remain obligations.
In particular, defining a scalar one-component stencil has not proved its
equality to `PhysicalGaugeCochains` by naming it similarly.

The next single question is to extend this actual finite-sum identity to the
constructed span and its cochain embedding. A direct route is to prove the
character Gram sum by finite translation, then use the diagonal multipliers.
Falsifiers are a wrong shift sign, a duplicated real multiplicity, using the
Pi infinity norm as L2, or identifying the scalar stencil with the physical
operator without supplying that proof. The whole-band bound cannot be added
as an assumption inside a new structure.

These are classical finite Fourier mechanisms, not a new spectral priority
claim or a new paper. They belong with the existing obstruction dossier. No
hRpoly producer, physical spectral gap or continuum conclusion follows.
PR29 remains20/41 and TermSource=0. No independent model assessment or peer
review is claimed. Colab evidence, including failures, must be recorded below
before describing this candidate as verified. No Windows Lean/Lake is allowed.

## Verification history

Initial source `3f1de516ff18515ea092d94d3dd2b8d328c22f01` failed run015:
dot notation selected `Equiv.Perm.sum_comp`, which requires a finite-set
argument, instead of the intended whole-type reindexing. The failed build
log and complete ZIP are retained. The proof was repaired using an explicit
`Fintype.sum_equiv`; the statement and mathematical criterion did not change.

Run016 did not reach Lean: a global run-number substitution had accidentally
changed digits in the driver's expected Mathlib pin. The actual repository
pin was correct. Its complete failure package and faulty driver are retained.
The original registered pin `07642720480157414db592fa85b626dafb71355b` was
restored, using replacements restricted to artifact names; the pin or
mathematical judge was not relaxed to accept another dependency. Run016 is
not a mathematical pass or a measured Lean failure of the corrected proof.

Run017 checked the corrected source in a fresh own Colab CPU/high-RAM clone,
18:45:20.744367-18:47:34.503150 UTC on29October2026. All nine steps exited zero;
five direct oracle reports contained exactly `propext`, `Classical.choice`
and `Quot.sound`. The sixth theorem is included through their dependencies.
Its complete evidence ZIP has SHA256
`503c1f703f528a5436c21391d848cfde6db5360fb3b9e1d4c025df8684cd5bdd`.
The validator checked all twelve manifest entries, both UTF8/LF source hashes,
nine child exits and five reports. Target `.olean` SHA256 is
`1e8e67d872b53fff90a84e0e41ef5091770ec4e22a4cb39b5a72fd7ecd82435f`;
raw oracle log SHA256 is
`a83dedce31b5f5da8348ee1672d5386a2a2599d7bcec1c3d7c7d8bb36975ec49`.
The runtime released automatically and its reconnect control was observed.
Compute units and pre-execution allocation duration were not measured.

This records a focused source verification. Terminal reproduction additionally
requires two complete fresh-clone packages at that same SHA with matching
output hashes. All sessions belong to this chat; they are not independent
scientific review. No statement about the still-missing physical operator
identification follows from a scalar stencil check.

The same saved notebook was then executed in a newly allocated own CPU/high-RAM
runtime, recorded as **017b** (18:48:34.839610-18:50:45.271259 UTC). Its complete
ZIP has SHA256
`d651ec6aaa029d7303ee9e4b85229c6819c07cfc6e5d2372955955a72621e7a6`.
All nine steps and five reports passed. Local manifest/log validation and an
explicit comparison show identical source SHA, target `.olean`, raw oracle
log and source-manifest hashes. Thus017 and017b close the two-fresh-clone
reproduction requirement for this exact module at251401e4. Both runtimes
released automatically and reconnect was observed. No independent scientific
review or whole-repository terminal audit is implied.

For the next construction, the pinned primary Mathlib source already supplies
`AddChar.sum_eq_zero_iff_ne_zero` in
[`Algebra/Group/AddChar.lean`](https://github.com/leanprover-community/mathlib4/blob/07642720480157414db592fa85b626dafb71355b/Mathlib/Algebra/Group/AddChar.lean)
and `AddChar.norm_apply` in
[`Analysis/Normed/Ring/Finite.lean`](https://github.com/leanprover-community/mathlib4/blob/07642720480157414db592fa85b626dafb71355b/Mathlib/Analysis/Normed/Ring/Finite.lean).
These exact sources were read; using them to prove the band Gram identity is
the next obligation, not a result certified by the present module.
