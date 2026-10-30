# Actual periodic shifts and flat cochain differentials

This continues the existing Fourier/rank-obstruction dossier; it is not a
separate paper or a claim of new Fourier analysis. The target is the actual
Euclidean-coordinate physical cochain interface in this repository. The
matrix-Lie-algebra interpretation and continuum limit remain separate.

For every n>0 the concrete FinBox/ZMod site equivalence intertwines
`FinBox.shift i` with addition of `Pi.single i 1`, including wraparound.
Backward shifts follow from the already proved finite-lattice inverse and
additive cancellation, avoiding unsafe natural-number subtraction casts.

Write e(x) for this equivalence, P for the real/imaginary Euclidean plane,
and E_j f for the actual one-component cochain constructed in PR92. For the
trivial background and every admitted SUNAdjointModel, the proved exact
identities are

    div E_j f (x) = P(f(e(x)) - f(e(x)-e_j));
    curl E_j f (x;a,b)
      = [a=j] P(f(e(x))-f(e(x)+e_b))
        + [b=j] P(f(e(x)+e_a)-f(e(x))).

Here a<b and each plaquette occurs once. These are actual repository
operators, not newly introduced scalar substitutes or assumed interface
fields. Real linearity of P is proved coordinatewise. Exact counting norm
preservation then makes the squared norm of the actual divergence equal to
`backwardShiftEnergy f e_j` for arbitrary complex-valued profiles, with no
Fourier, nonaliasing or regularity assumption. Nc>=2 supplies two internal
coordinates; the chosen direction j makes d>0 explicit. The flatness condition
is the explicitly trivial background; no nontrivial-background estimate follows.

## Verification

Source bf6fa4efd7bd7d883373d4ddb6299ff3c0b71426 was checked in two fresh,
serial Colab CPU/high-RAM clones. Both complete packages were recovered and
validated before comparison. Each has 12 manifest entries, two source-hash
entries, nine exit-zero steps and seven exact named oracle reports. The first
three transport lemmas use propext and Quot.sound; the remaining four also
use Classical.choice. No other axioms are admitted. Raw logs and declared
per-theorem lists agree. Each run also passes the oracle validator's positive
control and three actual-field mutations in both normal and optimized Python.

| Artifact | SHA256 of raw bytes |
| --- | --- |
| run028.zip | 3b6074096ed3dadf28989475cf2b2ce499685675a731e42aa69c6890483e6a56 |
| run028b.zip | 8e8bde41ee443c91a0b63b0daca08c93a04905f5b10f9a2a675c79f9e589e161 |
| target .olean, both | a22576640cae53acbc1f1e845258746c8c438562232881736b8e4efb47d1d3c0 |
| oracle.log, both | ed2b8a44ae7b259282aa10d64c9b1b71b28bc12a33ca41ae38ec31743cc8b28e |
| source-hashes.json, both | 2316dbe64077b4b54883e70e005e0fa3d01996833f137551747751b3a71dd704 |

Normalized LF source SHA256:
module4a24f26cc3d5f711cb70c8c1a7b53e7ec5d956f9fd23574d71cb41fd76470d37;
oracle7c1df638ef0a785ac08af5f55dfc3ac8fe615014edd3764bc68ff12a2ddfc166.
Only source LF hashes use normalization; raw output and ZIP hashes do not.

Run028:23:58:38.054373UTC on29October to00:01:24.746989UTC on30October,
166.692616s. Run028b:00:03:04.335155-00:06:29.300677UTC on30October,
204.965522s. Both automatically released and the disconnected control was
observed. Three earlier failed runtimes were also released. Total execution
intervals including failures:1000.350327 seconds. Additional allocation
and release overhead and compute units were not measured. All five runtimes
were this chat's own serial CPU/high-RAM machines;50.99GB RAM observed.
No GPU, local Windows Lean/Lake, runtime sharing, additional purchase or idle
connected machine. The first complete passing package was saved and validated
before the second fresh clone began.

Full ZIPs, failed attempts, validation scripts, normal/-O oracle selftests,
source manifests, exact executed notebook and runtime record are in
`reproducibility/torus-physical-shift-20261030/`. The convenience Python copy
trims only excess EOF blank lines; the notebook preserves the exact executed
input. This is focal module reproduction, not a terminal whole-repository audit.

The operator API explicitly takes `NeZero d` and `NeZero Nc` instances. These
are consistent with the chosen j:Fin d and Nc>=2, rather than a new analytic
restriction. In contrast, the purely scalar shift lemmas require only n>0.

The failed first candidate78c1012 (full run025 retained) exposed two interface
issues: the optional Nat-to-Fin coercion must be enabled with `Fin.NatCast`,
and the actual operator signatures require their explicit dimension instance.
Both were corrected without changing the mathematical differential formulas.
Candidate2acc444 then reached the actual norm proof but timed out while
unifying the final reindexing expression at the default200000 heartbeats.
Its full run026 is retained. The next proof gives the operator output a
local name, transports each pointwise squared norm explicitly, and unfolds
the scalar sum before reindexing. Run027 at62e3526 still hit the default
resource limit at the final sum. The current version uses Fintype.sum_equiv
with an explicit pointwise obligation and gives only this norm declaration
an800000-heartbeat elaboration budget. This changes an elaborator resource
limit, not hypotheses, axioms or kernel checking. The mathematical statement
and acceptance criterion remain unchanged.
The new oracle validator allows only subsets of the same three standard Lean
axioms because simple constructive transport lemmas need not use all three.
It checks all seven names and raw reports exactly, and records per-theorem
axiom lists. Normal and optimized Python selftests must accept the true log
and reject mutations of its actual theorem field, report count and axiom field.
No acceptance depends on `assert`. The validators are part of the preserved
reproducibility input, not an external review or a model score.

## What remains and the next falsifier

The full physical Hodge energy is still pending until the squared curl norm
is summed over actual unordered plaquettes. For fixed j, the plaquettes that
can contribute correspond to i!=j via i -> (min(i,j),max(i,j)); orientation
changes the sign of the vector but not its squared norm. A proof of this
explicit counting identity would give sum_{i!=j} forwardShiftEnergy f e_i.
Together with the divergence theorem this would identify the actual Hodge
form with the scalar one-component stencil already bounded in the prior
modules. This last paragraph is an analytic deduction and plan, not a formal
result of the present module. The physical synthesized-range dimension also
remains to be proved. Neither may be supplied as a structure field.

Falsifiers: a boundary wraparound error, a backward sign error, a duplicated
ordered plaquette, a missing counting factor, or a mismatch with the actual
operator definition. Preserve failures and any counterexample. After three
units without substantive mathematical progress, record the precise block
and change route. No hRpoly producer is discharged; PR29 remains20/41 and
TermSource=0. No Yang–Mills physical spectral gap or continuum claim follows.

## Originality and primary evidence

The shift and difference formulas are classical. Their contribution here is
the checked link to the existing concrete operator implementation, resolving
previously explicit transport obligations. Relevant primary sources are the
source at the tested repository SHA (not an unversioned working tree),
`PhysicalGaugeCochains.lean`'s flat application theorems,
`FiniteLatticeGeometryInstance.lean`'s shift inverses, and Mathlib's
[ZMod basic definitions at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/07642720480157414db592fa85b626dafb71355b/Mathlib/Data/ZMod/Basic.lean).
Formal validity, novelty and scientific relevance are distinct.

## Model assessments and review context

Construction and orchestration are by this chat's Codex assistant; the exact
backend model identifier is not exposed in this run. Lean reproductions in
this same workflow are mechanical checks, not independent model assessments
or independent scientific reviews. No score, peer review, acceptance, new AIRR
publication or repeated ai.viXra deposit is claimed. No assessment of a prior
PDF is inherited. No new PDF is produced by this internal code bridge unit.
