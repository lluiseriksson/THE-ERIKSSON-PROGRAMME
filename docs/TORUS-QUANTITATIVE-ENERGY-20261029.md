# Quantitative energy of the constructed centered Fourier family

Formal source `bb8bd02b75a8651dde5cac93f880d4944f15c612`, based on
main `53d85bc7f0dcec31000cd9fa7049737c3f67021d` after merging PR90.
This continues the existing flat-obstruction dossier, not a separate paper.

For centered labels k_i in0,...,2R, the actual residue is k_i-R. The proof
uses the INTEGER lift z_i=k_i-R, establishing |z_i|<=R from the label bounds.
It does not treat the wrapped `ZMod.val` of a negative frequency as small.
The standard-character formula on an integer lift and the complex exponential
bound give

    |stdAddChar(z_i)-1| <= 2*pi*|z_i|/n <= 2*pi*R/n.

Evaluating the actual product-torus character at a coordinate unit vector
gives this same scalar character. Summing the squared multipliers therefore
gives at most d*(2*pi*R/n)^2. Applying the already-derived counting Parseval
and exact combination-energy identity proves, for every centered coefficient
family and2R<n,

    oneComponentStencilEnergy(F) <= (4*pi^2*d*R^2/n^2) * countingL2Mass(F).

The constant is derived, with no assumed frequency envelope, Gram formula or
energy estimate hidden in a structure. The sums use scalar complex norms
pointwise and the counting measure, not the ambient function-space norm.

This is the explicit scalar one-component stencil, still awaiting its proved
identification with the repository's real PhysicalGaugeCochains operator.
Transport of the internal real plane and Fin/ZMod site indexing, and connecting
the coefficient presentation to every member of the old span, remain separate
obligations. No physical coarse-rank no-go, hRpoly producer or mass gap is
formalized by this module. PR29 remains20/41 and TermSource=0.

At physical spacing eta, the energy and this upper bound both acquire
eta^-2. With eta=1/L and n=L*Nprime, the right-side factor becomes
4*pi^2*d*R^2/Nprime^2. Its decay in L at unit spacing cannot be used as a
physical-gap contradiction. The preceding dossier gives an explicit analytic
rank-q mean-measurement repair at fixed physical volume; that scope restriction
remains essential.

These estimates are classical. The pinned primary source
[`CircleAddChar.lean`](https://github.com/leanprover-community/mathlib4/blob/07642720480157414db592fa85b626dafb71355b/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean)
supplies `ZMod.stdAddChar_coe` for integer lifts, and
[`Trigonometric/Bounds.lean`](https://github.com/leanprover-community/mathlib4/blob/07642720480157414db592fa85b626dafb71355b/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean)
supplies `Real.norm_exp_I_mul_ofReal_sub_one_le`. Both exact source files
were read. The resulting theorem has the original4*pi^2 constant.
No spectral novelty or literature-wide priority is claimed.

## Model assessments and review context

This same Codex chat developed the proof and orchestrated the compiler checks.
Those are execution checks, not independent model assessments or human peer
review. No score, acceptance or new AIRR publication is claimed. The exact
Colab source, oracle, logs, exit codes and output hashes determine verification
status; a sentinel or file's existence alone does not establish success.

Run021 verified the source on its first mathematical attempt in an own fresh
Colab CPU/high-RAM clone,20:40:56.421437-20:43:41.187574 UTC on29October2026.
All nine steps exited zero and four direct oracle reports contained exactly
`propext`, `Classical.choice` and `Quot.sound`. Its complete evidence ZIP has
SHA256 `545aab1d70e08335bd687e7eb4ed4c649d747badf424d9cd495c41ec26668a17`.
The validator checked twelve manifest entries, both UTF8/LF source hashes,
all child exits and all four reports. Target `.olean` SHA256:
`39a4c3706ced82cf30f985cd0d5837ecf5b3e1f971a40379a293da8a122e8032`;
raw oracle log SHA256:
`1efc4976995f3f4d29318b985464333b6572dbf2249a81caa62ca9ede09d0103`.
The complete package was preserved before requesting another fresh clone at
the same SHA. The runtime released and reconnect was observed. No GPU,
Windows Lean/Lake, shared runtime or new purchase was used. Compute units and
additional allocation duration were not measured. One successful build alone
does not imply the two-clone terminal reproduction condition.

Run021b repeated the unchanged prepared notebook in a newly allocated own
CPU/high-RAM runtime,20:44:18.577976-20:47:13.158036 UTC. Complete ZIP SHA256:
`2d5c5d8d6c8afea38243e8715bba8bf2712a3ce943ab0148585a2e95a0b01fed`.
All nine steps and four reports passed; all manifest entries and source hashes
were checked. Source SHA, target `.olean`, raw oracle log and source-manifest
hashes match021 exactly, closing two-fresh-clone reproduction for this module
atbb8bd02b. Both machines released and reconnect was observed. No failed
candidate or mathematical proof repair occurred in this unit. The result is
the scalar-stencil upper bound, not a physical-operator or continuum theorem.
