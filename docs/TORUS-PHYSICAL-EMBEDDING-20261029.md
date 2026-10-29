# Actual Fourier-profile embedding into physical gauge cochains

Here “physical” means the repository cochain interface, whose `SUNLieCoord`
is an explicitly defined Euclidean coordinate model. This does not identify it
with a matrix Lie algebra or discharge that separate interface obligation.

The map in `YangMills/RG/TorusPhysicalEmbedding.lean` constructs actual elements
of `PhysicalGaugeOneCochain d n Nc`; no isometry or injectivity is supplied as
an input. For `n > 0`, `Nc >= 2` and a chosen bond direction `j : Fin d`, it puts
the real and imaginary parts of a complex profile in internal coordinates 0
and 1 at bonds in direction j, and sets all other bonds to zero. Sites are
transported by the product of Mathlib's explicit `ZMod.finEquiv n`.

The internal coordinates have the Euclidean norm and the outer bond space
uses PiLp 2. Consequently

    ||E_j f||^2 = sum_x ||f(x)||^2.

This uses counting L2, not the supremum norm on a function type and not the
maximum norm on the ordinary product of two real normed spaces. The two
internal coordinates exist because `Nc >= 2` implies `2 <= Nc^2 - 1`.
The chosen direction makes the nonempty-bond requirement explicit; no such
injection is claimed when d=0. Addition and real scalar multiplication are
proved for the constructed map. Evaluation in the two internal coordinates
proves injectivity after undoing the site equivalence.

For the actual centered Fourier synthesis with `2*R < n`, the previous
counting Parseval theorem now gives

    ||E_j (sum_k c_k chi_k)||^2 = n^d * sum_k ||c_k||^2.

This closes the norm/faithfulness obligation for the intended one-component
embedding. It does not yet prove the shift/shiftBack intertwining, the
physical curl/divergence energy identity, the dimension of its synthesized
physical range, or the final dimension obstruction for the physical operator.
No hRpoly producer, PR29 count, or TermSource status changes.

## Formal verification

Source ddd2535231a34778ee5c0cee1b4062c19ad92d64 follows main1703df2c, which
merged PR91 by merge commit only after both required checks passed at8f13afd.
Two fresh Colab CPU/high-RAM machines fetched this exact SHA. Complete packages
were recovered, independently validated for their manifest contents, and
compared. Each contains 12 manifest entries, two source hashes, nine exit-zero
steps and six named oracle reports using only propext, Classical.choice and
Quot.sound. The same workflow runs both; this is mechanical reproduction.

| Artifact | SHA256 of raw bytes |
| --- | --- |
| run024.zip | b84ea5b98ea1c7e1b6510595c5a38e9d567741198fc6d5d49a083e57809f2a9e |
| run024b.zip | 9b40b0c60a56b4cbc60abc3348f94a656f4189f31edebd3590af7667700b3ea4 |
| target .olean, both runs | fb9c0baeaca047763427064fa1a2da6f8593e4ac68b9e0878950bcc9fb266a29 |
| oracle.log, both runs | 9d7446d40729b9962b4c4e969969b86e3ac8c386b66e5fe4ae52d5a9de8fdcad |
| source-hashes.json, both runs | aed3ada20e885d883fffd87a19b1fae6cd50362b2696819d8ad7a4d5fb86ee50 |

The normalized LF source SHA256 is d304e20142d13165decf2da774a8258a24d690cf8b0a84ca8c8932b7135e7d83;
the oracle LF source SHA256 is446b6e057f077573877b788e1d454fc61152e2686f18a45accdbb36e3490227d.
The package source manifests record this explicit normalization. Raw ZIPs and
raw output hashes are not newline-normalized.

Run024: 21:56:27.146041-22:00:23.292757 UTC (236.146716s).
Run024b:22:01:13.011393-22:04:03.788012 UTC (170.776619s).
Both runtimes released automatically and the disconnected control was observed.
The two earlier failed runtimes were also released; all four were serial and
belonged to this chat. Failed run022:21:43:14.259073-21:45:58.230136 UTC;
failed run023:21:49:32.126246-21:52:21.654202 UTC. Total execution intervals
including failures:740.422354s; allocation/release overhead and compute units
were not measured. No GPU, local Lean/Lake, shared runtime or new purchase.

See `reproducibility/torus-physical-embedding-20261029/` for full ZIPs,
validators, comparisons, exact executed notebook and source checks. The Python
convenience copy trims only excess EOF blank lines; the exact executed input
is retained in the notebook and durable D: evidence. This is focal module
closure, not a terminal audit of the entire repository.

Failed first candidate40b5bdab is retained with full run022 ZIP. Lean rejected
an implicit inner-product expansion (simp folded inner-self back to norm), a
redundant tactic after a solved scalar goal, and a conditional norm that had
not been moved through its if. The second candidate f98cf147 still failed (run023): the generic single-vector
inner simplification did not match the concrete target, and application of
the conditional rewrite stopped before distributing the square. The final
proof instead establishes a coordinatewise square identity, sums its two
disjoint singleton contributions, and proves the conditional norm identity
by explicit cases before summation. The scalar-multiplication proof uses
only the simplification that actually closes its goal. The mathematical statements and six-oracle
acceptance criterion are unchanged. No failed run is counted as verification.

## Originality, relevance, and sources

The real/imaginary Euclidean embedding and reindexing of a finite counting sum
are classical. This is repository-specific bridge work, not a claim of a new
mathematical discovery or a separate paper. It belongs with the existing
low-mode/rank-obstruction dossier. Formal correctness, originality and physical
relevance are separate questions.

Primary definitions inspected at the exact repository Mathlib pin
07642720480157414db592fa85b626dafb71355b:

- [EuclideanSpace, single-coordinate inner products and PiLp norm](https://github.com/leanprover-community/mathlib4/blob/07642720480157414db592fa85b626dafb71355b/Mathlib/Analysis/InnerProductSpace/PiL2.lean).
- [ZMod.finEquiv](https://github.com/leanprover-community/mathlib4/blob/07642720480157414db592fa85b626dafb71355b/Mathlib/Data/ZMod/Basic.lean).
- Actual target definitions: `YangMills/RG/PhysicalGaugeCochains.lean`.

## Model assessments and review context

Proof construction and orchestration were performed by this chat's Codex
assistant; the backend model identifier is not exposed in this execution.
The Colab runs are mechanical Lean reproductions in this same workflow, not
independent scientific reviews. No model score, peer review, acceptance, AIRR
submission or publication is claimed. No previous PDF assessment is inherited.
The existing AIRR/ai.viXra paper has not been deposited again.

## Next falsifiable step

Prove that the concrete site equivalence intertwines FinBox.shift/shiftBack
with cyclic addition/subtraction. Then prove that the physical flat curl and
divergence of this actual map give exactly the already constructed scalar
one-component stencil energy, including unordered plaquette counting. The
falsifier is any wraparound/sign/normalization discrepancy. If it fails,
preserve the discrepancy and repair the theorem's scope before using the
quantitative scalar bound. Do not assume the missing identity as a structure
field. After three substantive attempts without progress, record the concrete
obstruction and change the route. The unit-spacing obstruction must remain
separate from fixed-physical-volume scaling eta=1/L.

A minimal obstruction route needs only this one-component, two-internal-coordinate
range. Once its physical Hodge energy and real dimension 2*(2R+1)^d are proved,
choose R with 2*(2R+1)^d > M+r for the fixed measurement/repair dimension budget.
For sufficiently large n the no-alias condition holds and the scalar bound is
O(R^2/n^2), enough for a unit-spacing obstruction without multiplying by all
bond or Lie-algebra directions. This is a planned deduction, not a proved
physical theorem in the present module; the stronger q-fold dimension formula
in the analytic note must not be attributed to this one-component embedding.
