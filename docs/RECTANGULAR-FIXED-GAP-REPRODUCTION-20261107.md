# Exact finite reproduction of the rectangular fixed-gap adapter, unit180

Hash context: analytical note ee2b86c0e62b039b5f3100ff858d1e26b1cdac87; executed adapter1cf122830b459add773f235f024b8c8ff78d095c; pinned Colab wrapper5b9dc9e9cbcbbe1f763a950de1e237d33a7730cc. Checked remote main88f31a1981b757b9240a9076e2012545066b9028.

The actual guillotine rectangular adapter and the intermediate-island examples reproduce with exact rational arithmetic. Four fresh sparse detached clones produced eight byte-identical payloads (normal and Python -O in each). Two own CPU allocations were requested through Colab, and each was disconnected/deleted through the UI after exporting. Full logs, source hashes, decimal exit sentinels, reports and archives are preserved.

## Actual checks

Ten D3,n4 cases assemble the actual start-weighted periodic scalar Laplacian and the normalized rectangular mean matrix P=C*C. Exact symmetric elimination proves E+cP-cI positive semidefinite in every case: dimension64,63 positive pivots and one zero pivot. Zero pivots are accepted only with a zero residual row. The h-component map/energy is the orthogonal sum of these scalar blocks, so no divergence constraint is assumed in these finite inequalities.

Coverage, disjointness, weak-site singleton isolation, actual binary cuts, q<=q0+2D|S|, side bounds, direct versus matrix energy, and exact orthogonal mean/variance identities are checked separately. Cases include empty, corner, wrap pair, chain, diagonal, plane, checkerboard, full weak set and an exact-mean coefficient-gap profile. Their actual rectangle counts are respectively1,4,4,7,10,10,17,64,64,7 (the two corner cases appear separately).

Two intermediate-island cases t2 andt3 (n4 andn9) verify exact mean and admissible coefficients, the analytic critical moment<2, full disjoint D+1=4-cell coverage, local side/coefficient residual estimates and actual rational field inequalities. The competing threshold-singleton strategy costs8 and27 cells respectively. No full n9 matrix was factored; these cases check the local Poincare dictionary and explicit fields, while its universal argument remains analytical.

In D3 the moment exponent3/2 generally produces radicals. The ordinary cases retain exact squared coefficient ratios/counts and a safe rational upper bound r^(3/2)<=max(1,r^2), not a falsely rational exact moment. The island weak moment equals1 by an exact squared positive-quantity identity; its strong part is <=1-s<1. This deviation in representation from the offline phrase 'record actual M' changes neither the hypotheses nor a tested threshold and is stated explicitly.

Five real implementation mutations are rejected: a missing side slab; a falsely reported cut count; unnormalized means (constant-field failure); skipped isolation with actual mean-zero Rayleigh2 versus target16; and end-weighted edges instead of actual start-weighted edges (explicit discrepancy45). Two additional solver attacks reject a negative pivot and a zero pivot with a nonzero residual row. These are author-supplied finite checks, not external guard qualification or independent audit.

## Reproduction and resources

All eight payloads have SHA256:
48a77cf0733e47081923d6c461b4efe01f69781533056947a4eadec4baf90b6a.

First archive SHA256:
fa01143b7ffdc2fe72177eb1091e63d9b0c5e4794018babbc9cf3123022dc156.
Second archive SHA256:
61660fda9c39a3a0f7578366b44e401c8f81273a2ed1c54440081f122d080476.

Each archive:64 entries,63 manifest subjects,18 actual one-line zero decimal exits and four matching payloads. Both archive manifests were verified after export using hashes/metadata only on Windows. No scientific execution or compilation ran locally.

First wrapper execution: 2026-11-07T11:05:16.562584Z to11:05:32.486699Z,15.924117268s; child max RSS106520KiB. Second:11:05:57.712071Z to11:06:12.279534Z,14.567467378s; child max RSS106904KiB. Requested-to-release upper bounds including allocation and export were49.957s and51.084s. Billed units are unknown. CPU/standard RAM fit the measured memory; no GPU, new dependencies, additional paid model or shared runtime was used. The Gemini panel was present but no prompt was sent to it.

IMPORTANT: both allocations reported the SAME hostname fingerprint. The clones are demonstrably fresh, clean, pinned and in distinct temporary roots (/tmp/tep-point180-ddkdispu versus /tmp/tep-point180-4watrw0j), and both UI disconnect/reallocation sequences were observed, but different physical machines or independently provisioned hosts are NOT established. Raw per-allocation reports retain fresh_runtime_pair_completed=false; the separate paired record certifies eight matching clone/process outputs and observed releases, not machine independence. No third allocation was requested merely to obtain a different hostname.

## Model assessments and review context

This is a finite implementation reproduction prepared in the same Codex research context as the analytical note. It is not an independent model review, Lean proof or all-size computational certificate. No numerical stars are assigned and no AIRR deposit was made. The existing exact AIRR v7 PDF and its3.0/10 assessment remain unchanged and cannot be inherited by this note.

The positive theorem still assumes a fixed coefficient gap/bounded weak values. The threshold-singleton method is refuted beyond that scope; the original unrestricted rectangular question remains open. This verification removes no new mathematical hypothesis and does not reset stopped-route/no-progress counters. PR29 remains20/41 and TermSource0; no interacting/continuum Yang-Mills gap follows.

Next mathematical work must derive useful geometry of intermediate-coefficient regions from the original moment and actual local energy, rather than assuming rectangular islands or returning to the failed singleton strategy. Group results into the existing manuscript dossier before obtaining a genuine exact-PDF assessment with stars and any publication.