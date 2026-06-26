# Symbol Dictionary Seed

Candidate and pending source ↔ Lean symbol mappings. Do not treat `pending` entries as proved dictionaries.

| Link | Source symbol | Lean symbol | Status | Blocker |
|---|---|---|---|---|
| `dict.eq229.D` | `Balaban D-family` | `DIndex/DParts` | `pending` | Cammarota polymer dictionary and CMP116 D-family dictionary missing |
| `dict.eq231.P` | `Balaban P` | `Finset (Cube x Fin 4)` | `pending` | membership iff and orientation dictionary missing |
| `dict.eq231.gap` | `M^-4 |Z0\Y0|` | `gapMass Z D` | `candidate` |  |
| `dimocki.covariance.dictionary` | `C_k` | `physicalGaussian / covariance / precision` | `pending` | No direct scalar-to-Yang-Mills covariance identification. |
| `dimockii.appendixf.omega-relation` | `Omega-connected` | `omegaHolePolymerSystem / active-skeleton overlap` | `partially_implemented` | Prove all source-domain and metric identifications for the concrete Yang-Mills activity. |
| `dimockii.root.dictionary` | `(C'_(k,Omega))^(1/2)_loc` | `root / rootLocalization / PhysicalLocalizedCovarianceRootCertificate` | `pending` | Exact gauge Hessian, domain, determinant and local-piece reconstruction. |
| `seed.gapMass` | `M^-4 |Z0\Y0|` | `gapMass Z D` | `candidate` | Needs source dictionary from Balaban Z0/Y0 to gapCubes. |
| `seed.omega-connectivity` | `X_i ∩ X_j ∩ Ω ≠ ∅` | `omegaHolePolymerSystem / skeleton relation` | `source_extracted_needs_model_bridge` | Need final source-to-Lean polymer/skeleton dictionary. |
| `seed.r-local-bound` | `|R^(j)(X)| <= g_j^kappa0 exp(-kappa d_j(X))` | `RawYMActivityDecay` | `pending` | Need CMP119/CMP122 exact theorem extraction and polymer metric dictionary. |
