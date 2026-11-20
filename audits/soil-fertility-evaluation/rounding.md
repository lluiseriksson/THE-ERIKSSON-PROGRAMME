# What is lost when aggregate measures are rounded?

Supplement to [PR 333](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/333), prepared after the reviewed PDF. Use the common 122-case test, correct counts 112 and 111, and the formulas for support-weighted F1 and multiclass MCC in the manuscript. Keep three nonempty true classes and require the same true class counts in both arms. Round both F1 and MCC to the indicated number of decimal places. The original source values fall strictly inside the coarser rounding cells. The accuracy counts stay fixed.

| Decimals retained | Compatible common support vectors in sorted order | Pairs of minority recalls | Range of SMOTE minus Borderline-SMOTE minority recall |
|---:|---:|---:|:---|
| 3 | 109 | 206 | −1 to 8/17 |
| 4 | 1 | 1 | 0 (both recalls zero) |
| 5 | 1 | 1 | 0 (both recalls zero) |

The endpoints of the three-place range are attained. At supports (5,42,75) the first method can miss all five rare cases while the second detects all five. At supports (17,25,80) the first can detect 17 of 17 and the second 9 of 17. Cases with ties in the smallest support are included; both possible label orders are represented. These are reconstructed alternatives that could have generated the coarsened numbers. The study printed more precise values, which exclude both alternatives.

The search enumerates the diagonal and six off-diagonal counts, fixes the two traces and tests inclusive rounding cells by integer cross multiplication. Sorted true-support vectors index the compatible tables for each method. Taking their intersection before pairing the possible minority recalls enforces the shared cohort assumption. JSON certificates contain matrices attaining each extremum. For a multiclass prediction with no further restrictions on overlap, any two matrices with common true supports can be realized by assigning each model's labels within each true stratum. This is why both witnesses are sharp.

[Primary Table 4](https://www.mdpi.com/2673-4591/163/1/114). This precision analysis is a supplement; the score of the earlier PDF applies only to that artifact.
