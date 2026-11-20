# Identifying the least frequent class from the two published summaries

Assume a common unweighted held-out sample with at most 176 cases, three nonempty true classes, conventional support-weighted F1 and the multiclass Matthews correlation coefficient (MCC). The two accuracies in Table 4 force N=122 and 112 and 111 correct predictions respectively. Using the F1 and MCC values at their published precision gives exactly one matrix per method up to simultaneous renaming of true and predicted classes. Rows correspond to actual classes and are sorted by increasing support. Columns have the same class order.

| Actual support | SMOTE predicted counts | Borderline-SMOTE predicted counts |
|---:|:---|:---|
| 3 | 0, 3, 0 | 0, 3, 0 |
| 58 | 1, 55, 2 | 2, 54, 2 |
| 61 | 0, 4, 57 | 0, 4, 57 |

The entire one-case net gain in accuracy comes from the class with support 58. Neither method correctly predicts a member of the smallest class. This concerns the effective test sample under the stated assumptions. It does not identify population recall, the specific cases involved or the explanation for the effective denominator.

For trace H, row totals R, column totals C and diagonals t, weighted F1 is Σ 2Rᵢtᵢ/(Rᵢ+Cᵢ)/N. MCC is (NH−R·C)/sqrt[(N²−R·R)(N²−C·C)]. At fixed error count enumerate the six off-diagonal counts as weak compositions, then all diagonals of trace H. Sort the true supports, allow ties and impose both rounding intervals using integer comparisons, squaring the MCC endpoints only after checking its sign. Treat the printed decimal precision independently for each value. The first enumeration found one matrix even before imposing a common support. The other enumeration loops over diagonal vectors and off-diagonal row and column totals and reconstructs all nonnegative completions along the remaining free cell. These are checks with different parameterizations in the same research context.

[Primary report, Table 4](https://www.mdpi.com/2673-4591/163/1/114) · [Generalized correlation coefficient](https://pubmed.ncbi.nlm.nih.gov/15556477/)
