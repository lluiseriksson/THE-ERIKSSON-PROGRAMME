# Which model rankings can be inferred from the ReViCo image scores?

Of 190 pairs, 149 have a fixed order and 41 can take either strict order for the fraction of detected erroneous images fully repaired. These results are conditional on a scoring convention compatible with all 20 rows. Each language has equal weight in precision and recall. F1 is computed from those two means. The denominator stabilizer is 10^-8 and the six printed cells per model are rounded to tenths of a percent.

Three models can each rank first: Seed–2.0, Gemini2.5–Pro, Gemini3.1–Pro. Each of those three is strictly ahead of all other models on this particular outcome. No observed prediction logs are inferred from this ranking. Different models can choose their feasible counts separately because the published cells impose no between-model prediction constraint.

## Exact supported rates

Each endpoint is attained. The intervening interval can contain unattainable fractions. The final column counts possible six-integer summaries, irrespective of how many individual prediction files would give that summary.

| Model | Lowest repair fraction | Highest repair fraction | Feasible summaries |
|---|---:|---:|---:|
| Qwen2.5VL3B | 7/125 | 13/147 | 31205 |
| Qwen2.5VL7B | 45/169 | 21/53 | 49 |
| Qwen2.5VL32B | 138/307 | 91/153 | 805 |
| Qwen2.5VL72B | 138/325 | 171/310 | 766 |
| Qwen3VL2B | 24/79 | 24/79 | 1 |
| Qwen3VL4B | 75/353 | 104/301 | 2149 |
| Qwen3VL8B | 60/431 | 83/346 | 8416 |
| Qwen3VL32B | 112/303 | 147/284 | 1032 |
| Qwen3VL235B | 73/257 | 67/159 | 12908 |
| InternVL2B | 6/143 | 16/219 | 1760 |
| InternVL4B | 29/470 | 38/401 | 6765 |
| InternVL8B | 4/29 | 25/127 | 19 |
| InternVL14B | 19/125 | 16/61 | 5587 |
| InternVL38B | 82/221 | 104/213 | 214 |
| GPT–4o | 52/101 | 46/75 | 655 |
| GPT–5.4 | 148/467 | 101/214 | 8525 |
| Seed–1.8 | 296/587 | 391/597 | 4980 |
| Seed–2.0 | 426/607 | 487/615 | 5841 |
| Gemini2.5–Pro | 373/557 | 449/579 | 15354 |
| Gemini3.1–Pro | 432/623 | 493/628 | 7723 |

## What would resolve the ambiguity?

For each model and disclosure, we group all feasible summaries by the extra reported value or pair of values. A disclosure identifies the repair fraction for a model if every one of its groups has just one reduced fraction. Nine candidate counts are the Chinese, English and pooled counts for each of detected erroneous images (T), fully corrected images (C) and falsely flagged clean images (FP). The test covers all nine singles and all 36 pairs. Its scope is limited to these reporting options.

| Single count | Models for which it suffices |
|---|---:|
| Tzh | 1 |
| Ten | 1 |
| Czh | 1 |
| Cen | 1 |
| FPzh | 1 |
| FPen | 1 |
| Tpool | 1 |
| Cpool | 1 |
| FPpool | 1 |

Pairs sufficient for all 20 rows: (Tzh,Czh), (Tzh,Cen), (Tzh,Cpool), (Ten,Czh), (Ten,Cen), (Ten,Cpool), (Czh,Tpool), (Cen,Tpool), (Tpool,Cpool).

## Reproduction and scope

Place the parent tables.json beside the four source files. Run python3 repair_ranges.py and python3 repair_disclosure.py on Linux with a C++17 compiler and Boost headers. Both scripts use the image rows of Table 1 and the language denominators in Figure 3. The first enumerates the feasible counts using exact integer comparisons. Precision and recall numerators and denominators fit within 128 bits, and harmonic-mean cross products fit within 256 bits (all components are below 10^26 before the final products). It joins detection and correction on the two clean-image false-positive counts, requires corrections not to exceed detections per language and checks both extremizing witnesses again with Python rational arithmetic. Their six scores lie strictly inside the rounding cells, so the attained bounds are unaffected by the convention for rounding ties. The second script groups the enumerated summaries and records counterexamples for insufficient disclosures. Feasibility is a statement about the rounded numbers, not the evaluator actually run. This supplement postdates the assessed PDF.

[Source article, Table 1, Figure 3 and Appendix E](https://aclanthology.org/2026.emnlp-main.845/)
