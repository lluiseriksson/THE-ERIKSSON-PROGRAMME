# How much does whole-percentage reporting conceal?

We constructed the same 159 overlapping three-task windows for the pinned StarCoder2 C++ response bank as in the manuscript. Each window averages 150 recorded attempts. The inputs to each inverse calculation were the rounded window percentages, the task order, window width and count bounds. We generated both sets of labels directly from the recorded outcomes, rounding once with exact half-up arithmetic.

| Reporting precision | Compatible labelled vectors of failure counts | Task counts fixed across all compatible vectors | Attainable extremes of global pass@3 |
| --- | ---: | ---: | ---: |
| Tenth of a percentage point | 1 | 161 of 161 | 50.56408% at both ends |
| Whole percentage point | 1,161,773,222,400 | 71 of 161 | 50.39264% to 51.57032% |

Both endpoints in the last column are attainable. The table gives no assertion of attainability between them. Many compatible vectors can agree on the same count for a particular task. Treating the reported vector as a random draw from a uniform distribution on the compatible set would require an additional assumption.

## Counting argument

At each position retain a state for the last two failure counts of a feasible prefix. An edge appends an integer from 0 through 50 exactly when the sum of the resulting triple rounds to that window's reported percentage. Initialize each ordered pair with one path. Every full vector has exactly one path and every complete path gives a compatible vector. Adding prefix counts along edges therefore gives the exact number of possibilities. Propagating the minimum and maximum of the running sum of the per-task number of failing triples gives the extreme global pass@3 numerators, because the contribution of the next task depends only on its count. Traverse viable states backwards from the terminal layer to recover each coordinate's support among complete paths. Forward reachability alone could retain counts from prefixes that cannot be completed.

The result file includes two distinct witnesses for the whole-percentage reports and exact supports for the individual tasks. A separate exhaustive comparison tested counts, supports, witnesses and both extrema on all 1,024 vectors of five tasks with counts from 0 to 3 at each of three resolutions, giving 730 distinct test cases across resolutions. The finer-precision replay recovered the recorded vector exactly.

This supplement measures a reporting choice for one public bank in a fixed order. It concerns counts of failures per task. Statistical reconstruction from aggregates and forward–backward calculations have long precedents. [Dinur and Nissim](https://doi.org/10.1145/773153.773173) · [Rabiner](https://doi.org/10.1109/5.18626)

## Reproduction

Run `python precision.py` in the same directory as `audit.py` with PyArrow installed. Compare the JSON result with `precision.json`. The program verifies the input digest before reading the public evaluation outcomes. The supplement postdates the assessed manuscript at commit `d871578915478ce77d0dee026523cbd1b7c9ac87`.
