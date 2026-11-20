# Dispersion across all six division shares

For each period order the six division means from smallest to largest. The Lorenz ordinate at j/6 is the sum S_j of the j smallest scores divided by the total T. After a common shift c it is (S_j+jc)/(T+6c). Comparing periods and clearing the positive denominators cancels the quadratic term. Each ordinate has a linear sign test. Since both Lorenz curves are piecewise linear on the same knots, comparing all five interior knots suffices for dominance. A strict positive and a strict negative at two knots certify a crossing.

For the reported scores, treating four decimals as nearest rounding, the intervals for the six entries within each period are disjoint. Their order is fixed. A bottom entry increases the bottom share if raised, and a remaining entry decreases it. Thus the lowest and highest bottom shares for each period are attained at opposite corners of the six-dimensional rounding box. Each endpoint comparison has exact attainable upper and lower signs for that single ordinate. Simultaneous conclusions below use signs true for every admissible input, without assuming that extrema at different ordinates occur together.

| Common shift c (sufficient range) | NN-PCA | Standard PCA |
| --- | --- | --- |
| 0 through 0.077 | Later curve strictly above at all five knots | Later curve strictly above at all five knots |
| 0.106 through 1.309 | Curves cross | Curves cross |
| 1.708 and above | Later curve strictly below at all five knots | Later curve strictly below at all five knots |

These inward-rounded common intervals omit some origins with definite results in an individual specification. Exact rational breakpoints and the classifications at the breakpoints themselves appear in `lorenz.json`. In the intermediate interval, a dominance comparison alone cannot determine which period has less relative dispersion. For example, at c=1/4 both specifications already have crossing curves even though CV and max/min still both fall. Agreement of those two summaries therefore does not imply Lorenz dominance on these division means.

These results use equal weight for each division after obtaining its population-weighted mean. They concern the dispersion of division scores. They neither estimate household inequality nor introduce new spatial observations. The original paper's scale has c=0. Every alternative c here is a stated change in normalization, applied identically to both periods. [Original endpoint data](https://arxiv.org/html/2611.23798v1#S4.T6)
