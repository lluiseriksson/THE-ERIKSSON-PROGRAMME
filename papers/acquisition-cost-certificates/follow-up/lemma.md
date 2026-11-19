# What two exact whole-library moments can determine

Fix a library of N rows, a specified nonempty proper test set of size qN, and p=1−q. Scale the residual vector so that its squared Euclidean norm equals one. Write v for the fraction of its energy on the test set and k for the whole-library MAE divided by RMSE. Conditional on v, the attainable values of k form exactly the closed interval

    [(sqrt(v) + sqrt(1-v))/sqrt(N), sqrt(q v) + sqrt(p (1-v))].

To see this, take each row's absolute residual. In a group of g rows with Euclidean norm L, the attainable sums span [L, sqrt(g)L]. Concentrating energy on one entry and spreading it uniformly attain the endpoints. A continuous path of nonnegative unit vectors between them covers all intermediate sums, also for g=1 where the interval is a singleton. Scale the two groups to norms sqrt(v) and sqrt(1-v) and add their intervals. Locations within the groups and residual signs are unrestricted.

Let z be the whole-library RMSE divided by the full target standard deviation. A strict pass at threshold 1/2 requires v < q/(4z²). If this boundary lies strictly between 0 and 1, and k lies strictly within the displayed interval there, perturbing v slightly to either side produces residuals with exactly the same whole-library MAE and RMSE and opposite decisions on the *same specified test set*. This is a statement about the information contained in the two moments and the group sizes. The constructed predictions need not be predictions of a trained random forest or preserve other archived metrics.

For the rounded published decimals we test this for every admissible exact pair of moments. Put h=0.000005, k_min=max(0,a−h)/(r+h) and k_max=(a+h)/(r−h), where a,r are raw MAE and RMSE. If r≤h leave undecided. Use v_lo=q/[4(z+h)²] and v_hi=q/[4(z−h)²]. The lower end of the attainable k interval is always at most sqrt(2/N). Its upper end is concave as a function of v. We therefore require k_min²>2/N, 0<v_lo≤v_hi<1 and k_max below the upper end at both extremes. Every comparison can be decided exactly over rationals without taking a square root. Failing this conservative check makes no impossibility claim.

Analysis scope fixed before running: apply only to the 838 undetermined fixed-common-population cells from the reviewed integrated paper. Keep all unresolved and failed tests. A finding about individual cells does not classify the 149 open first-crossing comparisons under an actual fitted forest.
