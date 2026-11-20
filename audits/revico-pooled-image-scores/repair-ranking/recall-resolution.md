# Why two extra counts suffice

The exhaustive table identifies nine sufficient pairs. They are exactly the Cartesian product of any one detection count and any one correction count, chosen independently from Chinese, English and pooled. The sufficiency has a short proof that does not depend on the model, the two precisions or F1.

Let a and b be the true-positive counts for one task, with 376 and 266 erroneous images in the respective languages. The equally weighted recall in percent is

    R(a,b) = 50 [ a/(376+e) + b/(266+e) ],   e = 10^-8.

The printed recall gives an interval of width 0.1 percentage points. With a known, increasing b by one changes R by 50/(266+e), which exceeds that width. Thus at most one b can occur; feasibility of the row guarantees at least one. With b known, consecutive a values are separated by 50/(376+e), again more than 0.1. A pooled disclosure already supplies the sum. In each case one count and the rounded recall suffice to recover the pooled true-positive total for that task. Applying the argument to detection and correction determines the conditional repair fraction whenever the pooled detected count is positive.

More generally for a group with weight w and known denominator n+e in a percent-weighted recall, consecutive admissible numerators are separated by 100w/(n+e) with all other groups fixed. An interval of width smaller than that spacing contains at most one candidate. If the weight, denominators or rounding change, the spacing must be checked again. For example, an unknown group of 501 erroneous images with weight one half and fixed zero recall in the other group has 502 possible numerators but only 501 printed values between 0.0 and 50.0 at one decimal. Some numerators then collide.

The exact enumeration in disclosure.json supplies necessity within the nine candidate reporting fields for this table. Each single field guarantees recovery for only one of the twenty models, Qwen3-VL-2B, whose repair fraction was already fixed. Each of the other 27 two-field options has a counterexample in at least one model. These claims concern identification for every possible disclosure consistent with a row; an individual disclosed value can be more informative.