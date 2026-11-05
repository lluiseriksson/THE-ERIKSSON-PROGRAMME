# All actual fibres in the observation kernel (unit147)

At source354dd0de7facf8464b9e8e9b0f55c8edc641c2f6, a fresh exclusive Colab Linux CPU/high-RAM clone compiled PhysicalCycleKernel.lean. This removes the restriction to lifted scalar fields from the fibrewise kernel estimate. A is now ANY actual physical cochain in ker(actualCycleFullObservation cyclePairIntervals), and every transverse fibre, physical direction and internal coordinate is included. No divergence hypothesis is needed for this stage.

The vanishing actual Euclidean observation implies both pair sums vanish in each actual coordinate profile. The pre-existing scalar kernel-square theorem then gives (19/5)normSq(profile)<=energy(profile) for every profile. An exact arbitrary-field norm decomposition proves

    ||A||^2 = sum_z normSq(actualCycleFibreProfile A z).

Summing actual profile estimates derives

    (19/5)||A||^2 <= actualCycleLongitudinalEnergy A.

Here z ranges over all transverse fibres x physical directions x internal coordinates, and actualCycleLongitudinalEnergy is explicitly the sum of the existing four-cycle energy of these actual profiles. It is a derived inequality, not a supplied coercivity certificate or a restriction of A to a special ansatz. No new scalar theorem/novelty or independent authorship claimed.

Scope boundary: the remaining comparison actualCycleLongitudinalEnergy A <= actual flatGaugeHodgeK0CLM-plus-componentwiseWeightedRepairCLM energy is NOT yet Lean verified. The full physical-form kernel premise therefore remains pending. The explicit negative physical witness from unit146 remains separately verified. Do not combine these partial facts into an already formally closed full implication. No result about every partition, optimal rank or interacting/continuum mass gap.

Five oracle endpoints passed: actualCycleKernel_profile_pair_zero, actualCycleKernel_fibre_coercive, actualCycleFibre_norm_decomposition, actualCycleKernel_coordinate_sum_coercive, actualCycleKernel_norm_coercive. All depend only on propext/Classical.choice/Quot.sound. Both normal/optimized validators accepted5 actual oracle readouts and rejected3 actual mutations; every real exit sentinel0. Lean4.29.0-rc6, Mathlib07642720480157414db592fa85b626dafb71355b. Driver274.945762655s, build166.835230442s, oracle6.784877033s. FIRST fresh-clone verification, not paired terminal reproduction or independent scientific review.

Actual olean e4d6cfecddf19ea197c5869babefc7067b2ed8673261662278a4bcee171dd2e3; oracle6465f9068b226eba552a8ba7dccf740f974a4418f7c29dcabe836ab3c051a03a. Full private archive926cd81aa1b26a22014d8201a8306ef83b265dd3f79b5ef00b2a51c061885a64 (1240172bytes,46 inner hashes). Public archive485d850334f12a9414d4524e0132069a82644f666fa0c1ef2acbc05b0c7dc7cc (84517bytes,45 inner hashes) excludes third-party installer/binary asset and preserves full original sources/logs/report/oracle/validators/olean. Both manifests checked against extracted files. Driver147 SHA d7735b52d56aae03874e413fc4b0cb120a8eb6689eeec6f6a55882b090a68134.

First actual attempt failed because PiLp.norm_sq_eq_of_L2 takes the dependent family before the vector; the invocation treated A p as that family. Full original failed package4e458756301e024c8881713b199f645f1cb977272a0e76ec0ba0cc285768c1db and compiler log retained in D before editing. The correction uses rewriting to infer the family; statements unchanged. AttemptA380.230438753s. Both own sessions released; preparation disconnected, no Windows Lean/Lake/oracle/numerical computation. Final visible1765.41 units and0.26/hour; exact billed delta unknown.

Next prove the remaining full-energy comparison from the actual componentwise gradient identity and nonnegative transverse contributions, then close the physical-form kernel premise and pair the FINAL expanded source at a single SHA. Do not run another identical partial pair. Frozen reviewed PDFs, complete model reports, grades and pending exact-artifact permission unchanged. No new PDF/score/AIRR version. Original unrestricted critical rectangle question OPEN; common-refinement STOPPEDcounter3; PR29=20/41,TermSource=0.
