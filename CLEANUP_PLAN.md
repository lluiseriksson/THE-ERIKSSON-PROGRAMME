# CLEANUP_PLAN — keep the sound core, discard the sprawl

**Audited 2026-05-28 by `import`-graph analysis of the whole tree.** This is the
execution plan behind `FOUNDATIONS.md`: it says exactly which files to keep,
which to delete, how the kept files stay connected, and — crucially — the safety
rule that no deletion happens until the salvaged core is confirmed green.

It is staged because the repo is large (300+ `.lean` files) and the work cannot
be done safely in one shot.

---

## The central finding

The genuinely sound, Yang–Mills-relevant content is **structurally separable**
from the rest. Its entire import closure (verified by reading every `import`
line in the closure) touches **none** of `ClayCore/BalabanRG/**`,
`P8_PhysicalGap/BalabanToLSI`, or the vacuous `L8_Terminal/ClayTheorem` chain.

That closure is the new root `YangMillsCore.lean` (added 2026-05-28), a
`lean_lib` target you can build on its own:

    lake build YangMillsCore

If that is green with oracle `[propext, Classical.choice, Quot.sound]`, the core
is real and self-standing, and everything else can be deleted without touching
it.

---

## KEEP — the sound core (19 files, all sorry-free, axiom-free)

Reachable from `YangMillsCore.lean`:

```
YangMills/L0_Lattice/FiniteLattice.lean
YangMills/L0_Lattice/GaugeConfigurations.lean
YangMills/L0_Lattice/WilsonAction.lean
YangMills/L0_Lattice/GaugeInvariance.lean
YangMills/L0_Lattice/FiniteLatticeGeometryInstance.lean
YangMills/L1_GibbsMeasure/GibbsMeasure.lean
YangMills/P8_PhysicalGap/SUN_Compact.lean
YangMills/P8_PhysicalGap/SUN_StateConstruction.lean
YangMills/P8_PhysicalGap/MemLpLogIntegrability.lean      -- salvaged L·log·L envelope lemma
YangMills/ClayCore/SchurZeroMean.lean                    -- F0: ∫ tr U = 0
YangMills/ClayCore/SchurMomentVanishing.lean             -- Z_N rule: ∫ (tr U)^k = 0, N∤k  (NEW)
YangMills/ClayCore/SchurMixedMomentVanishing.lean        -- full Z_N grading: ∫ (tr U)^a conj(tr U)^b = 0, N∤(a−b)  (NEW)
YangMills/ClayCore/SchurEntryNAlitySelection.lean        -- Z_N rule at matrix-coefficient level: ∫ ∏U_{ij} ∏conj = 0, N∤(n−m)  (NEW)
YangMills/ClayCore/CenterVanishing.lean                  -- the reusable engine: ∫f=0 if f(ωI·U)=c·f(U), c≠1; all four rules as corollaries  (NEW)
YangMills/ClayCore/SchurPowerSumVanishing.lean           -- power-sum rule via the engine: ∫ tr(U^p) = 0, N∤p  (NEW)
YangMills/ClayCore/LeftInvariantVanishing.lean           -- general engine: ∫f dμ=0 for any left-invariant μ; bridges to lattice & U(1)  (NEW)
YangMills/ClayCore/SchurMixedPowerSumVanishing.lean      -- bigraded power-sum rule: ∫ tr(U^p)conj(tr(U^q))=0, N∤(p−q); D–S covariance  (NEW)
YangMills/ClayCore/SUOneDegenerate.lean                  -- boundary case: SU(1) trivial, ∫f d(sunHaarProb 1)=f(1); exposes U(1)-as-SU(1) degeneracy  (NEW)
YangMills/ClayCore/U1FourierOrthogonality.lean           -- U(1)=AddCircle character orthogonality: ∫ fourier n dHaar = δ_{n,0}; FIRST exact nonzero value  (NEW)
YangMills/ClayCore/SchurTwoSitePhase.lean
YangMills/ClayCore/SchurOffDiagonal.lean
YangMills/ClayCore/SchurNormSquared.lean
YangMills/ClayCore/SchurDiagPhase.lean
YangMills/ClayCore/SchurEntryOrthogonality.lean
YangMills/ClayCore/SchurEntryOffDiag.lean
YangMills/ClayCore/SchurL25.lean                         -- L2.5: ∫ |tr U|² ≤ N
YangMills/ClayCore/SchurPhysicalBridge.lean
```

Also keep at the root:

```
YangMillsCore.lean   lakefile.lean   lake-manifest.json   lean-toolchain   LICENSE
FOUNDATIONS.md   CLEANUP_PLAN.md   docs/legacy/AXIOM_FRONTIER.md   PETER_WEYL_ROADMAP.md
docs/legacy/ (historical status docs)   docs/
```

`L0_Lattice/SU2Basic.lean` is standalone and SU(2)-relevant — keep it for the
recommended SU(2) warmup even though the core does not yet import it.

---

## KEEP BUT DECOUPLE — the non-vacuous target (Stage 2)

These hold the *honest* target definitions but currently sit on top of the
sprawl (`ClayPhysical` imports `P6_AsymptoticFreedom.AsymptoticFreedomDischarge`):

```
YangMills/L8_Terminal/ClayPhysical.lean      -- IsYangMillsMassProfile, ClayYangMillsPhysicalStrong
YangMills/L7_Continuum/ContinuumLimit.lean   -- LatticeMassProfile, HasContinuumMassGap
```

**Stage 2 task:** extract the definitions that are worth keeping
(`LatticeMassProfile`, `HasContinuumMassGap`, `wilsonConnectedCorr`,
`ConnectedCorrDecay`, `IsYangMillsMassProfile`, `ClayYangMillsPhysicalStrong`)
into a new self-contained directory `YangMills/Target/` that imports only the
core + Mathlib, seal Leak A / Leak B per `FOUNDATIONS.md §3`, then delete the
heavy originals. Until that extraction compiles, do **not** delete L7/L8.

---

## DISCARD — the sprawl (routes only to the vacuous target)

Delete by path. Everything below feeds only `∃ m > 0` (`ClayYangMillsTheorem`)
or `ClayYangMillsStrong`, both proved vacuous in `FOUNDATIONS.md §1`:

```
YangMills/ClayCore/BalabanRG/**                 -- ~150 P81/Coherence/Packet/Frontier/Bridge files
YangMills/ClayCore/*.lean (NOT in the KEEP list) -- ClayAuthentic, ClayWitness, ClayTheorem, KPSmallness,
                                                 --   AbelianU1Witness (models U(1) as the TRIVIAL group SU(1) —
                                                 --   see SUOneDegenerate.lean), etc.: all route to the vacuous target
YangMills/P8_PhysicalGap/**                      -- EXCEPT the 3 kept above
YangMills/L2_Balaban/**
YangMills/L3_RGIteration/**
YangMills/L4_LargeField/**   L4_WilsonLoops/**   L4_TransferMatrix/**
YangMills/L5_MassGap/**      L5_KPDecay/** (P5)
YangMills/L6_FeynmanKac/**   L6_OS/**
YangMills/L7_Continuum/**                         -- EXCEPT ContinuumLimit.lean (decouple first)
YangMills/L8_Terminal/**                          -- EXCEPT ClayPhysical.lean (decouple first)
YangMills/P2_MaxEntClustering/**
YangMills/P3_BalabanRG/**
YangMills/P4_Continuum/**
YangMills/P5_KPDecay/**
YangMills/P6_AsymptoticFreedom/**
YangMills/P7_SpectralGap/**
```

Root scratch files to delete:

```
Test.lean   TestC71Full.lean   TestC72Proto.lean   OracleC69.lean   OracleC96.lean
README.proposed.md                                -- folded into the new README.md
```

The ~25 BFS-dead axioms catalogued in `docs/legacy/AXIOM_FRONTIER.md` live inside the
discarded files and disappear with them. The single "live" axiom
`lsi_normalized_gibbs_from_haar` (in `BalabanToLSI.lean`) also goes; it only ever
fed the vacuous target.

Also rewrite the old root `YangMills.lean`: either delete it or reduce it to
`import YangMillsCore` (the script does the latter), so a bare `lake build` no
longer drags in deleted modules.

---

## SAFETY PROTOCOL (do not skip)

1. Work on a branch: `git switch -c cleanup/sound-core`.
2. **Build the core first, before any deletion:** `lake build YangMillsCore`.
   Must be green. If not, fix imports — do not delete anything yet.
3. Only then delete the DISCARD set.
4. Point `YangMills.lean` at the core; `lake build` again to confirm nothing
   dangling remains.
5. `#print axioms` spot-check the headline core lemmas (see below).
6. Commit + push the branch; open a PR; keep `main` intact until the branch is
   green in CI.

`docs/legacy/cleanup_and_push.ps1` performs steps 1–6 in order and **aborts before
deleting** if `lake build YangMillsCore` fails. Read it before running.

Oracle spot-checks:

```lean
import YangMillsCore
#print axioms YangMills.sunHaarProb_trace_re_integral_zero
#print axioms YangMills.sunHaarProb_trace_pow_complex_integral_zero
#print axioms YangMills.ClayCore.sunHaarProb_trace_normSq_integral_le
-- each expected: [propext, Classical.choice, Quot.sound]
```

---

## Stages

- **Stage 1 (done, 2026-05-28):** inventory; verify the core closure is
  sorry/axiom-free and sprawl-free; add `YangMillsCore.lean` + `lean_lib`;
  write this plan and the new README; prepare the cleanup script.
- **Stage 2:** confirm `lake build YangMillsCore` green on the user's machine;
  extract the non-vacuous target into `YangMills/Target/` (decouple L7/L8).
- **Stage 3:** run the deletion (script), rewire `YangMills.lean`, push the
  branch, open the PR.
- **Stage 4:** start the real frontier from `FOUNDATIONS.md §6` F2 onward, or a
  U(1)/SU(2) end-to-end warmup.

Nothing in Stages 2–4 should reintroduce a dependency on the discarded sprawl.
```
