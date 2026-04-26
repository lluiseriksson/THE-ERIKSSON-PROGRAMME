# BUILD_VERIFICATION_PROTOCOL.md

**Audience**: any agent or human with a working Lean 4 + Mathlib + project build environment
**Author**: Cowork agent (Claude), produced 2026-04-25 (Phase 451)
**Subject**: step-by-step protocol for verifying that the 2026-04-25 Cowork session output (38 Lean blocks + 17 PR-ready files) actually `lake build`s
**Companion**: `MATHLIB_SUBMISSION_PLAYBOOK.md` (PR-focused, complementary)

---

## 0. Why this document exists

The 2026-04-25 Cowork session produced **~322 Lean files** across 38 long-cycle blocks (L7-L44) **plus 18 Mathlib-PR-ready files** in `mathlib_pr_drafts/` (post-Phase 460 update: L43 now has 4 files, +1 from Phase 458; PR-ready 18 from Phase 453), **without running `lake build`** during the session (the workspace lacks `lake`).

The Codex daemon may have been validating in parallel, but **no end-to-end Cowork-side build verification is recorded**.

This document gives the next agent / human (with a build environment) a deterministic protocol to:

1. Verify the project's existing core (`YangMills/ClayCore/`) still builds clean.
2. Verify the 35 Bloque-4 blocks (L7-L41) build clean.
3. Verify the 3 physics-anchoring blocks (L42-L44) build clean.
4. Verify the 17 PR-ready files compile against current Mathlib master.
5. Verify the 0-sorry discipline (no spurious sorries slipped in).
6. Verify the `#print axioms` discipline holds (no unexpected axioms).

Estimated total time: **2-4 hours** if no major issues; **8-12 hours** if multiple sorry-catches or namespace collisions need polishing.

---

## 1. Setup checklist (do once)

```bash
# 1. Clone the project (if not already).
cd ~/work
git clone <project-repo>
cd THE-ERIKSSON-PROGRAMME

# 2. Verify project builds with current Mathlib pin.
lake build  # expect success or known-pin failures

# 3. Note the Mathlib pin for later reference.
cat lakefile.toml | grep mathlib  # or lakefile.lean equivalent

# 4. Optional: clone Mathlib master separately for PR verification.
cd ~/work
git clone https://github.com/leanprover-community/mathlib4.git
```

---

## 2. Phase 1: Core build verification (~30 min)

```bash
cd THE-ERIKSSON-PROGRAMME

# Build the core. Should succeed with no errors.
lake build YangMills.ClayCore

# Verify oracle discipline.
echo "open YangMills.ClayCore in #print axioms wilson_loop_normSq_integral_eq_one" | lean --run
# Expected: [propext, Classical.choice, Quot.sound]

# If any axiom outside this triple appears, file a regression issue.
```

**Success criteria**: zero `error:` lines, all theorems print `[propext, Classical.choice, Quot.sound]`.

**If failure**: regression in the core. Document and roll back to the last known-good commit.

---

## 3. Phase 2: Bloque-4 blocks L7-L41 (~1 hour)

```bash
# Build each block in order. Each should succeed.
lake build YangMills.L7_Multiscale.MasterCapstone
lake build YangMills.L8_LatticeToContinuum.MasterCapstone
lake build YangMills.L9_OSReconstruction.MasterCapstone
lake build YangMills.L10_OS1Strategies.MasterCapstone
lake build YangMills.L11_NonTriviality.MasterCapstone
lake build YangMills.L12_ClayMillenniumCapstone.ClayMillenniumLeanRealization
lake build YangMills.L13_CodexBridge.CodexBridgePackage
lake build YangMills.L14_MasterAuditBundle.SessionMasterCapstone

# L15-L29: substantive deep-dive blocks.
lake build YangMills.L15_BranchII_Wilson_Substantive.Capstone
lake build YangMills.L16_NonTrivialityRefinement_Substantive.Capstone
lake build YangMills.L17_BranchI_F3_Substantive.Capstone
lake build YangMills.L18_BranchIII_RP_TM_Substantive.Capstone
lake build YangMills.L19_OS1Substantive_Refinement.Capstone
lake build YangMills.L20_SU2_Concrete_YangMills.Capstone
lake build YangMills.L21_SU2_MassGap_Concrete.Capstone
lake build YangMills.L22_SU2_BridgeToStructural.Capstone
lake build YangMills.L23_SU3_QCD_Concrete.Capstone
lake build YangMills.L24_SU3_MassGap_BridgeStructural.Capstone
lake build YangMills.L25_SU_N_General.Capstone
lake build YangMills.L26_SU_N_PhysicsApplications.Capstone
lake build YangMills.L27_TotalSessionCapstone.Capstone
lake build YangMills.L28_StandardModelExtensions.Capstone
lake build YangMills.L29_AdjacentTheories.Capstone

# L30-L41: creative attack programme.
for L in 30 31 32 33 34 35 36 37 38 39 40 41; do
  lake build YangMills.L${L}_CreativeAttack_*.Capstone
done

# L41 has the grand statement as its capstone:
lake build YangMills.L41_AttackProgramme_FinalCapstone.AttackProgramme_GrandStatement
```

**Success criteria**: each `lake build` returns successfully.

**If failure on a specific block**: read the error message; the issue is likely:
- A new Mathlib lemma renamed (e.g., `pow_le_pow_left` → `pow_le_pow_left₀`).
- An import statement that has moved.
- A typeclass instance no longer being synthesised.

Fix per-error and continue.

---

## 4. Phase 3: Physics-anchoring blocks L42-L44 (~30 min)

```bash
# L42: lattice QCD anchors (continuous view of confinement).
lake build YangMills.L42_LatticeQCDAnchors.BetaCoefficients
lake build YangMills.L42_LatticeQCDAnchors.RGRunningCoupling
lake build YangMills.L42_LatticeQCDAnchors.MassGapFromTransmutation
lake build YangMills.L42_LatticeQCDAnchors.WilsonAreaLaw
lake build YangMills.L42_LatticeQCDAnchors.MasterCapstone

# L43: center symmetry (discrete view) — 4 files post-Phase 458.
lake build YangMills.L43_CenterSymmetry.CenterGroup
lake build YangMills.L43_CenterSymmetry.DeconfinementCriterion
lake build YangMills.L43_CenterSymmetry.MasterCapstone
lake build YangMills.L43_CenterSymmetry.CenterElementNonTrivial  # Phase 458, closes the L43 hypothesis-conditioning gap

# L44: large-N expansion (asymptotic view).
lake build YangMills.L44_LargeNLimit.HooftCoupling
lake build YangMills.L44_LargeNLimit.PlanarDominance
lake build YangMills.L44_LargeNLimit.MasterCapstone
```

**Success criteria**: all 11 files build successfully.

**Specifically watch for**:
- L43 `CenterGroup.lean` — the `polyakov_invariant_implies_zero` theorem uses `linear_combination`; if that tactic name has drifted, swap.
- L43 `MasterCapstone.lean` — the `bundle_SU2` definition uses `linear_combination` to prove `(-1 : ℂ) ≠ 1`.
- L43 `CenterElementNonTrivial.lean` (Phase 458) — uses `Complex.exp_eq_one_iff` + `Int.le_of_dvd`. The proof structure depends on the exact statement of `Complex.exp_eq_one_iff`; if its existential form differs (e.g., `∃ n : ℤ, x = ↑n * (2 * π * I)`), adjust the destructuring accordingly.
- L44 `PlanarDominance.lean` — uses `nlinarith` heavily for the genus suppression bounds.

---

## 5. Phase 4: 0-sorry verification (~10 min)

```bash
# Search the entire YangMills directory for any sorry.
grep -rn "sorry\|admit\b\|@[admit]" YangMills/ | grep -v "//\|--"

# Expected output: empty.
```

**Critical verification**: the session maintained 0 sorries despite **2 sorry-catches** (Phase 437 in L43, Phase 444 in L44). Both were resolved by hypothesis-conditioning and theorem reformulation — neither admitted a sorry.

**If any sorry is found**: regression. The session-end state must have 0 sorries. Either the file was modified post-session or the original commit did contain a sorry that was missed.

---

## 6. Phase 5: `#print axioms` verification (~30 min)

For the project's master capstones, verify axiom-cleanliness:

```bash
# Sample for each block's master theorem.
for thm in \
    "YangMills.L7_Multiscale.l7_master_capstone" \
    "YangMills.L12_ClayMillenniumCapstone.clayMillennium_lean_realization" \
    "YangMills.L13_CodexBridge.cowork_codex_full_attack" \
    "YangMills.L41_AttackProgramme_FinalCapstone.the_grand_statement" \
    "YangMills.L42_LatticeQCDAnchors.L42_master_capstone" \
    "YangMills.L43_CenterSymmetry.L43_master_capstone" \
    "YangMills.L44_LargeNLimit.L44_master_capstone"
do
    echo "Checking $thm..."
    echo "#print axioms $thm" | lean --run
done
```

**Expected output for each**: `[propext, Classical.choice, Quot.sound]`.

**If unexpected axioms**: file a regression issue. The 0-axiom-outside-Experimental discipline must hold.

---

## 7. Phase 6: Mathlib-PR-ready files (~3-6 hours)

For each of the 17 files in `mathlib_pr_drafts/`, follow `MATHLIB_SUBMISSION_PLAYBOOK.md` §2:

1. Drop file into Mathlib master clone at the appropriate path (per playbook §2.2).
2. `lake build` against current Mathlib master.
3. Address tactic-name drift (per playbook §2.3.1).
4. Verify `#print axioms` clean (per playbook §2.5).
5. Run `#lint` and address warnings.

**Time estimate per file**: 30-45 minutes for simple files (`LogTwoLowerBound_PR.lean`); up to 2-3 hours for complex files (`MatrixExp_DetTrace_DimOne_PR.lean`).

**Total estimate**: 10-13 hours for all 17 files (per playbook §6).

---

## 8. Phase 7: Cross-references verification (~30 min)

Verify that surface-doc cross-references are consistent:

```bash
# README.md §11 should reference 38 blocks.
grep -c "38 long-cycle\|L7-L44" README.md  # expect ≥ 1

# BLOQUE4_LEAN_REALIZATION.md should reference 38 blocks.
grep -c "38 long-cycle\|L7-L44\|L42.*L43.*L44" BLOQUE4_LEAN_REALIZATION.md  # expect ≥ 1

# COWORK_FINDINGS.md should have Findings 001-023.
grep -c "## Finding 0[0-2][0-9]" COWORK_FINDINGS.md  # expect = 23

# All surface docs should mention triple-view.
grep -l "triple-view\|L42.*L43.*L44" *.md
# Expected: at least FINAL_HANDOFF.md, STATE_OF_THE_PROJECT.md,
# NEXT_SESSION.md, SESSION_2026-04-25_FINAL_REPORT.md,
# BLOQUE4_LEAN_REALIZATION.md, README.md, TRIPLE_VIEW_CONFINEMENT.md.
```

---

## 9. Success report template

After completing phases 1-7, fill in:

```
=== Build Verification Report — 2026-04-25 Session ===

Phase 1 (core):                         [PASS / FAIL details]
Phase 2 (Bloque-4 L7-L41):              [PASS / specific failures: ...]
Phase 3 (physics-anchoring L42-L44):    [PASS / specific failures: ...]
Phase 4 (0-sorry):                      [PASS / found sorries in: ...]
Phase 5 (#print axioms):                [PASS / unexpected axioms in: ...]
Phase 6 (Mathlib-PR-ready):             [N/M built clean, M-N drift cases noted]
Phase 7 (cross-references):             [PASS / inconsistencies: ...]

Total verification time: ___ hours.
Issues filed: ___ (list).
Recommended fixes: ___ (list).
```

File the report to `BUILD_VERIFICATION_REPORT_<date>.md` for future reference.

---

## 10. Honest meta-caveat

This protocol is itself **untested** — it was produced inside the same Cowork session that produced the artifacts being verified, so the protocol's correctness has the same untested status as the artifacts.

In particular:
- The exact Lean module paths in §3 are based on best knowledge of the project structure; some may have minor differences (e.g., the master capstone might be named `Capstone` rather than `MasterCapstone` in some L blocks).
- The `lake` invocations assume the project's `lakefile.toml` exposes the relevant module names; if not, adjust to actual exports.
- The `#print axioms` invocations are syntactically correct but may need adjustment for Lean's `--run` flag behavior in the user's environment.

**Treat this protocol as a structured starting point, not a fully-verified script.** The first run will likely surface several path adjustments; subsequent runs will be smoother.

---

*Cross-references*: `MATHLIB_SUBMISSION_PLAYBOOK.md` (PR-focused, complementary), `BLOQUE4_LEAN_REALIZATION.md` (block-by-block detail), `mathlib_pr_drafts/INDEX.md` (PR queue), `PHASE_TIMELINE.md` (chronology of what was produced).
