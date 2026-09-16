# Physical FULL classification: next bounded diagnostic

Previous goal turn: progress, cold owner transport sealed/published in
72e645a223e0265e762c199d13c0f6b87ff9e2c2, ledger1221. No live runtime.

New PRE-VALIDATION files:
- tmp/NeumannFullFlagCastRepro.lean: Mathlib-only scale/cast cancellation.
- tmp/NeumannPhysicalFullFlagDraft.lean: computed Bool from actual
  Int.toNat(side)=ambientPeriod; same flag in incoming/outgoing masks;
  fine-to-block classification at B>0 and nonnegative block sides.

The draft keeps hm>0 and hfit<=N for both actual bond masks. It does not
remove FULL sides or posit a second independent flag. The scale lemma's
nonnegativity is supplied by physical side positivity, not a new smallness
window. No Green representation, summability or inverse claim is made.

Local textual guard passed on exactly these two files (0.0901621s,
15556608 observed peak RSS); import prefix check passed for the main draft.
No compiler test yet. A first guard invocation used str instead of Path and
was rejected before checking source; corrected invocation is the cited PASS.

Next queue, in one prepared CPU/high-RAM Colab diagnostic:
1. bootstrap pinned toolchain/Mathlib and verify exact source hashes;
2. lake env lean tmp/NeumannFullFlagCastRepro.lean;
3. only after repro PASS, lake build YangMills.RG.NeumannRectangleDirectionalMasks;
4. lake env lean tmp/NeumannPhysicalFullFlagDraft.lean;
5. exact five-name audit, preserve evidence, bounded HOT repair on first
   error if needed; cold promotion only after a diagnostic PASS.

No need to rebuild the mixed-owner module for this classification draft;
its only project import is the already cold-sealed directional masks.
The final consumer still must instantiate the mixed image family with this
computed flag. 20/41, TermSource=0 and window15 open remain unchanged.
