# F5 hot v2 — six audited declarations, then first owner-action error

Draft source `a289ee24dc41c25f2480c408de45b3105b09ce71`.
Runner `c8e1bbacd4447034c3ce124d455a4e2a74b1b450`.
Retained cold source `5138e9bd4bc88797c91c21df5bb5c630c71600ca`.
Started once 2026-09-05T11:16:40.540590Z, launcher PID42196.

Archive SHA256 `966eaa348af6724008e8b3710d9b3836fa203f967fbb50a23d206ba53231b876`.
Downloaded bytes matched; all 33 archived files, recorded log hashes and
compiled output hashes checked locally. Exact exit vector: nine zeros,
then one at owner_action_draft. This is HOT evidence, not a cold seal.

| Stage | Exit | Seconds |
|---|---:|---:|
| Mathlib-only repro | 0 | 6.623895629000799 |
| sealed prerequisites | 0 | 331.3868860470011 |
| real-slice transport | 0 | 13.369573486001173 |
| full point-source fibre bound | 0 | 15.314663406999898 |
| owner action | 1 | 9.902168661999895 |

The four real-slice and two point-fibre declarations have the exact allowed
trio {Classical.choice, Quot.sound, propext}. They do not include the failed
owner-action declaration. Its raw output includes Lean's error-recovery
sorryAx; that declaration is rejected, not counted as a passed oracle.

First error: `tmp/FullGreenOwnerFibreActionDraft.lean:85:10`, rewrite did
not find `sourceOwner source` underneath the beta-unreduced kernel lambda.
Raw owner log SHA256 `5981701e696b3449e1157d2e8df0b755508dc90174d449d00b9b2d1b85d203a3`.
Repair source cee1f6d36ea8d81c5f301860f0a349b14efac47d states the type of hk
explicitly before rewriting; no statement, constant or hypothesis changes.
The separate v3 runner first exercises this step without project imports,
then reruns only the failed owner action after verifying this prefix.

No PRE-VALIDATION retirement, root build, regional/derivative B0 or
window15 attainment follows. Counters stay 20/41, TermSource=0.
