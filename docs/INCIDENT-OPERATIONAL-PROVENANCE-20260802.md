# Operational governance provenance incidents — 2026-08-02

**Purpose.**  This is the compact explanatory record for three operational
rules adopted on 2026-08-02.  The normative rules live in
[`OPERATIONAL-GOVERNANCE-CHARTER.md`](OPERATIONAL-GOVERNANCE-CHARTER.md); this
record says which measured incident paid for each rule.  It makes no
mathematical claim and does not alter or certify PR #51, PR #44, or PR #54.

**Evidence boundary.**  The dispatch, auditor response, cleanup count, policy
block, line-ending count, and hash pairs were reported by the owner during
operational coordination.  They are recorded as an **incident report**, not as
an independently certified audit transcript.  Repository history separately
confirms that `8eb733ddd54eeb28849cdfa8d9d8e7c09c6d0363` is a direct child of
`dae703ddb5e5d0f71e14bfd147c781f530d736cd` and adds five lines to
`docs/OPERATIONAL-GOVERNANCE-CHARTER.md`.

## 1. External reading on a moving branch

PR #51 was dispatched to external reader (33) at
`dae703ddb5e5d0f71e14bfd147c781f530d736cd`.  While the reading was in flight,
the branch advanced to `8eb733ddd54eeb28849cdfa8d9d8e7c09c6d0363` through the
five-line documentation commit `Require explicit audit clone cleanup
reporting`.  The reader detected that the SHA no longer matched and stopped
without issuing a verdict on a moving target.

**Rule purchased.**  Freeze branch and PR body during external reading;
declare known defects as carve-outs for later repair; identify the review
object in both commission and verdict by SHA, body-capture method, byte
representation and normalization, and hash.

## 2. Disposable clone accumulation

Nine disposable clones remained in `%TEMP%` after audits.  Eight dead
`pr39-*` clones were identified and removed in a controlled cleanup; they are
not retained evidence and are not reported as still present.  Cleanup of the
ninth clone was blocked by policy, so its outstanding disposition is:

`CLEANUP-PENDING: C:\Users\lluis\AppData\Local\Temp\pr51-audit-b3c68b391c264c698ebb93d5240e4492`

**Rule purchased.**  Remove every disposable clone when its task ends.  If
removal fails, report the exact absolute path on a separate `CLEANUP-PENDING:`
line, and keep disposable garbage distinct from deliberately retained
evidence.

## 3. Textual hashes across line-ending regimes

The frozen PR #51 body differed by 68 CRLF conversions in the Windows
checkout and matched after normalization to LF.  The reported SHA-256 pairs
were:

| Object | Git blob / LF bytes | Windows checkout / CRLF bytes |
| --- | --- | --- |
| PR body | `7eecefbe492a80317e85f4b4cc360109e334bb3905cd6b9d5e2808387a64198c` | `5fc5e087456b3fcef6235257ce1fd813aff2910b2b65c337585b59df911e8143` |
| Baseline | `09ca858cd7bef66b4b78e6ca2199a17add3a6064b5483e54a7cf0d6c25dfce0e` | `b846059fb0c6525999582132c3a945ad3b1dfbaa28faeec41a4f0ea3769a3d22` |

**Rule purchased.**  Every textual hash declares its byte representation and
normalization.  A text has no unique, context-free hash without that byte
regime.

## Existing 300-second transport incident

This record does not replace or paraphrase away the earlier evidence for the
300-second agent/MCP ceiling.  The charter retains the original PR #35 timeout
measurement and terminal phased-verdict links and identifies the two
approximately 300-second outer-transport expirations that paid for that rule.
