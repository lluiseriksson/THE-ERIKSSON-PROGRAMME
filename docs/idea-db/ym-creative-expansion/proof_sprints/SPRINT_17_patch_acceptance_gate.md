# Sprint 17 — Patch acceptance gate

Use the scoring rubric before merging agent output.

Reject immediately if:
- no field/hypothesis is removed;
- new consumers are added;
- source status is promoted without exact formula and dictionary;
- the patch claims theorem_checked without build/oracle evidence.

Accept docs-only patches only if they sharpen a blocker enough that the next theorem statement is unambiguous.
