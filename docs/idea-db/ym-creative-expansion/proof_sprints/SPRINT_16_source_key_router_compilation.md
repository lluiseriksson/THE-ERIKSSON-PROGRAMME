# Sprint 16 — Source-key router compilation

Goal: turn `SOURCE-KEY-ROUTER.md` into deterministic prompts and forbid unrelated source browsing.

Inputs:
- one proof card key;
- its allowed source keys;
- its `do_not` list.

Output:
- one mission prompt;
- one source extraction worksheet;
- one expected Lean theorem statement.

Failure: an agent opens a source key not routed to the proof card before exhausting the listed keys.
