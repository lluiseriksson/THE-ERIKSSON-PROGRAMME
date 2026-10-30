# Exact historical acknowledgment preparation

The public predecessor was registered separately after the human's explicit
single-entry approval. That approval does not approve a historical grant.

The original intake wrapper stopped on an older account-level terms/privacy
version. The native `authorize-historical-revision` contract instead records
the current terms/privacy with the actual external human instruction for the
exact artifact. This wrapper preserves that contract: it does not update the
account, the database directly, native authorization code, permissions or quotas.

`inspect` is read-only apart from protected evidence files and reports the stored
and current versions separately. It does not treat inspection as acknowledgment.
`deposit` requires a separately supplied, SHA256-pinned actual human reply with
explicit current terms/privacy and exact one-artifact grant confirmation. A
catalogue approval, stale account acknowledgment or broad autonomous instruction
does not satisfy that requirement. The native CLI still issues the grant; its
24-hour lifetime, one use and limited scopes remain unchanged. Publication,
editorial acceptance and named-provider transfers remain separate.

Required private JSON fields: `paper_id`, `sha256`, `terms_version`,
`privacy_version`, `accepted_terms`, `read_privacy`, `approve_exact_grant`,
`source_reference`, `actual_human_answer`, `recorded_at`. The three boolean fields
must be true based on an actual new human reply. No completed approval is supplied
in this repository. Never copy private authorization files, grants or tokens here.

No grant, deposit or publication is established by this preparation. The frozen
PDF remains b37f2fe86b7a8a526ad02f8b28491c300a9ff72d5653536bc5532e8c9468ed8f.
This operational wrapper does not incorporate the subsequent Hodge theorem.
