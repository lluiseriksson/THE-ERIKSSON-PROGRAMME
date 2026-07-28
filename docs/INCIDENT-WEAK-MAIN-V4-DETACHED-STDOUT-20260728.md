# Incident — weak-main v4 detached stdout (2026-07-28)

The first near v4 execution completed all 576 computations with zero failures
according to its separate progress stream.  It is not a certificate.

The process was launched through a bounded PowerShell tool call using shell
redirection.  When that enclosing call timed out, the spawned Python process
and workers continued, but their canonical stdout handle no longer transported
the eventual `emit()` output.  The terminal state was therefore:

```text
progress: END completed=576 failures=0
stdout:   empty
stderr:   empty
```

No transcript may be reconstructed from the progress file, which intentionally
contains no interval rows.  The empty stdout and its progress file are
preserved under `nonterminal-detached-stdout` names.

The rerun uses an independently started process with explicit
`RedirectStandardOutput` and `RedirectStandardError` file handles owned by that
process.  It starts from fresh canonical paths and repeats all 576 boxes.  No
mathematical parameter, target, dependency, or validator is changed.
