# Local run-record staging

Historical Surface generators emit their custom JSON records here so they
cannot silently pollute the strict `run-manifests/` namespace.

`*.json` is intentionally ignored.  A staged record has no evidentiary or
promotion status.  Before committing its result, either:

1. create a strict schema-v1 execution manifest under `run-manifests/`, with
   genuine command, timestamps, environment, dependency and artifact hashes;
   or
2. define and register a domain-specific record schema plus a validator that
   independently checks every referenced artifact and acceptance predicate.

Never copy a staged JSON into `run-manifests/` merely to make it visible.
