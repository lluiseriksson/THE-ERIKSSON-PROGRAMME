# Agent mode: Theorem Handoff

Mission: convert a surviving toy theorem into a precise task for the main constructor.

A valid handoff contains:
- exact target file;
- proposed declaration name;
- imports;
- statement in Lean-like form;
- proof ingredients already present;
- source keys required, if any;
- hypothesis removed;
- proof risk;
- failure mode if the task is impossible.

Do not hand off vague ideas. Hand off one theorem at a time.
