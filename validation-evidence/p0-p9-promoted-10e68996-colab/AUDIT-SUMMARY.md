# P0--P9 promoted prefix-Green graph: Colab seal

- Status: `PASS`
- Source checkpoint: `10e6899692defec09b416d73a64ec36ee5cc7393`
- Runner revision: `p0-p9-promoted-10e6899692de-v1`
- Runner transport SHA-256: `6FA5030D14654E452324F5E8E94BDDC7929E2D0B982C6FD957245E8074668FB7`
- Mathlib pin: `07642720480157414db592fa85b626dafb71355b`
- Runtime: Colab Pro+ CPU/high-RAM (`50.99 GiB`), opened
  `2026-08-20T19:42:23.903119Z`, closed
  `2026-08-20T20:57:46.302941Z`.
- Evidence records: `56`; nonzero exits: `0`; aggregate recorded stage time:
  `4521.861 s`.
- Numbered focal/audit queue: `39/39` stages exited `0`.
- Axiom headers: `200/200`; every set is a subset of
  `{propext, Classical.choice, Quot.sound}`; neither `sorryAx` nor
  `ofReduceBool` occurred.
- Canonical evidence-payload SHA-256 (before the terminal newline):
  `49F216701E4B0BEB22BF4FB8442F2699FF471B2170111ED9BF095E4064418562`.
- Downloaded archive SHA-256:
  `45443DB78A7FE08AD956462EEA6E992D2737F41B18940BF4F9C8E643A476A782`.

The archive was downloaded before the runtime was disconnected and its raw
SHA-256 was rechecked on Windows.  The contained JSON was parsed locally:
its source, runner, Mathlib pin, record count and exit codes match this
summary.  The runtime was then disconnected and deleted without rerunning the
cell.

This seal validates the public P0--P9 prefix-Green graph only.  It does not
produce the uniform CMP99 (3.42) pair, the four source-localized actions, the
C6c.4 supremum, window-15 attainment, any terminal field or a `TermSource`
inhabitant.  Counters remain exactly `20/41`, `TermSource = 0`.
