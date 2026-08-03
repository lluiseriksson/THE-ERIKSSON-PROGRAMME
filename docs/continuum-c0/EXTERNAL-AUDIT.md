# CONTINUUM-C0 external audit

## Accepted Opus audit

Profile check immediately before the audit:

```json
{
  "loggedIn": true,
  "authMethod": "claude.ai",
  "apiProvider": "firstParty",
  "email": "masterythief@gmail.com",
  "subscriptionType": "max"
}
```

Invocation properties:

- CLI model: exact `claude-opus-5`;
- effort: `max`;
- output: JSON;
- no session persistence;
- API/auth environment variables removed;
- `ANTHROPIC_SMALL_FAST_MODEL=claude-opus-5`, so any CLI auxiliary pass uses
  the same required model;
- one read of `OPUS-AUDIT-PACKET.md`, no repository mutation or delegation.

Accepted telemetry:

```json
{
  "is_error": false,
  "num_turns": 2,
  "modelUsage": {
    "claude-opus-5": {
      "inputTokens": 777,
      "outputTokens": 8778,
      "cacheReadInputTokens": 24754,
      "cacheCreationInputTokens": 3854
    }
  }
}
```

`modelUsage` contains exactly one model key: `claude-opus-5`.

Verdict: **PASS**.

The auditor found:

- no stored comparison functional or state field;
- `AlgebraCompatibility.map_one` blocks the zero embedding;
- the discrete truncated-correlation premise does not assume factorization
  of the limit;
- the `1/8450` calculation and consistency of the `10⁻⁶` example are sound;
- the strong-coupling obstruction is disclosed rather than used as a
  continuum claim; and
- identity reflection, constant-coupling mechanics, and missing geometric
  producers are stated at their true conditional strength.

Residual non-blocking risk: there is no joint witness yet for the full
physical bundle of algebraic, geometric, scale-convention, and eventual
anchor-separation compatibility. The charter lists these as open producers,
so the bounded C0 contract remains honest.

## Second Opus audit after the two-point theorem

The updated source-level audit used the same verified profile and exact model
constraints. Accepted telemetry:

```json
{
  "is_error": false,
  "num_turns": 42,
  "modelUsage": {
    "claude-opus-5": {
      "inputTokens": 9285,
      "outputTokens": 40358,
      "cacheReadInputTokens": 2453916,
      "cacheCreationInputTokens": 163905
    }
  }
}
```

`modelUsage` again contains exactly one key, `claude-opus-5`. Verdict:
**PASS**, with no blocking finding.

The auditor independently checked that the canonical pair first discharges
the thermodynamic-volume geometry at fixed separation index, including
distinctness and exact no-wrap distance, before the outer index tends to
infinity. It also identified three wording/strength issues:

1. the canonical correlation theorem is not wired as an instance of the
   generic `WeakLimit` embedding theorem;
2. the first discharged specialization used `β=0`; and
3. the physical-spacing reading was prose rather than a formal theorem.

All three were handled after the audit without adopting an external proof:
the packet now distinguishes the two interfaces, the example is strengthened
and locally re-elaborated at the existing positive coupling `β=10⁻⁶`, and
`tendsto_axisPairPhysicalSeparation_reciprocal` formally proves that spacing
`1/(k+1)` with offset `2k` tends to physical separation `2`. The final local
oracle includes these headlines.

## Fable attempt

The required `masterythief` profile check passed, including
`loggedIn=true` and `email=masterythief@gmail.com`. The initial Fable 5 High
request returned HTTP 429 with `is_error=true` and no verified Fable-5
response.  After the independent audit exposed the precise uniform-in-`β k`
proof bottleneck, the one permitted retry was made against that bounded
source region.  It also returned HTTP 429, with empty `modelUsage` and
`verified_fable_5=false`.  Neither attempt contributed a claim or proof, and
there will be no further retry.

## Independent post-delivery audit and repair target

An independent audit of published commit
`72cae3d25b3ec7e00dfdc4836c4f026c5a215981` rechecked the exact RG distance
theorem, the closed positive-coupling example, the KP obstruction, and the
absence of project axioms.  It confirmed those claims, but identified a real
semantic defect in the endpoint: the observable separation varied with `k`
while the Gibbs state remained fixed at `β=10⁻⁶`; the reciprocal-spacing
limit was only a separate arithmetic theorem.

The repair is source-level rather than rhetorical:
`tendsto_d4ScaleIndexedTruncatedCorrelation_zero` now constructs the actual
state at `β k` for an arbitrary schedule uniformly confined to the explicit
KP window, and `tendsto_d4ScaleIndexedTwoPointData` pairs that correlation
with the physical-separation limit in one endpoint.  The charter now puts the
still-missing physical law relating `β k` to `scale.spacing k` first among
the open obligations.  `CorrelationGeometry.lean` is explicitly labelled as
an alternative conditional adapter, not part of the canonical endpoint.

## Exact Opus audit after the scale-indexed repair

A preliminary source audit correctly detected that the packet had been
updated to claim 28 oracle headlines while the recorded transcript still
contained 26.  That run was not accepted as contractual evidence because its
`modelUsage` included an auxiliary model in addition to `claude-opus-5`.
The oracle was rerun locally, the two new headlines were recorded, and the
packet was corrected before the accepted audit.

The final audit used
`CLAUDE_CONFIG_DIR=$HOME\.claude-profiles\masterythief`,
`ANTHROPIC_SMALL_FAST_MODEL=claude-opus-5`, removed API/auth environment
variables, and invoked the exact requested model and maximum effort without
session persistence.  Accepted telemetry:

```json
{
  "is_error": false,
  "num_turns": 58,
  "modelUsage": {
    "claude-opus-5": {
      "inputTokens": 13123,
      "outputTokens": 45402,
      "cacheReadInputTokens": 4085486,
      "cacheCreationInputTokens": 159034
    }
  }
}
```

`modelUsage` contains exactly one key, `claude-opus-5`.  Verdict:
**PASS**, with no blocking finding.

The auditor independently recomputed the uniform axis constants, verified
that `β k` reaches the actual Gibbs measure, checked the nested
volume-before-scale geometry and the `1/8450` wall, and compared the complete
28-headline oracle output with the checked-in transcript.  Its nonblocking
findings are now explicit frontiers:

- the canonical two-point theorem is not an instance of the generic weak
  limit factorization lane;
- `GeometricScalingCompatibility` does not derive its numerical radius from
  the embedded support;
- the RP transport still admits identity reflection;
- candidate laws and tightness are trivial for the constant mechanics
  witness;
- the paired endpoint instantiates no physical scale convention and carries
  no schedule-specific information; and
- no finite-separation nonvanishing or lower bound is proved.
