# `poincare_wall` W-3 review release manifest

Date: 2026-07-14

## Isolation and provenance

- Frozen scientific base: `12ca1a87`, sealed by `64969b35`.
- Frozen external PDF: `poincare_wall (1).pdf`, SHA-256
  `372055E04F70F3CCF2D9FAB4D5D185FE3BF391EBD78819877075518B044BCEA1`.
- Local review branch: `poincare-wall-w3-review`, created directly from
  `64969b35` with no merge from the C6/B-2 branch.
- W-3 code commit: `829fab52`.
- Isolated oracle-query commit: `90ed3585`.
- Scientific manuscript commit: `009da5b0`.
- Reviewed artifact commit: the commit containing this manifest, the
  transcript, and `poincare_wall_w3_review.pdf`.

The committed delta does not modify `CURRENT-STATE.md`,
`docs/VERIFICATION-LEDGER.md`, any C6 paper or charter, or any terminal
Wilson-obstruction module.  The recursive W-3 import closure adds no
C6-specific import edge.  The foundational `WilsonAction` import already
present in the frozen base remains unchanged.

## Certified scope

The endpoint is exactly

```text
not (VolumeUniformQuotientPoincareGate d 2 Nc rho)
```

for `d >= 3`, `Nc >= 2`, and arbitrary `SUNAdjointModel Nc`.  It is a
second formally certified wall for the current flat quotient-Poincare
route at fixed coarse side `N' = 2`.

The review makes no claim for another coarse side, for a rescaled or
weighted block operator, for the interacting Wilson Hessian, or for the
thermodynamic or continuum limits.  The gate is not proved necessary,
equivalent, or exhaustive for Yang-Mills, and the result is not presented
as direct progress toward the Clay problem.

## Lean verification

- Toolchain: `leanprover/lean4:v4.29.0-rc6`.
- Mathlib pin: `07642720480157414db592fa85b626dafb71355b`.
- Build command: `lake build YangMillsCore`.
- Build result: `Build completed successfully (8413 jobs)`.
- New module count: three.  `PhysicalPoincareLowModeFalsifier` was already
  present in the frozen base; Hodge, block, and endpoint are new.
- W-3 module warning count: zero.  The complete build replays only
  pre-existing linter warnings from the base tree.
- Oracle command: `lake env lean oracle_check.lean`.
- Oracle result: 2210 invocations, 2207 distinct names:
  - 2124 `[propext, Classical.choice, Quot.sound]`;
  - 49 `[propext, Quot.sound]`;
  - 17 `[propext]`;
  - 20 axiom-free.
- All sixteen new W-3b/W-3c/endpoint targets use exactly
  `[propext, Classical.choice, Quot.sound]`.
- `sorryAx`: zero.  Nonstandard axiom sets: zero.

## Artifact hashes

All hashes are SHA-256.  Text hashes use LF-normalized bytes.

| Artifact | SHA-256 |
| --- | --- |
| `oracle_check.lean` at `90ed3585` | `205A52FFF58EC41C7E746A4EC0732B875F6F16BE522BEB4DA20C02D3D386AB3C` |
| Full raw oracle output | `09044831B051646510F828C6E1C3A45B9BA3503482DB65866C695259E43DD75C` |
| `ORACLE-20260714-90ed3585.txt` | `B0D67D4A1056EDE627361E7335765B4C9457C88208BDC6021074CE0C7AE2F356` |
| `poincare_wall.tex` | `B294E02800AC2D08ED671AAA3560BE8C8B042C380D90467FF2C881E7DE1F938D` |
| `poincare_wall_w3_review.pdf` | `68C983F4BE9E7C87C40E3251B67F103C4C19B69D2C54A12B6DABA16002489C94` |

The reviewed PDF is a distinct 10-page Letter artifact.  It is not a
replacement for the frozen PDF.  All fonts are embedded; the file is not
encrypted and contains no forms or JavaScript.  All ten pages were
rendered and visually inspected, with no clipping or table overflow.
