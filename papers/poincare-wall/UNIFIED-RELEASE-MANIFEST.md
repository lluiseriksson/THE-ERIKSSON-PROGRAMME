# `poincare_wall` unified v1.3 release manifest

Date: 2026-07-14  
Release tag: `poincare-wall-v1.3-2026-07-14`  
Release branch: `poincare-wall-unified-v1.3`

## Release decision

This release reconciles two independently sealed editorial candidates without
moving or rewriting either seal:

- the fixed-coarse-side review candidate at `14e2d58f` supplied the explicit
  scope discipline, dependency-record presentation, and immutable-release
  method;
- the later W-3c source checkpoint `a17d7816` supplied a strictly stronger
  compiled endpoint for every positive fixed coarse side `N'`.

The unified paper states the stronger theorem. It does not infer the general
case from the earlier `N'=2` paper. No Lean source is changed in v1.3.

## Scientific scope

The second wall is stated exactly for:

- every `N' > 0`;
- `d >= 3`;
- `Nc >= 2`;
- every `SUNAdjointModel Nc`;
- the current unscaled line-integral block map and current unweighted coarse
  norm.

The paper does not claim that either Poincare gate is necessary, equivalent,
or exhaustive for Yang--Mills theory. It proves no continuum construction,
thermodynamic limit, volume-uniform Combes--Thomas estimate, or mass gap. A
rescaled or weighted block operator and coercivity from an interacting Wilson
Hessian remain separate questions.

## Formal provenance

- Lean source checkpoint: `a17d78165eaf7fc9ad505e8d3ed8e544848f8518`
- W-3c source/transcript seal: `33072662b8d42c91185b852592bff51a6542b222`
- committed oracle transcript: `3923b93272ac9bf3b13de5e1539b522ddbbcbc95`
- linked-paper baseline: `193bb675dc64063bd13623c75dddd49b95f38300`
- verification-ledger seal (Addendum 509):
  `b6c9a2868c10b964f0cdc6433d028b10188b33f3`
- toolchain: Lean `v4.29.0-rc6`; Mathlib `0764272048...`
- build command: `lake build YangMillsCore`
- build result: `Build completed successfully (8412 jobs)`

The five W-3c targets used by the dependency record are:

1. `norm_sq_flatBlockConstraintQCLM_le_inv_mul`
2. `flatGaugeHodgeK0_inner_blockScaleSquareModeCochain_eq_div`
3. `blockScaleSquareMode_rayleigh_numerator_le`
4. `quotientPoincare_squareMode_linear_lower_bound`
5. `volumeUniformQuotientPoincareGate_false`

Each prints exactly `[propext, Classical.choice, Quot.sound]` in the frozen
oracle transcript. The transcript records 2250 invocations (2247 distinct
output names), 2228 results on a nonempty subset of the standard axiom set and
22 axiom-free results, with zero `sorryAx` and zero nonstandard axiom sets.

- transcript SHA-256, LF: `5C4855F9A54B82904EE85BE5DCC731996D1AB9817E2DDAFEB33DA0B868DABC92`
- oracle script SHA-256, LF: `CBEFB14D8A07D98FDE5293640550EF492A4AEB41A0CB818D3397F8499E5AA0B1`
- raw-output SHA-256, LF: `4176F9E916720FA2CE2ED5B84D83E1DB1BB778D264DDBF6D626C6F66AB761AC1`

## Sealed paper artifacts

- `poincare_wall.pdf`
  - SHA-256: `1F5334E93E8C7A72207C47C237537F4E6BD4C108F3F631B5D9DF7C65B06FA1C0`
  - 11 pages, US Letter, 156889 bytes
  - 33 fonts; all embedded
  - 80 link annotations: 42 internal and 38 external HTTPS links
  - no malformed external links
  - not encrypted
  - no forms, JavaScript, embedded files, or executable multimedia
- `poincare_wall.tex`
  - SHA-256: `66DDEC3106471E3470B16EE165674F5E221C2621BBC67F9517537F8F7FCC6F6C`

The PDF was rendered independently at 160 dpi and every page was inspected.
No clipping, overlap, broken glyph, or margin overflow was found. In
particular, the dependency record on page 8 and the theorem--artifact map on
pages 8--9 remain within the text area. The TeX build reports no overfull box,
undefined reference, or PDF-string warning.

## Immutability rule

The annotated tag above must not be moved. Any later correction requires a
new commit, new PDF and TeX hashes, a new manifest, and a distinct tag. The
older fixed-`N'=2` candidate and v1.2 paper remain historical, independently
verifiable artifacts.
