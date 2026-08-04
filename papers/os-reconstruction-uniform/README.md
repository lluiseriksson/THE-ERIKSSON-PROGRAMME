# Volume-uniform OS reconstruction paper

This directory is the paper lane for task (52).  It is separate from the
placeholder/provenance cleanup and does not modify any previously submitted
paper.

Source: `os_reconstruction_uniform.tex`

Revised source responding to the 5.03/10 draft review:
`os_reconstruction_uniform_v2.tex`

The v2 paper adds the exact reconstructed connected-correlator identity and
its volume-uniform exponential-decay endpoint.  It preserves v1 as a frozen
historical object and does not claim a new Dobrushin estimate.

Lean source: `../../YangMills/OS/OSReconstructionUniform.lean`

The generated PDF is copied to `../../output/pdf/` after render-and-visual QA.
The verification manifest and frozen-object record are kept with the audit
artifacts, not inferred from the presence of a source file.

Verification manifest:
`../../docs/audit-artifacts/52-os-reconstruction-uniform-verification.json`

Frozen object:
`../../docs/audit-artifacts/52-OS-RECONSTRUCTION-UNIFORM-FROZEN-OBJECT.json`

The v2 verification and frozen-object manifests use distinct filenames so the
v1 evidence is not overwritten:

`../../docs/audit-artifacts/52-os-reconstruction-uniform-v2-verification.json`

`../../docs/audit-artifacts/52-OS-RECONSTRUCTION-UNIFORM-V2-FROZEN-OBJECT.json`

V2 PDF: `../../output/pdf/os_reconstruction_uniform_v2.pdf`

Integrated source responding to the 5.14/10 review:
`os_reconstruction_uniform_v3.tex`

V3 reproduces the already checked Dobrushin-to-operator argument inside the
paper, identifies the boundary space with the full real function algebra of a
finite slice, and derives the mixed-correlator bound.  It changes no Lean
source or theorem statement and does not claim a sharper analytic estimate.

V3 PDF: `../../output/pdf/os_reconstruction_uniform_v3.pdf`

Formal revision responding to the 5.18/10 review:
`os_reconstruction_uniform_v4.tex`

V4 promotes the mixed reconstructed connected-correlator consequence to
named Lean declarations, including an explicit zero-time argument, an exact
coordinate identity, and the volume-uniform product-norm decay endpoint.  It
does not sharpen the inherited Dobrushin estimate or claim a thermodynamic or
continuum limit.

V4 PDF: `../../output/pdf/os_reconstruction_uniform_v4.pdf`

V4 verification and response records:

`../../docs/audit-artifacts/52-os-reconstruction-uniform-v4-verification.json`

`../../docs/audit-artifacts/52-OS-RECONSTRUCTION-UNIFORM-V4-RESPONSE.md`
