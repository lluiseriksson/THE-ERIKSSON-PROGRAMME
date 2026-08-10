# Dobrushin quasi-local C*-state paper — ai.viXra submission record

Date recorded: **2026-08-05**

Operation: **new paper submitted to ai.viXra.org**

Moderation/publication outcome and public identifier: **not recorded here**

## Submitted paper

Title: *From Dobrushin Comparison to a Quasi-Local C*-State: A Lean-Checked
Construction for the Two-Dimensional Ising Model*

- Author: **Lluis Eriksson**
- Category: **Mathematical Physics**
- Length: **17 pages**
- Paper commit: [`c1943b4957c2eacbfecf73e83a0d81f788118d33`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/c1943b4957c2eacbfecf73e83a0d81f788118d33)
- Verified D-9 source anchor: [`f587b35001f4ae87c7fe0383662864df6bc9a1c0`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/f587b35001f4ae87c7fe0383662864df6bc9a1c0)
- [Exact submitted PDF at the paper commit](https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/c1943b4957c2eacbfecf73e83a0d81f788118d33/output/pdf/dobrushin_thermodynamic_limit.pdf)
- PDF SHA-256: `7FAECBB1A2799A00B93DA255597030E2561104A98D01ABE1C3B455E2661F8993`
- PDF size: **377,505 bytes**
- [Repository ZIP at the paper commit](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/archive/c1943b4957c2eacbfecf73e83a0d81f788118d33.zip)

The digest and byte count above are taken from the release manifest committed
with the exact paper object. This record does not substitute a mutable local
preview or the earlier 12-page D-7 PDF.

## Exact submission metadata

The form used author `Lluis Eriksson`, category `Mathematical Physics`, and
the title above. The comments field was:

> 17 pages. Lean 4 formalization. AI-assisted with OpenAI Codex; all Lean
> builds and axiom-oracle checks were verified by the author. Source and
> validation evidence are linked in the PDF.

The abstract describes a Lean-checked construction in the classical
anisotropic Dobrushin region: the comparison/resolvent estimate, compatible
finite-volume expectations, translation-covariant local algebra, its
commutative C*-closure and a positive norm-one state, together with finite-set
Gibbs conditional kernels and their exact finite-volume tower identity.

## Verification evidence carried by the release

The D-9 release manifest records fresh Colab validation at source anchor
`f587b35001f4ae87c7fe0383662864df6bc9a1c0`:

- three targeted modules building successfully at 8,178, 8,179 and 8,180 jobs;
- `lake build YangMillsCore` exiting zero at **8,494 jobs**;
- the repository axiom oracle exiting zero with **5,481 lines**;
- all 19 D-9 declarations present, with axiom dependencies contained in
  `[propext, Classical.choice, Quot.sound]`;
- two final `pdflatex` passes exiting zero and all 17 pages visually inspected.

These are branch/release measurements. The D-9 source and paper commit were
not ancestors of `main` when this record was written, so they do not replace
the canonical `main` checkpoint.

## Exact scope and frontier

The submitted paper constructs a quasi-local commutative C*-state and proves
the finite-volume conditional-kernel identities stated in the manuscript. It
does **not** claim the infinite-volume DLR fixed-point equation for the
completed state, covariance of that completed state under the full `Z^2`
action, arbitrary Folner/exhaustion independence, a parameter region beyond
classical Dobrushin uniqueness, or any Yang--Mills consequence.

The earlier D-7 object at `daa1b40d940d1f1b2a07de303271b37b6e736121`
remains a valid historical checkpoint, but its 12-page PDF and narrower
frontier are not the submitted 17-page artifact recorded here.
