# Eq337 complex closed-radius public module cold seal

Cold Colab Pro+ high-RAM evidence for the promoted public scalar module and
its axiom audit.

- source checkpoint: `ae676b71f2bae392560db80cbadcd24e6193305a`
- source blobs:
  - `YangMills/RG/BalabanCMP99Eq337ComplexClosedRadiusScalar.lean`
    SHA-256 `7adfd435acf6e312c17769bda7dc739360b85735ee0f8f6af8a653275502ba01`
  - `YangMills/RG/BalabanCMP99Eq337ComplexClosedRadiusScalarAudit.lean`
    SHA-256 `ff5a8ea1ae904fce9501fac2bcf8bbd03ff1cdeb76b68457340dc56f30dc096c`
- runner revision: `eq337-complex-closed-radius-module-cold-v2`
- runner SHA-256: `66e690a2a50297688f33a7fd1998ca38061e4533aaaff05a457313f9afb71155`
- runtime: Colab CPU, high RAM (`50.99 GiB`)
- Lean toolchain asset SHA-256: `bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e`
- Mathlib pin: `07642720480157414db592fa85b626dafb71355b`
- module focal: `exit 0`, `27.169 s`
- audit: `exit 0`, `16.179 s`, 15/15 declarations within
  `{propext, Classical.choice, Quot.sound}`
- evidence payload SHA-256: `44e299887f8236319984b9f3d85f09dfea48791db81a9b231b812c41b15bc052`
- Colab archive SHA-256: `046dd4b3dd97616c8f51bc79e15af12b616bba58fa4a274ce03317532322dd96`
- executed notebook SHA-256: `227E6316CFF252832928077BE8EA20B50243364CEDE2EEEDCBD2AB4F82F1E376`
- terminal verdict: `FINAL_STATUS=PASS`

The preceding v1 attempt stopped before elaboration because its runner had
not created the target `.olean` directory. The retained-runtime diagnostic
then compiled the unchanged source and audit, and this v2 cold run sealed the
same source checkpoint after the runner-only repair.

This seal does not install the physical Eq. (3.37) chain or move `20/41`.
