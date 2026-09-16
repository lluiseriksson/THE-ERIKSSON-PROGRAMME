# CMP99 arbitrary-residue dictionary cold gate v1 — blocked instrumentation

This archive records the fail-closed Colab Pro+ CPU/high-RAM attempt against
exact source checkpoint `ac83083f89969d147505332ea6b7ab9bbb56f2cd`.
The immutable runner was published at
`9690568835d4cb0a8c68d5b4aaa964df1c591022`, with Git-blob SHA-256
`305307E736C14DDF294B903DB9053812FE53FD465C5061AA70212683B2323AB5` and
`RUNNER_REV=cmp99-arbitrary-residue-dictionary-cold-v1`.

The run opened on CPU with `50.99 GiB` RAM, verified the pinned Lean
`4.29.0-rc6` asset SHA-256
`BF3E0A4025E47A0BEA9ED907D12DCCD3D3590B1D8AD6C55A915298B01AD9D3E`,
cloned and detached exact source, and then stopped before dependency
materialization or Lean compilation at:

```text
SOURCE_BLOB_HASH_MISMATCH=YangMills/RG/BalabanCMP99FlatIntegerResidueClassDictionary.lean
```

The runner had supplied Git SHA-1 object identifiers where the inherited
gate compares raw-file SHA-256 values.  The raw-file digests measured from
the exact Git blobs are:

```text
BalabanCMP99FlatIntegerResidueClassDictionary.lean
  980F5C4F6F36388F28BA2C2D64442E595AF571DE2952511EFD2BD836C9BA84D8
BalabanCMP99FlatIntegerResidueClassDictionaryAudit.lean
  4D88A364A652C3DB43A7CC01E064B173F874BA992E6E86F9B8DDD1426E65CD54
```

Downloaded archive SHA-256:
`FC47B70D37D56F15A849679E7AB3435D2034C04F685A99B236E9884ED547CA2C`.
The extracted final `evidence.json` SHA-256 is
`6809DCAB2CF1E08742AB6897DFF2807FD116181CF60716A2513AE97EB22CC6B1`.

Classification: `BLOCKED-INSTRUMENTATION`.  This is not compiler evidence;
PRE-VALIDATION remains, the audit stays outside `YangMillsCore.lean`, and
`20/41`, `TermSource = 0`, and window 15 remain unchanged.
