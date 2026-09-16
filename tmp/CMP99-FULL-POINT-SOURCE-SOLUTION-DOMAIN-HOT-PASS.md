# Full point-source endpoint domains — hot PASS checkpoint

- Source checkpoint: `e4f2bbc33599da7b0f7ff91deeb5307719616a25`.
- Hot runner checkpoint: `555ec521fb8dbb698d077d35d52ebb9cbc649b6b`.
- Runner SHA-256: `417217cf200a09928a5a733097ccaa96aa0abaa048db144237e32334262861e6`.
- Focal: exit `0`, `1584.996 s`, `8638/8638` jobs.
- Audit: exit `0`, `8.146 s`.
- Audited declarations:
  - `cmp99SourceFlatFullPointSourceSolutionDomain_centered`
  - `cmp99SourceFlatFullPointSourceSolutionDomain_physical`
- Both declarations use exactly
  `{propext, Classical.choice, Quot.sound}`.
- Evidence payload SHA-256:
  `8448c6a2e220bac28eb268c89209482c69744e6f4b0a8e800b80e27d9ca411eb`.
- Evidence archive SHA-256:
  `ec2311536d51a0bc4b67694c68ffbd7cf2f9e3a5a46f4f62f5373f876661a1a7`.

This is retained-runtime diagnostic evidence, not seal authority.  The two
PRE-VALIDATION notices remain and the audit stays outside `YangMillsCore.lean`.
Counters remain exactly `20/41`; window 15 is compatible but unattained and
`TermSource = 0`.

## Exact cold successor

- Cold-runner checkpoint: `386c3c7e15702b56f82e29b227d9d3601d1feb89`.
- Cold-runner SHA-256:
  `81f5bf48421204246bce75a23fa774ce9f28f39dc8f383639c6f013ee4043267`.
- Run `scripts/colab_cmp99_full_point_source_solution_domain_cold.py` in a
  fresh Colab Pro+ CPU/high-RAM checkout, exactly once.
- On PASS, preserve and verify the archive, retire PRE-VALIDATION only from
  the two certified modules, import the audit in `YangMillsCore.lean`, and
  append the exact hashes/timings/delimitations to the ledger and vertical
  map.  Do not move `20/41`.

## Prepared next brick (not promoted)

- `tmp/BalabanCMP99SourceFlatFullPointSourceMixedDomain.draft.lean`
- `tmp/BalabanCMP99SourceFlatFullPointSourceMixedDomainAudit.draft.lean`

The mixed-domain telescope remains scratch until the cold seal above exists.
