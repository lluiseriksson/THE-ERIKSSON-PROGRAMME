# Lean audit for the compensated-flow revision - 2 August 2026

## Result

**PASS.** The scientific revision changes only the manuscript's claim boundary
and comparison with the Driver--Hall--Kemp ordinary-edge operator. The Lean
producer, audit module, and immutable source ZIP are byte-identical to the
independently reconstructed package.

- Lean: `v4.29.0-rc6`
- Mathlib: `07642720480157414db592fa85b626dafb71355b`
- Clean-source build: `2915/2915`, successful
- Producer: 426 physical lines
- Public declarations: 26
- Audited theorems: 16
- Local `sorry`, `admit`, or `axiom`: 0
- Source files in the ZIP: 57
- Pre-build and post-build source mismatches: 0

Every new theorem reports only `propext`, `Classical.choice`, and
`Quot.sound` under `#print axioms`.

## Immutable identifiers

- Revised PDF SHA-256:
  `2BB66657A544E9AF4A30D682DC69F92E18A5D3B1AB8F53C105D0DFDE767CC7C1`
- Revised TeX SHA-256:
  `97A943C350CF2D8B6F260A9593272F0D892E187427D09CFCC64796DB24818901`
- Unchanged source ZIP SHA-256:
  `B7E8DA37732A58C858144AAF983D587F9485066FEC5F6B4F716D751F978EBAE6`
- Producer SHA-256:
  `FA8FA86F6480123B8E63E0E285AD4B2C5CA6E0DEB85C85DB86261C66A24B5048`
- Audit module SHA-256:
  `0A2AAA9CABEC03B3DD5F902E3625C80AC37A2D37CBAA02F56EFADB855E6C3CFD`
- Clean-source transcript SHA-256:
  `8B7011C4C567425A28FADB24404E13D5AC4E80C520D1232472EB834598168F4C`

## Corrected claim boundary

The compiled endpoint concerns the quotient-lifted compensated mixed operator.
It is not identified with the ordinary-edge mixed operator of
Driver--Hall--Kemp. The manuscript now displays both operators and their
distinct reverse resolutions and marks their comparison as open.
