# Archived submitted SU(2) compensated-flow artifact

This directory preserves the exact artifact that was submitted and reviewed,
not the abandoned `REV2` manuscript.

Immutable submitted objects:

- PDF: `machine-checked-su2-crossing-compensated-flow-ward.pdf`, SHA-256
  `2BB66657A544E9AF4A30D682DC69F92E18A5D3B1AB8F53C105D0DFDE767CC7C1`.
- TeX: `machine-checked-su2-crossing-compensated-flow-ward.tex`, SHA-256
  `97A943C350CF2D8B6F260A9593272F0D892E187427D09CFCC64796DB24818901`.
- Lean source ZIP:
  `ATTACH-THIS--SU2-CROSSING-DIFFERENTIAL-DESCENT--B7E8DA37.zip`, SHA-256
  `B7E8DA37732A58C858144AAF983D587F9485066FEC5F6B4F716D751F978EBAE6`.

The three files under `source/` are direct reading copies of producers contained
in the ZIP. Their Git blobs use LF and match `RECOVERED-HASHES.txt` byte for
byte. The clean-source transcript intentionally retains its original CRLF byte
stream because the committed manifest identifies those exact bytes.

The later `REV2` PDF and TeX were not submitted and are deliberately excluded.
Its experimental render guard was also excluded: it produced false negatives
and did not certify the rendered text. This rescue performed no new Lean build;
the build claim remains the historical, committed audit and transcript.
