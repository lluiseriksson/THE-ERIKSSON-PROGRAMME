# PROVENANCE HASHES (certificate & judge scripts)

Round 2 of this file (external audit on 7c75dd6: the first version
labeled every on-disk hash 'executed (CRLF)' while some scripts sit
on disk with LF endings).  Fields now: 'executed bytes' = sha256 of
the file exactly as it sits on disk and was executed, with its
detected EOL; 'LF-normalized' = sha256 after CRLF->LF (the git blob
form).  Rule: refreshed in the same commit whenever a certificate
script changes.

## cascade1_signed_minoration.py
- executed bytes (EOL: CRLF): 101d713f8b32608cfd73d1a7194bd8f78c9a6a409625902a0ae8c375c71cbf9f
- LF-normalized:            aa4cc1d75bc9f5175a7347f8c0a4e9086e88f46f67680b3ebeeb2f190c18ae11

## cascade1_floor_arb.py
- executed bytes (EOL: CRLF): 8bfbeba35f7263d2e31c36ebc5fe8abebee0f9df21b1f8e0fbc65551de8f84bc
- LF-normalized:            396189f456c49846e78de0732d3151dd650071320f537939a762a948a1769e4f

## cascade2_step0_eps.py
- executed bytes (EOL: CRLF): a4d3b23dfafa221bbbd30b0c5263108321fc7f37fbd040a7ad6d5b0b7383dfbf
- LF-normalized:            e493bb4306804887a71d975c362d8af9a103278ebc73c1f95945e76e6c6db1c1

## cascade2b_zoneL.py
- executed bytes (EOL: CRLF): df9f3a896ba51cb554e08c32e5d94e2a03c77531d9e994e81590785ee43e1258
- LF-normalized:            c3f914f6d316f95b4cb52b2f9e0bf7e120b30489e5e4a49f62af4617d82d60b2

## cascade3_judges.py
- executed bytes (EOL: LF): 5cf353be84ec32f1bcbdaac574327e333f7b2b22c93294543035f42afc8133bf
- LF-normalized:            5cf353be84ec32f1bcbdaac574327e333f7b2b22c93294543035f42afc8133bf

## cascade3_mirror_extraction.py
- executed bytes (EOL: LF): 1b2b833f0667ffd5b9e74fb0da49f09d68a54f3145a3b57858684f97c9453db8
- LF-normalized:            1b2b833f0667ffd5b9e74fb0da49f09d68a54f3145a3b57858684f97c9453db8

## cascade3b_judges.py
- executed bytes (EOL: CRLF): f5713b4a77454bc7b5b7299a80b648ce88d83d9028e843fab723c7c001756e97
- LF-normalized:            9acecc6cfd9d18d36e054ff69e5daca3c2f48f24247aefd40e0d79fb1be7f551

## cascade3b_mainside.py
- executed bytes (EOL: LF): 2233fa54c99857970fe4ed2a7bcad98514f5fd613a92004945497a763f34f199
- LF-normalized:            2233fa54c99857970fe4ed2a7bcad98514f5fd613a92004945497a763f34f199

## cascade3c_buckets.py
- executed bytes (EOL: CRLF): 698cf838a8e6127de1ee6b0bf15077a21311d59d5ba5d0e55ddff7c397f26359
- LF-normalized:            e816c2afab2073a4407c07812ad5d393481e460d7dc4212d4b3f9b8731ee23b6

## pilot_dz_beta.py
- executed bytes (EOL: LF): 0e431957ff6f6fc963c531929a3389a7726928afa7e06289928b0b66d5960805
- LF-normalized:            0e431957ff6f6fc963c531929a3389a7726928afa7e06289928b0b66d5960805

