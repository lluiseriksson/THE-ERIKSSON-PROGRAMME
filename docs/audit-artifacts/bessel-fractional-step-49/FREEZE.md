# Freeze manifest - audit (49)

Capture date: 2026-08-04 (Europe/Stockholm)

Branch: `codex/audit-bessel-fractional-49`

Base: `04f87347f3e4d46a05e77bc1c70855794e111477`

Frozen audit-body commit: `4e2b7f9a7187ff85ded124aac255fcf1caa69d0b`

Capture method for text files:

1. raw worktree bytes: `.NET File.ReadAllBytes`;
2. LF view: `.NET File.ReadAllText`, replace CRLF and lone CR by LF,
   encode UTF-8 without BOM;
3. CRLF view: start from the LF view, replace LF by CRLF, encode UTF-8
   without BOM;
4. digest: SHA-256 over the corresponding byte array;
5. Git blob: `git rev-parse HEAD:<path>` at the frozen audit-body commit.

| Object | Raw bytes | Raw SHA-256 | LF bytes / SHA-256 | CRLF bytes / SHA-256 | Git blob |
|---|---:|---|---|---|---|
| `docs/BESSEL-FRACTIONAL-STEP-AUDIT-20260804.md` | 11578 | `f96557f24e1d3bdd0d571c842a83084a156a186413e6b09810ba6d136452c329` | 11578 / `f96557f24e1d3bdd0d571c842a83084a156a186413e6b09810ba6d136452c329` | 11872 / `115a3efe304d30a30402c8ce5b0edeab87a5ef709cd2e0427bd7de5bf84f64bb` | `d0578d54578efbde2dcb951247d2953028207e34` |
| `scripts/audit49_fractional_bessel.py` | 2909 | `866cfe2c523f4221c1893ad2a5279c0bea681e8eba0dfdf5760439e75d85f161` | 2909 / `866cfe2c523f4221c1893ad2a5279c0bea681e8eba0dfdf5760439e75d85f161` | 3005 / `56dee61839d354cf8524f5d687e3954e2fbe59dc4b28d5f62010b8505228b7cc` | `f7d6c7b942ef5dc4ff35e1218e72b4802492be86` |
| `papers/bessel-amos-fh/bessel_amos_fh.tex` | 24065 | `a131975ef81d912e332b8914057f006c19d937cdc9a7574fdff67a0b399346e6` | 23509 / `97c1806d6207e551a4b93b8967460cb7693120b9957b379e372c8c3acae4ceb2` | 24065 / `a131975ef81d912e332b8914057f006c19d937cdc9a7574fdff67a0b399346e6` | `4b614d977d56b97b5f47c80f7ffc285b789c7b43` |

Primary-source PDF captures (raw downloaded bytes, SHA-256 via
`Get-FileHash`; the files remain local audit intermediates and are not claimed
as repository artifacts):

| Source | URL | Bytes | SHA-256 |
|---|---|---:|---|
| Freitas--Laugesen, arXiv 1810.07461 | `https://arxiv.org/pdf/1810.07461` | 520466 | `9f72a16080b397f4cb9595132e89cb972edd1f9cb85424d29337bb1d10c11877` |
| Segura, arXiv 2105.02524 | `https://arxiv.org/pdf/2105.02524` | 261080 | `b4c9be36aa139a05acb89f7872929e832e103e3475aae52e6ff8f287a87372fb` |

Relevant pages were text-extracted with MiKTeX `pdftotext -layout` and
rendered with MiKTeX Poppler `pdftoppm` at 110 dpi. Visual inspection covered
Freitas--Laugesen pp. 20--21 and Segura pp. 15--16.

No Lean/Lake/oracle execution was performed. No `.olean` materialization is
asserted. The terminal verdict remains assigned to a separate task.
