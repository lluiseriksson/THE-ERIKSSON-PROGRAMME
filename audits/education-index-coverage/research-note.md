# Duplicate attribution changes the cost of omitting a bibliographic index

We reconstructed the status, title and source columns of the 106-page screening register deposited by Graziella Rodrigues de Lima for requirements-engineering education with LLMs. The register contains 1,259 rows, including 22 accepted, 94 duplicated and 1,143 rejected. All accepted rows on the first two pages were checked visually. The accompanying script reads the original PDF as `source.pdf` using PyMuPDF and writes derived counts and title-key hashes to standard output. Source register: https://doi.org/10.5281/zenodo.24407666 .

| Accepted titles lost on omitting one index | Representative rows alone | With duplicates, whitespace-normalized titles | With duplicates, punctuation-insensitive tokens |
|---|---:|---:|---:|
| ACM Digital Library | 2 | 1 | 1 |
| IEEE Digital Library | 8 | 2 | 1 |
| Scopus | 12 | 8 | 8 |

Crediting duplicate records adds a second recorded source for 11 of 22 accepted titles under the first rule and 12 under the second. All three indexes together are necessary to cover these 22 titles under either rule. These counts describe the frozen export. Database coverage outside the export and the identification of a study through substantially different title strings are unresolved.

The singleton counts also give an exact sensitivity threshold in a specified error model. Permit one previously missing incidence between an accepted title and one additional source per edit. For any pair of sources, each accepted title absent from that pair requires its own edit. Adding one incidence per absent title attains this bound. Thus the nominal three-index minimum can drop to two after just one additional authenticated linkage in either matching model. Dropping Scopus specifically requires eight such links. These are sensitivity bounds, not evidence that any such links exist. No external search recall or general superiority of any index is inferred.
