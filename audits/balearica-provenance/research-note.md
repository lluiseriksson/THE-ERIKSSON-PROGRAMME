# Counting observations, source links and possible peak months in Balearica

These descriptive results use a 20 November 2026 snapshot. We selected three contrasting common species before inspecting monthly totals, then selected the olive and rock pigeon before querying their records. This is a purposive panel. Results describe entries in the database. Ecological abundance and phenology would require evidence on recording effort.

## Which unit is counted?

For each fully reconciled species below, the occurrence list contains one distinct Balearica ID and one distinct external GBIF occurrence ID per row. Each row links both to a GBIF occurrence and to its GBIF dataset. Counting provider links recovers the displayed source count, while counting distinct row-provider pairs recovers the size of the occurrence list. The individual row records establish the multiplicity directly. The database query implementation has not been inspected.

| Species | Occurrences | Source count | GBIF datasets | Unknown month | Possible leading months (1–12) |
|---|---:|---:|---:|---:|---|
| *Turdus merula* | 3 | 6 | 1 | 0 | 1, 2, 4 |
| *Posidonia oceanica* | 590 | 1180 | 22 | 54 | 8, 10 |
| *Quercus ilex* | 1559 | 3118 | 26 | 212 | 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12 |
| *Olea europaea* | 3152 | 6304 | 21 | 562 | 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 |
| *Columba livia* | 6947 | 13894 | 15 | 231 | 4 |

The month bounds allow each undated record to fall in any of the twelve months, and allow ties. For a dated count c_j and u undated rows, month j can share first place exactly when c_j + u reaches the largest dated monthly count. Assigning all u to j proves sufficiency. A unique winner is guaranteed precisely when its dated count exceeds its largest rival plus u. Recompute after excluding all rows of one dataset to measure the sensitivity of the result to that dataset. Empty samples have no winner. Missing dates may be constrained by metadata outside this snapshot.

For *Posidonia oceanica*, the dated leaderboard has October at 114 and August at 69. Of 590 records, 54 have no month in Balearica. Assigning 46 of these to August and the other eight to a low-count month makes August strictly first. Assigning all 54 to October preserves October. Both completions have exactly the observed dated counts. This invalidates a unique October peak inferred from these metadata alone.

Among dated entries, removing a single contributing dataset changes the peak from October to August for the seagrass, from January to October for both the holm oak and olive, and from April to May for the rock pigeon. For the pigeon, April has 1,144 dated entries, against 842 for May and 231 undated. Even assigning all undated entries to May leaves April ahead by 71 when every dataset is retained. Thus robustness to missing months and robustness to dataset composition yield different answers in the same species. The blackbird has a three-way tie among its three dated entries, all from one dataset.

Two of the three blackbird occurrence links resolved in the GBIF API to the same dataset and month as Balearica. The third returned HTTP 404 on this check. Its current external identity remains unresolved. Dataset-level results retain the provenance listed by Balearica and do not rely on all historical links staying live.

## Reproduction and attribution

The accompanying JSON contains derived counts and hashes of the source responses. Run `python seasonal_bounds.py` with Python 3 in this directory to recover the possible and guaranteed leaders, including after each single-dataset omission. Compare the taxon-specific occurrence list and source aggregate in the [Balearica API](https://balearica.uib.cat/api/docs). The platform is maintained by the Centre Balear de Biodiversitat, Universitat de les Illes Balears. See the [distribution methodology](https://balearica.uib.cat/method/getting_started/distribution.html), [platform article](https://doi.org/10.3897/BDJ.14.e209972), and [GBIF record](https://www.gbif.org/occurrence/4018619371). Only aggregate counts are distributed here. This research note received no external scientific review.
