# K4 t-box candidate pre-registration: `[3.06,3.07]`

**Status:** candidate-only design; no gate promotion.

This page freezes one adjacent t-box before reading its output.  It uses the
same certified-candidate configuration as the preceding chain:

- `delta = [1/25,81/2000]`;
- `t = [153/50,307/100]`;
- `seed_grid = 12`, `max_cells = 2304`;
- Arb precision 140 bits;
- production transcript plus a byte-identical replay;
- validator requires all seven literal fractions to be `< 1`.

The result, even if it passes, cannot promote K4, S1'''/S2''', G2, or G6.  The
global t-union, physical-carrier overlap, low-z treatment, moving boundaries,
and outer tails remain separate obligations.
