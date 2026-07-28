# Current mid-cover block — fresh units 10–19, 30–31, and 32 repair

The isolated current-tree runs now have production/replay pairs for:

- order-20 units `10`–`19` (beta `[203/4,213/4]`), 10 units;
- order-20 units `30`–`31` (beta `[223/4,225/4]`), 2 units;
- the preregistered order-22 repair unit `32` (beta `[225/4,113/2]`), 1 unit.

The independent validators checked exact rational beta domains, the frozen
Taylor configurations, adjacent `t` partitions to the moving endpoint, and
strictly negative outward-rounded row bounds.  For units 10–19 the
production/replay bytes are identical after rerunning both channels with the
same start index and cache evolution; units 30–31 and 32 also pass byte
equality.  The total fresh row counts are 1,501 for units 10–19, 338 for
units 30–31, and 168 for unit 32.

Unit 20 (`[213/4,107/2]`) still has no current production transcript: the
order-20 evaluator reaches its minimum-width limit before completing.  The
83-unit `[193/4,69]` cover is therefore not complete, and this block remains
candidate sign evidence only.  It does not close the finite-beta union, the
sign-to-`(H_tail)` relay, K2, G2, or G6.

Representative current production hashes (SHA-256) are recorded in the
transcripts themselves; the current run head is `75a78e2d1a8255629e95fc4904b87abaf84ec1c9`.
