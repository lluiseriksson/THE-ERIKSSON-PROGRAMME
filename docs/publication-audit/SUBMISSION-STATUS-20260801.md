# Submission status - owner report on 2026-08-01

The owner reported in the Codex task on 2026-08-01 that all thirteen
replacement forms in the audited owner sequence had been sent. The public
ai.viXra pages still exposed the prior versions when checked the same day.
Accordingly these records are **ENVIADO/PENDIENTE**, not `PUBLICADO`.

No confirmation number, confirmation email, exact submission timestamp or
submitted-account address was supplied to this audit.  Those fields remain
`NOT RECORDED`; they must not be invented from the task timestamp.

| Order | Record | Target | Owner-reported state | Public version visible 2026-08-01 | Confirmation evidence |
|---:|---|---|---|---|---|
| 1 | `2602.0052` | v3 | ENVIADO/PENDIENTE | v2 | owner report; frozen PDF `4ce8cb39d5e47b59c27c88a3398660ca61985dff1f7589cf04c8ea472e09733b`, 16 pp |
| 2 | `2602.0036` | v3 | ENVIADO/PENDIENTE | v2 | owner report; frozen PDF `7e86eb7ba4e3ac1d79345632d20140b4b5fc8407fb9f55a171ec2bf79dd0b12f`, 19 pp |
| 3 | `2602.0033` | v3/R30 | ENVIADO/PENDIENTE | v2 | owner report; frozen PDF `878dba7cc659477ea9172a24f9dba88498d41ba49af44cfdcb1a73baa13f6285`, 25 pp |
| 4 | `2602.0085` | v2 | ENVIADO/PENDIENTE | v1 | owner report; frozen PDF `deff7be46aa56ddfbcac63addce730a4bc4449768e5920951d1a304912525518`, 26 pp |
| 5 | `2602.0084` | v2 | ENVIADO/PENDIENTE | v1 | owner report; frozen PDF `4099349dc23496d5938e5dee8092de991083c92dea15481a3a69d2c1ba008bc9`, 21 pp |
| 6 | `2602.0035` | v2 | ENVIADO/PENDIENTE | v1 | owner report; frozen PDF `053107800c2b81f2f6649016f095f748146acf5af073eea0a7776ab7da575db8`, 21 pp |
| 7 | `2602.0038` | v3 | ENVIADO/PENDIENTE | v2 | NOT RECORDED |
| 8 | `2602.0041` | v4 | ENVIADO/PENDIENTE | v3 | NOT RECORDED |
| 9 | `2601.0115` | v3 | ENVIADO/PENDIENTE | v2 | NOT RECORDED |
| 10 | `2512.0073` | v2 | ENVIADO/PENDIENTE | v1 | NOT RECORDED |
| 11 | `2601.0047` | v3 | ENVIADO/PENDIENTE | v2 | NOT RECORDED |
| 12 | `2607.0035` | v2 | ENVIADO/PENDIENTE | v1 | NOT RECORDED |
| 13 | `2607.0023` | v2 | ENVIADO/PENDIENTE | v1 | NOT RECORDED |

## Public-verification gate

For each record, wait until the public page exposes the intended version.  Then
download the PDF anew and record the direct URL, UTC observation time, SHA-256,
byte size, page count, encryption state, title, abstract and comments.  Compare
the public PDF with the frozen submitted PDF and visually inspect every page.
Only after those checks may that row move from `ENVIADO/PENDIENTE` to
`PUBLICADO`.

Do not modify the submitted PDFs, release ZIPs or manifests while processing is
pending. Do not resend a form merely because ai.viXra processes the thirteen items
in a different order.

## Cross-lane provenance reconciliation

A separate source desk reported commit `2c785f90` (not pushed and not present in
either local clone accessible to this audit) after comparing its six earlier
objects with the PDFs actually submitted. This audit independently matched the
six submitted hashes and page counts above to the frozen local PDFs; it did not
adopt the inaccessible commit.

The source-desk comparison reports: `2602.0035v2` is text-identical to its desk
object and differs only by recompilation; `2602.0036v3` differs on pp. 2--4;
`2602.0052v3` differs on pp. 3--5; `2602.0084v2` differs on pp. 1--6;
`2602.0085v2` differs on pp. 1--5; and submitted R30 is not that desk's R29.
For 0036/0052 the first differences appear compositional, while 0084/0085
contain real wording changes. This is a provenance statement, not a finding
that the submitted wording is false; the final package audits remain the
controlling audit records.

The desk also reported that the common invariant block survives verbatim in
submitted 0033 pp. 14--17, 0035 pp. 8--11 and 0036 pp. 5--8, and that the
restored eight-page manuscript remains intact at the end of submitted 0033.
R29's deictic phrase `the family above` became false after intervening family
insertions; submitted R30 repairs the reference by naming the intended family.
R29 was not submitted.

## Supersession replacements added by owner policy

The owner further directed that every `SUPERSEDE-BY-NEW-PAPER` relationship be
made visible in the old record's replacement PDF and abstract, in uppercase.
Four additional replacement packages were therefore audited separately:
`2512.0073v2`, `2601.0047v3`, `2607.0035v2` and `2607.0023v2`.  They are not part
of the first nine but were also reported sent later in the task. Their frozen
local packages remain independently audited, while their publication state is
`ENVIADO/PENDIENTE` in owner order 10--13. `2607.0089v1` remains claim-level
`REVIEW-PENDING` despite being the named successor in the final package.
