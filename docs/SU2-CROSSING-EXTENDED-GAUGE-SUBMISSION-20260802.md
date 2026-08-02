# viXra submission record — SU(2) crossing extended gauge invariance

## Status

- Submitted: **2026-08-02**
- Operation: **NEW PAPER**
- Category: **Physics — Mathematical Physics**
- viXra identifier: **pending moderation**
- Upload policy: PDF only; the Lean audit ZIP is retained separately

This is a submission record, not a claim that viXra has already assigned or
published an identifier. The PDF and ZIP are not represented here as
repository-hosted artifacts.

## Title and author

**Machine-Checked Extended Gauge Invariance at an SU(2) Crossing: Four-Edge
Wilson Holonomy, Haar-Preserving Quotient Coordinates, and Reduction to the
Ward Chart**

Lluis Eriksson

## Immutable artifact identities

| Artifact | Filename | SHA-256 |
|---|---|---|
| Submitted PDF | `machine-checked-su2-crossing-extended-gauge.pdf` | `8A9B9356F1CFA3C2D69A9371BB62F01D243E7725D203F2726F31772A8B821D9E` |
| Retained Lean audit ZIP | `ATTACH-THIS--SU2-CROSSING-EXTENDED-GAUGE--242790FA.zip` | `242790FA0687CE08C6BCC7A6AC120BE4CC4D24AD92CAF62A46A2794D6D39304E` |

The obsolete PDF (`088ED64C…710772`) and obsolete ZIP
(`769CF851…A2A65E7`) are not authorized submission artifacts.

## Abstract supplied with the submission

We formalize extended gauge invariance at a simple four-edge SU(2) crossing
and connect the geometric edge chart to the two-coordinate chart used by a
machine-checked crossing Ward identity. On SU(2)^4 we define the two
opposite-edge right actions from the abstract Makeenko--Migdal theorem, prove
that they are commuting product-Haar-preserving actions, and show that their
common parameter composes to ordinary vertex gauge invariance. The four-edge
Wilson word `tr2(a3^-1 beta a2 a4^-1 alpha a1)` is proved invariant under both
half-actions. We construct the explicit quotient
`r(a)=(a2 a4^-1,a1 a3^-1)`, a canonical section, and prove existence and
uniqueness of the universal factorization for every extended-gauge-invariant
complex function. The complete map from the cyclic four-edge chart to
physical and gauge coordinates is proved to preserve literal four-fold Haar
measure in one public endpoint. Finally, the four-edge Wilson word is
identified exactly with the prior two-coordinate crossing word evaluated on
`r(a)`. The Lean producer has 56 public declarations in 488 physical lines;
all 36 theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`,
with no local proof escape. No heat-kernel area derivative or full
Makeenko--Migdal equation is claimed.

## Submitted comments

> 6 pages, 2 tables, 2 figures. Lean 4.29.0-rc6; Mathlib commit
> 07642720480157414db592fa85b626dafb71355b. Clean-source build and audit
> passed. 56 public declarations; no sorry, admit or local axiom.

## Scope boundary

This paper packages a finite-dimensional SU(2) crossing and quotient-chart
formalization. It does not prove the heat-kernel area derivative, the complete
Makeenko--Migdal equation, a continuum construction, or a Yang--Mills mass
gap. Recording its submission changes no node or percentage in the programme's
Clay-distance dashboard.
