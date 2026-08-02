# viXra submission record — SU(2) crossing compensated-flow Ward identity

## Status

- Submitted: **2026-08-02**
- Operation: **NEW PAPER**
- Category: **Physics — Mathematical Physics**
- viXra identifier: **pending moderation**
- Upload policy: PDF only; the unchanged Lean source ZIP is retained separately

This is a submission record, not a claim that viXra has already assigned or
published an identifier. The PDF and ZIP are not represented here as
repository-hosted artifacts.

## Title and author

**Machine-Checked Haar and Differential Descent at an SU(2) Crossing: A
Four-Edge Compensated-Flow Ward Identity**

Lluis Eriksson

## Immutable artifact identities

| Artifact | Filename | SHA-256 |
|---|---|---|
| Submitted PDF | `machine-checked-su2-crossing-compensated-flow-ward.pdf` | `2BB66657A544E9AF4A30D682DC69F92E18A5D3B1AB8F53C105D0DFDE767CC7C1` |
| Retained, unchanged Lean source ZIP | `ATTACH-THIS--SU2-CROSSING-DIFFERENTIAL-DESCENT--B7E8DA37.zip` | `B7E8DA37732A58C858144AAF983D587F9485066FEC5F6B4F716D751F978EBAE6` |

The obsolete PDF beginning `23A47EB1` is not an authorized submission
artifact. The reviewed PDF metadata `/Title` was deliberately left unchanged:
altering that cosmetic field would change the already reviewed bytes. Neither
the PDF nor the ZIP is to be regenerated for this submission.

## Abstract supplied with the submission

We machine-check the exact measure and differential bridge between the
four-edge SU(2) crossing chart and the two effective group coordinates used by
a finite-dimensional Ward identity. The quotient
`r(a)=(a2 a4^-1,a1 a3^-1)` pushes normalized four-fold Haar measure exactly to
normalized two-fold Haar measure. Two gauge-compensated flows on the original
four edges intertwine with independent right multiplication of the quotient
coordinates, so first and mixed derivatives of the crossing Wilson word
descend without choosing a gauge. The three Pauli directions are verified
individually, their mixed generators close into direct and reverse
resolutions, and the two-coordinate Ward theorem lifts to a literal four-edge
integral with coefficients `-1/4` and `-1/2`. This compensated operator is not
identified with the ordinary-edge mixed operator of Driver--Hall--Kemp: the
paper writes both operators and their distinct reverse resolutions and marks
their comparison as open. The Lean producer has 26 public declarations and 16
audited theorems. No weak four-face heat-kernel identity, area derivative, or
full Makeenko--Migdal equation is claimed.

## Submitted comments

> 7 pages, 2 tables, 2 figures. Lean 4.29.0-rc6; Mathlib commit
> 07642720480157414db592fa85b626dafb71355b. Clean-source build and audit
> passed. 26 public declarations; no sorry, admit or local axiom.

## Scope boundary

This paper formalizes a finite-dimensional SU(2) Haar and differential bridge
for a compensated crossing flow. It does not identify that operator with the
ordinary-edge Driver--Hall--Kemp operator and does not prove the weak
four-face heat-kernel identity, an area derivative, the full
Makeenko--Migdal equation, a continuum construction, or a Yang--Mills mass
gap. Recording its submission changes no node or percentage in the programme's
Clay-distance dashboard.
