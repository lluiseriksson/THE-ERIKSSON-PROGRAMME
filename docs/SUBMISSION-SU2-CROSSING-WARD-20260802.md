# SU(2) crossing Ward paper submission record (2026-08-02)

**State:** submitted to ai.viXra as a new paper, as reported by the owner;
public identifier pending.

**Category:** Physics -- Mathematical Physics.

**Title:** *Machine-Checked Finite-Edge SU(2) Crossing Ward Identity: Pauli
Generator Transfer and Single-Trace Closure*.

**Author:** Lluis Eriksson.

**Frozen submission:** 6 pages, 2 tables, 1 figure.

The exact local artifacts were independently hashed before this repository
record was written:

```text
PDF  3A0AC2C21FE44AA524AD26BF29F15EC245D2C74F14108DC29D934D261D30D17D
ZIP  FCE8997D3DEAAF2AE4C4EFF75D27D261F52FC0A478C0C5B519AAF4C166556F2B
```

The uploaded file is
`machine-checked-su2-crossing-ward-weak-kappa2.pdf`.  The audit package
`ATTACH-THIS--SU2-CROSSING-WARD-WEAK-KAPPA2--FCE8997D.zip` is retained
outside ai.viXra for direct audit or referee requests.  PDF copies beginning
with SHA-256 `413D9133` or `2AAF52CB` are superseded and must not be used.

The paper formalizes a finite-dimensional crossing Ward identity for
fundamental SU(2) Wilson words on finite edge spaces.  It proves the Pauli
generator insertion, the mixed-derivative Fierz contraction, two Haar
integration-by-parts transfers, and exact closure on the direct and reverse
single-trace resolutions with the stated normalization coefficients
`-1/4` and `-1/2`.  The frozen audit reports 19 public declarations, with the
13 new theorems depending only on `propext`, `Classical.choice`, and
`Quot.sound`, and no local `sorry`, `admit`, or axiom.

## Scope boundary

This is not a full Makeenko--Migdal area equation.  The remaining physical
input is a weak four-face identity against crossing-certified
extended-gauge-invariant observables.  In the paper's Pauli-Laplacian heat
time, the coefficient is `kappa = 2`.  The submission does not change the
repository's stated distance to the four-dimensional continuum Yang--Mills
mass-gap problem.

## Exact submission comments

```text
6 pages, 2 tables, 1 figure. Lean 4.29.0-rc6; Mathlib commit 07642720480157414db592fa85b626dafb71355b. Clean-source build and audit passed. 19 public declarations; no sorry, admit, or local axiom.
```

Once ai.viXra assigns the public identifier, add it here and compare the
downloaded public PDF byte-for-byte with the frozen PDF hash above.
