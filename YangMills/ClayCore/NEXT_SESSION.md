# Next Session: L2.6 --- Character Schur orthogonality on SU(N_c)

## Target (full form)

    theorem sunHaarProb_character_orthogonality
        {N : Nat} [NeZero N] (rho sigma : IrrepIndex) (h : rho != sigma) :
        (integral U : Matrix.specialUnitaryGroup (Fin N) Complex,
            character rho U * star (character sigma U) d(sunHaarProb N)) = 0

plus the equality case for rho = sigma.

## Strategy (two-step, mirrors L2.3/L2.5)

### Step 1 --- fundamental entry-pair orthogonality

Prove the restricted statement

    integral U_ij * star (U_kl) dHaar  =  (delta_ik * delta_jl) / N

by left-invariance against both the two-site phase and the coordinate
permutation subgroup S_N subset SU(N) (acting by permutation of basis
vectors, sign-corrected to keep det = 1). This gives the fundamental-
times-antifundamental Schur block --- directly computable, concrete.

### Step 2 --- general irreps

Abstract over IrrepIndex and character : IrrepIndex -> U -> C.
Use step 1 plus the algebraic decomposition of (character rho)*(character sigma)
into irreducible blocks, already packaged abstractly in
CharacterExpansion.lean.

## Realistic scope for next session: STEP 1 only

The restricted identity

    integral U_ij * conj(U_kl) dHaar = delta_ik * delta_jl / N

on SU(N), because:

- It is a direct generalization of L2.5 (L2.5 = the i=k=j=l case gives
  integral |U_ii|^2 <= 1; summing over i gives integral |tr U|^2 <= N_c).
- The two-site phase argument of L2.5 step B extends directly to
  distinguish (i, j) from (k, l).
- The 1/N normalization drops out from combining
  sum_i integral |U_ii|^2 = 1 (once <= is upgraded to = via the
  permutation invariance).

Step 2 (general character orthogonality) requires Peter-Weyl
infrastructure not yet in Mathlib and is a separate milestone.

## File layout

- SchurEntryOrthogonality.lean   --- step 1, the i/j/k/l restricted form
- (step 2 file deferred to a later session)

## Proof sketch for step 1

1. For any i, by sunHaarProb left-invariance against any permutation
   P_pi in S_N subset SU(N) (sign-corrected), the integral
   integral |U_{pi(i), pi(j)}|^2 dHaar is the same for all (pi(i), pi(j)).
   So all N^2 entries give the same value.
2. L2.5 gives integral |U_ii|^2 <= 1 and sum_i integral |U_ii|^2 <= N.
   Combined with step 1 (all entries equal), integral |U_ij|^2 = 1/N.
3. For off-diagonal entries (i, j) vs (k, l) with (i, j) != (k, l),
   the two-site phase (adapted) kills the cross term exactly as in L2.5-B.

## Rules (unchanged)

- no sorry, no new axioms
- oracle must stay [propext, Classical.choice, Quot.sound]
- push after every green milestone
- update docs every 3 commits
- split files if > 150 lines