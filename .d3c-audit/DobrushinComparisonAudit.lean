/-
D-3c TERMINAL AUDIT DRIVER

Target commit 40ca85239cb14f18ebf16aa46769f3bc02bbaf6b
Target blob   3fe356cc97e57f2d241158b692e6b8a3acece83a
Canonical     698080fa80ea44d2f1ae7b46cab333b5d0d6f4b97d205df2844db69d510017ea

This driver IS the manifest printed in the module header, written with FULLY
QUALIFIED names so that nothing here depends on an implicit `open`.

  11 load-bearing / interface theorems
   4 headline witness theorems
  16 supporting witness lemmas
  --
  31 theorems        -- #check AND #print axioms
   9 definitions     -- #check only; compiled, NOT claimed Formalized
  --
  40 named declarations = manifest coverage.  40/40 means COVERAGE OF THE
     MANIFEST, never `40 theorems`.
-/
import YangMills.OS.DobrushinComparison

-- ===== SECTION 1: 11 load-bearing / interface theorems =====
#check @YangMills.OS.Dobrushin.deltaAt_siteExp_self   -- endpoint  -- deltaAt i (E i f) = 0
#check @YangMills.OS.Dobrushin.deltaAt_siteExp_le   -- endpoint  -- THE key lemma
#check @YangMills.OS.Dobrushin.Bupd_mulVec   -- endpoint  -- coordinate formula, orientation
#check @YangMills.OS.Dobrushin.deltaVec_siteExp_le   -- endpoint  -- matrix form, consumes C i i = 0
#check @YangMills.OS.Dobrushin.deltaAt_eq_deltaAtOff   -- convention equivalence
#check @YangMills.OS.Dobrushin.abs_sub_update_le   -- oscillation auxiliary
#check @YangMills.OS.Dobrushin.abs_sub_le_deltaAt   -- oscillation auxiliary
#check @YangMills.OS.Dobrushin.deltaAt_nonneg   -- oscillation auxiliary
#check @YangMills.OS.Dobrushin.C_nonneg_of_majorant   -- D-3d interface, OFF-DIAGONAL only
#check @YangMills.OS.Dobrushin.Bupd_mulVec_mono   -- D-3d interface, needs global nonnegativity
#check @YangMills.OS.Dobrushin.Bupd_mulVec_mono_of_majorant   -- D-3d interface, assembles both sources

-- ===== SECTION 2: 4 headline witness theorems =====
#check @YangMills.OS.Dobrushin.deltaVec_hypotheses_satisfiable   -- satisfiability, DEGENERATE (C = 0)
#check @YangMills.OS.Dobrushin.Witness.hypotheses_hold   -- satisfiability, NON-degenerate (C 0 1 != 0)
#check @YangMills.OS.Dobrushin.Witness.pw_tv_attained   -- the MAJORANT is attained
#check @YangMills.OS.Dobrushin.Witness.deltaAt_siteExp_attained   -- the TRANSPORT bound is attained

-- ===== SECTION 3: 16 supporting witness lemmas =====
#check @YangMills.OS.Dobrushin.uniformKernel_local
#check @YangMills.OS.Dobrushin.uniformKernel_nonneg
#check @YangMills.OS.Dobrushin.uniformKernel_sum
#check @YangMills.OS.Dobrushin.uniformKernel_tv
#check @YangMills.OS.Dobrushin.Witness.fw_update_zero
#check @YangMills.OS.Dobrushin.Witness.fw_update_one
#check @YangMills.OS.Dobrushin.Witness.pw_local
#check @YangMills.OS.Dobrushin.Witness.two_cases
#check @YangMills.OS.Dobrushin.Witness.pw_nonneg
#check @YangMills.OS.Dobrushin.Witness.pw_sum
#check @YangMills.OS.Dobrushin.Witness.Cw_diag
#check @YangMills.OS.Dobrushin.Witness.pw_tv
#check @YangMills.OS.Dobrushin.Witness.siteExp_pw
#check @YangMills.OS.Dobrushin.Witness.deltaAt_zero_fw
#check @YangMills.OS.Dobrushin.Witness.deltaAt_one_fw
#check @YangMills.OS.Dobrushin.Witness.deltaAt_one_siteExp

-- ===== SECTION 4: 9 definitions (compiled; axiom cones NOT reported here) =====
#check @YangMills.OS.Dobrushin.deltaAt
#check @YangMills.OS.Dobrushin.deltaAtOff
#check @YangMills.OS.Dobrushin.siteExp
#check @YangMills.OS.Dobrushin.LocalKernel
#check @YangMills.OS.Dobrushin.Bupd
#check @YangMills.OS.Dobrushin.uniformKernel
#check @YangMills.OS.Dobrushin.Witness.pw
#check @YangMills.OS.Dobrushin.Witness.Cw
#check @YangMills.OS.Dobrushin.Witness.fw

-- ===== SECTION 5: axiom cones, 31 theorems, none omitted =====
#print axioms YangMills.OS.Dobrushin.deltaAt_siteExp_self
#print axioms YangMills.OS.Dobrushin.deltaAt_siteExp_le
#print axioms YangMills.OS.Dobrushin.Bupd_mulVec
#print axioms YangMills.OS.Dobrushin.deltaVec_siteExp_le
#print axioms YangMills.OS.Dobrushin.deltaAt_eq_deltaAtOff
#print axioms YangMills.OS.Dobrushin.abs_sub_update_le
#print axioms YangMills.OS.Dobrushin.abs_sub_le_deltaAt
#print axioms YangMills.OS.Dobrushin.deltaAt_nonneg
#print axioms YangMills.OS.Dobrushin.C_nonneg_of_majorant
#print axioms YangMills.OS.Dobrushin.Bupd_mulVec_mono
#print axioms YangMills.OS.Dobrushin.Bupd_mulVec_mono_of_majorant
#print axioms YangMills.OS.Dobrushin.deltaVec_hypotheses_satisfiable
#print axioms YangMills.OS.Dobrushin.Witness.hypotheses_hold
#print axioms YangMills.OS.Dobrushin.Witness.pw_tv_attained
#print axioms YangMills.OS.Dobrushin.Witness.deltaAt_siteExp_attained
#print axioms YangMills.OS.Dobrushin.uniformKernel_local
#print axioms YangMills.OS.Dobrushin.uniformKernel_nonneg
#print axioms YangMills.OS.Dobrushin.uniformKernel_sum
#print axioms YangMills.OS.Dobrushin.uniformKernel_tv
#print axioms YangMills.OS.Dobrushin.Witness.fw_update_zero
#print axioms YangMills.OS.Dobrushin.Witness.fw_update_one
#print axioms YangMills.OS.Dobrushin.Witness.pw_local
#print axioms YangMills.OS.Dobrushin.Witness.two_cases
#print axioms YangMills.OS.Dobrushin.Witness.pw_nonneg
#print axioms YangMills.OS.Dobrushin.Witness.pw_sum
#print axioms YangMills.OS.Dobrushin.Witness.Cw_diag
#print axioms YangMills.OS.Dobrushin.Witness.pw_tv
#print axioms YangMills.OS.Dobrushin.Witness.siteExp_pw
#print axioms YangMills.OS.Dobrushin.Witness.deltaAt_zero_fw
#print axioms YangMills.OS.Dobrushin.Witness.deltaAt_one_fw
#print axioms YangMills.OS.Dobrushin.Witness.deltaAt_one_siteExp
