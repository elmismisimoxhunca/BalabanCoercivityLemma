import NuA3
import CaT1
import CaT2d

theorem coverage_row_fails
    (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell : 2 ≤ ell)
    (a : ℝ) (ha : 0 < a) :
    AdalyFormal.NcwdhStrong.FailsAtEll c ell hell a :=
  NcwdhFam.ncwdh_fails_ge_two c hc ell hell a ha

theorem coverage_row_both
    (c : ℕ) (hc : 10 ≤ c) : CovAssume.P428Target8NCWDHcov c :=
  CovAssume.p428Target8NCWDHcov_of_total c hc

theorem coverage_row_ell2
    (c : ℕ) (hc : 10 ≤ c) (a : ℝ) (ha : 0 < a) :
    CovAssume.FamilyTorusCovConstAt c 2 (le_refl 2) a ∧
      ¬ CovAssume.FamilyTorusSitesConstAt c 2 (le_refl 2) a :=
  CovAssume.covPlaq_separately_necessary_two c hc a ha

#print axioms coverage_row_fails
#print axioms coverage_row_both
#print axioms coverage_row_ell2
