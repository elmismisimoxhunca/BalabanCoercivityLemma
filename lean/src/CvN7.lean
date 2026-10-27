import CvN6

/-!
# CvN7 -- the two-sided statement: coverage is SUFFICIENT (proved r8 headline) and NECESSARY (lane cover_necessary_20261016)

* `coverage_necessary`: the r8 headline `P428Target8` (with `CoversOm0p`) holds (lane m2_rightinv_20261015, `p428Target8`) AND the
  same headline with `CoversOm0p` removed, `P428Target8NC`, is false (CvN6 `not_P428Target8NC`).
* `coverage_necessary_general`: for every bound `F ≥ 12`, the general-class headline WITH r8's coverage hypothesis holds
  (lane general_class_20261015, `p428Target8GC`) and WITHOUT any coverage hypothesis it is false (CvN6 `not_P428Target8G`).
-/
set_option autoImplicit false

namespace AdalyFormal.CoverNec

theorem coverage_necessary :
    AdalyFormal.StatementLaneG.P428Target8 ∧ ¬ AdalyFormal.NoCover.P428Target8NC :=
  ⟨AdalyFormal.M2RightInv.p428Target8, not_P428Target8NC⟩

theorem coverage_necessary_general (F : ℕ) (hF : 12 ≤ F) :
    AdalyFormal.GeneralClass.P428Target8GC F ∧ ¬ AdalyFormal.GeneralClass.P428Target8G F :=
  ⟨AdalyFormal.GeneralClass.p428Target8GC hF, not_P428Target8G F⟩

#print axioms coverage_necessary
#print axioms coverage_necessary_general

end AdalyFormal.CoverNec
