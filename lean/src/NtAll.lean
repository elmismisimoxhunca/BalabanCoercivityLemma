import NtFinal
import NtFam4

/-!
# NtAll -- combined statements for every `ell >= 3` (lane ncwdh_small_ell_20261018)

* `ncwdh_fails_all`  (NtFinal) : `FailsAtEll c ell _ a` for every `c >= 10`, `ell >= 3`, `a > 0`.
* `famConst_all`     : the per-cube family headline with the constant family `constFam c` fails (`¬ FamilyTorusNCConstAt c ell _ a`) together with the full witness
  `ConstFamWitnessFull c ell hell3 a` (class cube present, all class cubes regular, `WellDefG`, an uncovered site of `Ω₀`, failing competitor), for every `c >= 10`, `ell >= 3`, `a > 0`.
* `ncwdh_all`        : the conjunction of both, for every `ell >= 3`.
-/
set_option autoImplicit false

namespace NcwdhFam

open AdalyFormal.NcwdhStrong
open AdalyFormal.Target.ClayStatement

theorem famConst_all (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell3 : 3 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ¬ FamilyTorusNCConstAt c ell (by omega) a ∧ ConstFamWitnessFull c ell hell3 a :=
  constFam_headline c hc ell hell3 (stagOK_of_three hell3) a ha

theorem ncwdh_all (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell3 : 3 ≤ ell) (a : ℝ) (ha : 0 < a) :
    FailsAtEll c ell (by omega) a ∧ ¬ FamilyTorusNCConstAt c ell (by omega) a ∧ ConstFamWitnessFull c ell hell3 a :=
  ⟨ncwdh_fails_all c hc ell hell3 a ha, (famConst_all c hc ell hell3 a ha).1, (famConst_all c hc ell hell3 a ha).2⟩

theorem ncwdh_all_three (c : ℕ) (hc : 10 ≤ c) (a : ℝ) (ha : 0 < a) :
    FailsAtEll c 3 (by omega) a ∧ ¬ FamilyTorusNCConstAt c 3 (by omega) a ∧ ConstFamWitnessFull c 3 (le_refl 3) a :=
  ncwdh_all c hc 3 (le_refl 3) a ha

#print axioms famConst_all
#print axioms ncwdh_all
#print axioms ncwdh_all_three

end NcwdhFam
