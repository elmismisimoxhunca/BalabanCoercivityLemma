import SoA1
import CsA2

/-!
# SoA2 -- the table of the constant-family granting-existence bodies on the arithmetic family `ell ∣ 2 (c - 1)`, `ell` even (lane sites_only_20261019)

* `not_familyTorusSitesConstAt_div` : `ell ≥ 4` even (`ell ≥ 3` and `2 ∣ ell`), `c ≥ 10`, `ell ∣ 2 (c - 1)`, `9 ell ≤ 2 (c - 1)`: the sites-only body fails.
* `sites_only_table_even`            : for `ell` even, `c ≥ 10`, `ell ∣ 2 (c-1)` and (`ell = 2` or `9 ell ≤ 2 (c-1)`): both-clause body holds, plaquette-only body holds, sites-only body fails.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

open CovAssume
open CovSplit

theorem not_familyTorusSitesConstAt_div (c ell : ℕ) (hell3 : 3 ≤ ell) (hE : 2 ∣ ell) (hc : 10 ≤ c)
    (hdiv : ell ∣ 2 * (c - 1)) (hw : 9 * ell ≤ 2 * (c - 1)) (a : ℝ) (ha : 0 < a) :
    ¬ FamilyTorusSitesConstAt c ell (by omega) a := by
  obtain ⟨q, hq⟩ := hdiv
  have hq9 : 9 ≤ q := by
    have : ell * 9 ≤ ell * q := by rw [← hq]; linarith
    exact Nat.le_of_mul_le_mul_left this (by omega)
  exact not_familyTorusSitesConstAt_S c ell hell3 hE hc (q + 1) (by omega) (by simpa using hq.symm) a ha

theorem sites_only_table_even (c ell : ℕ) (hE : 2 ∣ ell) (hell : 2 ≤ ell) (hc : 10 ≤ c)
    (hdiv : ell ∣ 2 * (c - 1)) (hw : ell = 2 ∨ 9 * ell ≤ 2 * (c - 1)) (a : ℝ) (ha : 0 < a) :
    FamilyTorusCovConstAt c ell hell a ∧ FamilyTorusPlaqConstAt c ell hell a ∧ ¬ FamilyTorusSitesConstAt c ell hell a := by
  refine ⟨familyTorusCovConstAt_of_proved hc ell hell a ha, familyTorusPlaqConstAt_holds hc ell hell a ha, ?_⟩
  by_cases h2 : ell = 2
  · subst h2
    exact not_familyTorusSitesConstAt_two c hc a ha
  · have hell3 : 3 ≤ ell := by omega
    have h9 : 9 * ell ≤ 2 * (c - 1) := by
      rcases hw with h | h
      · exact absurd h h2
      · exact h
    exact not_familyTorusSitesConstAt_div c ell hell3 hE hc hdiv h9 a ha

#print axioms not_familyTorusSitesConstAt_div
#print axioms sites_only_table_even

end AdalyFormal.SitesOnly
