import NtCvOS16

/-!
# NtFinal -- the refutations of the coverage-free headline for EVERY `ell >= 3` (lane ncwdh_small_ell_20261018)

All statements are about `NsCS1`'s `P428Target8NCWDHc c` / `FailsAtEll c ell _ a` (unchanged upstream module; CvS1's `P428Target8NCWDH` with the cube factor `12`
replaced by a parameter `c`; pinned to the frozen statement at `c = 12` by `target_twelve_iff`).

This is the `ncwdh_strong_20261017/NsFinal` composition re-run on a fork of the chain in which `StagOK ell` is `2 ∣ ell ∨ (ell % 2 = 1 ∧ 3 ≤ ell)`
(so `StagOK ell` holds for every `ell ≥ 3`), the odd-`ell` regularity cap is `tcap = 33/20` and the odd loop bound is `1 + 2 (ell-1) (2/ell²)`
(parity-refined alternating-sum ranges), the crossing bound is `cs ≥ -1/14`, and the test window of the nested chain is `p ∈ {0, ell}` on a window of `ell + 1` rows.

* `ncwdh_fails_all`   : for EVERY cube factor `c ≥ 10`, EVERY `ell ≥ 3`, EVERY `a > 0`: `FailsAtEll c ell a`.
* `ncwdh_fails_three` : the instance `ell = 3`.
* `not_P428Target8NCWDHc`, `not_P428Target8NCWDH_frozen`.
-/
set_option autoImplicit false

namespace AdalyFormal.NcwdhStrong

open AdalyFormal.CoverStrong (P428Target8NCWDH)

theorem stagOK_of_three {ell : ℕ} (h : 3 ≤ ell) : AdalyFormal.CoverOmega.StagOK ell := by
  by_cases hev : 2 ∣ ell
  · exact Or.inl hev
  · exact Or.inr ⟨by omega, h⟩

/-- **every `ell ≥ 3`**: for EVERY cube factor `c ≥ 10`, EVERY `a > 0`. -/
theorem ncwdh_fails_all (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell3 : 3 ≤ ell) (a : ℝ) (ha : 0 < a) :
    FailsAtEll c ell (by omega) a :=
  AdalyFormal.CoverOmega.Struct.failsAtEll_ok c hc ell hell3 (stagOK_of_three hell3) a ha

theorem ncwdh_fails_three (c : ℕ) (hc : 10 ≤ c) (a : ℝ) (ha : 0 < a) :
    FailsAtEll c 3 (by omega) a :=
  ncwdh_fails_all c hc 3 (le_refl 3) a ha

theorem not_P428Target8NCWDHc (c : ℕ) (hc : 10 ≤ c) : ¬ P428Target8NCWDHc c :=
  AdalyFormal.CoverOmega.Struct.not_P428Target8NCWDHc c hc

theorem not_P428Target8NCWDH_frozen : ¬ P428Target8NCWDH :=
  fun h => not_P428Target8NCWDHc 12 (by norm_num) (target_twelve_iff.mpr h)

#print axioms ncwdh_fails_all
#print axioms ncwdh_fails_three
#print axioms not_P428Target8NCWDHc
#print axioms not_P428Target8NCWDH_frozen

end AdalyFormal.NcwdhStrong
