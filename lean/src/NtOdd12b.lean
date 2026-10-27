import NtOdd12

/-!
# NsOdd12b -- `H0Good`: the `H0` family of the nested staggered family, both parities (lane ncwdh_strong_20261017)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace Topology
open Set Filter
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG

variable {ell M R : ℕ}

theorem pn_H0_good (hell3 : 3 ≤ ell) (hE : StagOK ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a : ℝ) :
    H0Good ell M R (by omega) a := by
  rcases hE with hE | ⟨hO, h3⟩
  · refine ⟨fun _ => 1, fun _ _ => analyticAt_const, ⟨0, ⟨by linarith [tcap_pos ell], tcap_pos ell⟩, one_ne_zero⟩, fun t htπ _ => ?_⟩
    exact Pn_H0_bijective_even hell3 hE hdvd hM hR a t (abs_lt_pi_of_tcap htπ)
  · obtain ⟨dH, hdH, h0, hb⟩ := pn_H0_odd hell3 hO h3 hdvd hM hR a
    unfold H0Good
    rw [tcap_odd hO]
    exact ⟨dH, hdH, ⟨0, ⟨by norm_num, by norm_num⟩, h0⟩, hb⟩

#print axioms pn_H0_good

end AdalyFormal.CoverOmega
