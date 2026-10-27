import ProductAngle
import T1MainSegment

set_option autoImplicit false

/-! Direct consumer adapter to the certified principalSuTwoLog subtype. -/
namespace SmallnessBridge.ProdBound

open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.Bch2
open AdalyFormal.Balaban.RMapLipschitz
open AdalyFormal.DeltaKR66 (principalSuTwoLog)

/-- Definitional subtype adapter; the certified logarithm is not replaced or redefined. -/
theorem nu_principalSuTwoLog_eq_angle {g : SU2} (h : su2Angle g ≤ Real.pi / 2) :
    nu ((principalSuTwoLog g : AdalyFormal.Balaban.CovariantOperators.SuTwo) : M2) =
      su2Angle g := nu_su2Log_eq_angle h

/-- Direct bridge from a contour's factor list to the norm-bound domain. -/
theorem principal_list_prod_small (gs : List SU2) (delta : ℝ)
    (h : ∀ g ∈ gs, su2Angle g ≤ delta)
    (hsmall : (gs.length : ℝ) * delta < Real.pi / 2) :
    nu ((principalSuTwoLog gs.prod : AdalyFormal.Balaban.CovariantOperators.SuTwo) : M2) ≤
      (gs.length : ℝ) * delta ∧ (gs.length : ℝ) * delta < Real.pi / 2 :=
  ⟨(list_prod_small_log gs delta h hsmall).1, hsmall⟩

/-- The same adapter for the requested gₙ ··· g₁ ordering. -/
theorem principal_reverse_prod_small (gs : List SU2) (delta : ℝ)
    (h : ∀ g ∈ gs, su2Angle g ≤ delta)
    (hsmall : (gs.length : ℝ) * delta < Real.pi / 2) :
    nu ((principalSuTwoLog gs.reverse.prod : AdalyFormal.Balaban.CovariantOperators.SuTwo) : M2) ≤
      (gs.length : ℝ) * delta ∧ (gs.length : ℝ) * delta < Real.pi / 2 := by
  simpa only [List.length_reverse] using principal_list_prod_small gs.reverse delta
    (fun g hg => h g (List.mem_reverse.mp hg)) (by simpa only [List.length_reverse] using hsmall)

/-- Exact printed-style Frobenius sufficient condition, retaining its strict threshold. -/
theorem principal_list_prod_frobNorm_cap (gs : List SU2) (eps : ℝ)
    (h : ∀ g ∈ gs, frobNorm ((g : M2) - 1) ≤ eps) (heps : eps ≤ 2)
    (hsmall : (gs.length : ℝ) * eps < 2) :
    nu ((principalSuTwoLog gs.prod : AdalyFormal.Balaban.CovariantOperators.SuTwo) : M2) ≤
      (gs.length : ℝ) * ((Real.pi / 4) * eps) ∧
      (gs.length : ℝ) * ((Real.pi / 4) * eps) < Real.pi / 2 :=
  list_prod_small_log_of_frobNorm_cap gs eps h heps hsmall

#print axioms nu_principalSuTwoLog_eq_angle
#print axioms principal_list_prod_small
#print axioms principal_reverse_prod_small
#print axioms principal_list_prod_frobNorm_cap

end SmallnessBridge.ProdBound
