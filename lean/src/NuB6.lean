import NuB4
import NuB5

/-!
# NuB6 -- monotonicity of `<y, N(c)⁻¹ y>` in `c = cos 2t` for `Ad_h`-fixed `y` (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.CoverJacobi
open AdalyFormal.GaugeCov
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner hsInner_self_nonneg)
open AdalyFormal.StatementLane (scaleUp Tower)
open AdalyFormal.StatementLaneG
open scoped RealInnerProductSpace

section
variable [CfData]
variable {ell M R : ℕ}

/-- the parameter `t(w) = arccos w / 2` with `cos 2 t(w) = w`. -/
noncomputable def tOf (w : ℝ) : ℝ := Real.arccos w / 2

theorem cos_tOf {w : ℝ} (h1 : -1 ≤ w) (h2 : w ≤ 1) : Real.cos (2 * tOf w) = w := by
  unfold tOf
  rw [show 2 * (Real.arccos w / 2) = Real.arccos w by ring]
  exact Real.cos_arccos h1 h2

theorem abs_tOf_lt {w : ℝ} (h1 : -1 < w) : |tOf w| < Real.pi / 2 := by
  unfold tOf
  have h0 : 0 ≤ Real.arccos w := Real.arccos_nonneg w
  have hlt : Real.arccos w < Real.pi := Real.arccos_lt_pi.mpr h1
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem tOf_one : tOf 1 = 0 := by unfold tOf; simp

open Classical in
theorem bPl_nonneg {L : PeriodicLatticeExtent} (S Pl : Set (PeriodicLatticePlaquette L)) (w : BondFnL2 L) :
    0 ≤ bPl S Pl w w := by
  unfold bPl
  refine Finset.sum_nonneg (fun p _ => ?_)
  split_ifs
  · exact hsInner_self_nonneg _
  · exact le_rfl

theorem Nmat_eq (P : IngrBParams) :
    GenP.Nmat P = P.data.Q.comp ((Ring.inverse P.G1inv).comp P.data.Qs) := by
  unfold GenP.Nmat
  exact ContinuousLinearMap.ext (fun _ => rfl)

end

end AdalyFormal.NcwdhTwo
