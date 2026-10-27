import GN11
import GN12
import AdalyFormal.Balaban.OnRangeCoercivity

/-!
# GN13 -- the local curl drift `δc` of GN12 from the link sup (tree `plaqEnergy_curlDrift_le`)

`hc_of_frobSup`: `‖χ_P curl_1 x - χ_P curl_U x‖ ≤ 4√2 · frobSupBond U · ‖x‖` for every plaquette set `P`
(every `Ω₀`).  In M0: `frobSupBond U ≲ ρ/n`, so `n² δc² = 32 ρ²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg frobNorm_le_frobSupBond curlDrift
  curlDrift_apply plaqEnergy plaqEnergy_curlDrift_le)

variable {L : PeriodicLatticeExtent}

theorem hc_of_frobSup (U : Cfg L) (P : Set (PeriodicLatticePlaquette L)) (x : BondFnL2 L) :
    ‖AdalyFormal.StatementLaneR6.plaqMask P (curlCovariantLM_L2 (trivialU L) x)
      - AdalyFormal.StatementLaneR6.plaqMask P (curlCovariantLM_L2 U x)‖
      ≤ (4 * Real.sqrt 2 * frobSupBond U) * ‖x‖ := by
  set α := frobSupBond U
  have hα0 : 0 ≤ α := frobSupBond_nonneg U
  have hE := plaqEnergy_curlDrift_le U (WithLp.ofLp x) α hα0 (frobNorm_le_frobSupBond U)
  have hx2 : ‖x‖ ^ 2 = AdalyFormal.Balaban.RegularUPerturbation.bondEnergy (WithLp.ofLp x) :=
    AdalyFormal.Balaban.OnRangeCoercivity.norm_sq_eq_bondEnergy x
  have hsq : ‖AdalyFormal.StatementLaneR6.plaqMask P (curlCovariantLM_L2 (trivialU L) x)
      - AdalyFormal.StatementLaneR6.plaqMask P (curlCovariantLM_L2 U x)‖ ^ 2
      ≤ plaqEnergy (curlDrift U (WithLp.ofLp x)) := by
    rw [PiLp.norm_sq_eq_of_L2]
    unfold plaqEnergy
    refine Finset.sum_le_sum (fun p _ => ?_)
    rw [PiLp.sub_apply, AdalyFormal.StatementLaneR6.plaqMask_apply, AdalyFormal.StatementLaneR6.plaqMask_apply]
    split_ifs
    · have h : (curlCovariantLM_L2 (trivialU L) x) p - (curlCovariantLM_L2 U x) p
          = -(curlDrift U (WithLp.ofLp x) p) := by
        show curlValueCovariant (trivialU L) (WithLp.ofLp x) p - curlValueCovariant U (WithLp.ofLp x) p = _
        simp [curlDrift]
      rw [h, norm_neg]
    · simp
  have hfin : ‖AdalyFormal.StatementLaneR6.plaqMask P (curlCovariantLM_L2 (trivialU L) x)
      - AdalyFormal.StatementLaneR6.plaqMask P (curlCovariantLM_L2 U x)‖ ^ 2
      ≤ ((4 * Real.sqrt 2 * α) * ‖x‖) ^ 2 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have : ((4 * Real.sqrt 2 * α) * ‖x‖) ^ 2 = 32 * α ^ 2 * ‖x‖ ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, h2]; ring
    rw [this, hx2]
    linarith
  have hr : 0 ≤ (4 * Real.sqrt 2 * α) * ‖x‖ := by positivity
  by_contra h
  have h' := lt_of_not_ge h
  nlinarith [norm_nonneg (AdalyFormal.StatementLaneR6.plaqMask P (curlCovariantLM_L2 (trivialU L) x)
      - AdalyFormal.StatementLaneR6.plaqMask P (curlCovariantLM_L2 U x))]

#print axioms hc_of_frobSup

end AdalyFormal.SliceCoerc
