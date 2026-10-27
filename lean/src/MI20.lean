import MI19

/-!
# MI20 -- the tail-weighted norm `N(B) = ‖e^{−σ} B‖²` (M1 lane E, 2026-10-13)

* `N_le_wnorm` : `N(B) ≤ wnormSq B` (tail stratum ≥ both-endpoint stratum);
* `nsum_partition` : `Σ_p N(h_p B) = N(B)` for `B` supported on bonds touching `Ω₀`.
(`ginvIMS_of`, the W1 output, is assembled in MI22.)
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply deltaPrimeBilL2NormLoc)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

variable {L : PeriodicLatticeExtent}

section N
variable {Lf : PeriodicLatticeExtent} {ell M R k κ c : ℕ} {S : Tower Lf}

/-- the tail-weighted norm is dominated by the both-endpoint weighted norm. -/
theorem N_le_wnorm (hS : Admissible ell M R k S) (hell0 : 0 < ell) (B : BondFnL2 Lf) :
    ‖bondWt (-sigG (geomOf ell k S)) B‖ ^ 2 ≤ AdalyFormal.M1.wnormSq S ell k B := by
  rw [PiLp.norm_sq_eq_of_L2]
  unfold AdalyFormal.M1.wnormSq
  refine Finset.sum_le_sum (fun b _ => ?_)
  rw [bondWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  show Real.exp (-(sigG (geomOf ell k S) b.1)) ^ 2 ≤ _
  rw [Real.exp_neg, exp_sig (geomOf ell k S) hell0, ← strat_eq_stratG hell0 hS]
  have hb : AdalyFormal.M1.bstrat S k b ≤ AdalyFormal.M1.strat S k b.1 := min_le_left _ _
  have h1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell0
  have h2 : (0 : ℝ) < (ell : ℝ) ^ AdalyFormal.M1.bstrat S k b := by positivity
  have h3 : (ell : ℝ) ^ AdalyFormal.M1.bstrat S k b ≤ (ell : ℝ) ^ AdalyFormal.M1.strat S k b.1 :=
    pow_le_pow_right₀ h1 hb
  exact pow_le_pow_left₀ (by positivity) (inv_anti₀ h2 h3) 2

/-- the tail-weighted norm is partitioned by `hbond` on `bondSupp`. -/
theorem nsum_partition (hS : Admissible ell M R k S) (hc : 5 ≤ c) (hκ : 0 < κ) (hM : 0 < M) (hell0 : 0 < ell)
    (B : BondFnL2 Lf) (hB : ∀ b : Bond Lf, ¬ (b.1 ∈ S.Om 0 ∨ periodicLatticeShift b.1 b.2 ∈ S.Om 0) → B b = 0) :
    ∑ p, ‖bondWt (-sigG (geomOf ell k S)) (bondMul (hbond ell M k κ c S p) B)‖ ^ 2
      = ‖bondWt (-sigG (geomOf ell k S)) B‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [bondWt_apply, bondMul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  by_cases hb : b.1 ∈ S.Om 0 ∨ periodicLatticeShift b.1 b.2 ∈ S.Om 0
  · have h1 := sum_hbond_sq (k := k) (κ := κ) (M := M) (c := c) (S := S) (ell := ell) hc hκ hM hell0 hb
    calc ∑ p, Real.exp ((-sigG (geomOf ell k S)) b.1) ^ 2 * (hbond ell M k κ c S p b ^ 2 * ‖B b‖ ^ 2)
        = Real.exp ((-sigG (geomOf ell k S)) b.1) ^ 2 * ((∑ p, hbond ell M k κ c S p b ^ 2) * ‖B b‖ ^ 2) := by
          rw [Finset.sum_mul, Finset.mul_sum]
      _ = _ := by rw [h1, one_mul]
  · rw [hB b hb]; simp

end N

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.N_le_wnorm
#print axioms AdalyFormal.M1IMS.nsum_partition
