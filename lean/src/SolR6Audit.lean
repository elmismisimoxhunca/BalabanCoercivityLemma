import GdR6b
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
namespace SolR6Audit
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2 AdalyFormal.D1Literal AdalyFormal.D1Guarded AdalyFormal.NonVac
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

-- Fresh composition of committed cancellation with the actual negative vector.
-- This does NOT use G1inv_diff_eq, and asserts no units at pi.
theorem corrected_domination_fails_pi (sJ : PlaqSel) {m R : ℕ}
    (hm : 1 ≤ m) (hR : 18 ≤ R) {α₀ : ℝ} (hα : 0 < α₀) :
    ∃ v : ↥(bondSupp (geomOf 2 2 (SlabNv 2 (2 ^ m) R))),
      ⟪v, G1invS selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R)
        (Uth ((SlabNv 2 (2 ^ m) R).Om 0) Real.pi) 1 (LamN (2 ^ m) R)) v⟫ < 0 ∧
      0 ≤ ⟪v, G1invS selIn selIn (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R)
        (Uth ((SlabNv 2 (2 ^ m) R).Om 0) Real.pi) 1 (LamN (2 ^ m) R)) v⟫ := by
  have hM : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hdvd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have G := slabGeo_inst (ell := 2) (show 2 ≤ 2 by omega) hM hdvd (show 1 ≤ R by omega)
  have hN : ∀ μ, scaleUp 2 2 (nvLu (2 ^ m) R) μ + 1 = nvN 2 (2 ^ m) R := fun μ => scaleUp_nv (by norm_num) hM μ
  have hAdm : Admissible 2 (2 ^ m) R 2 (SlabNv 2 (2 ^ m) R) := slab3_admissible G hN
  have h3 : 3 ≤ R * 2 ^ m := by nlinarith
  obtain ⟨_, v, hv, hv'⟩ := domination_fails_pi sJ hm hR hα
  have e1 := G1invS_eq_Ginv_theta selAll sJ
    (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R)
        (Uth ((SlabNv 2 (2 ^ m) R).Om 0) Real.pi) 1 (LamN (2 ^ m) R)) hAdm (by norm_num) h3 Real.pi rfl
  have e2 := G1invS_eq_Ginv_theta selIn selIn
    (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R)
        (Uth ((SlabNv 2 (2 ^ m) R).Om 0) Real.pi) 1 (LamN (2 ^ m) R)) hAdm (by norm_num) h3 Real.pi rfl
  refine ⟨v, ?_, ?_⟩
  · rw [e1]; exact hv
  · rw [e2]; exact hv'

-- A real input assertion used for S82: the zero endomorphism must not pass.
noncomputable def checkedOp : ℝ →L[ℝ] ℝ := 1
theorem checked_unit : IsUnit checkedOp := by
  exact (isUnit_one : IsUnit (1 : ℝ →L[ℝ] ℝ))

-- Another input assertion: actual NV seed, not a redefined energy.
noncomputable def checkedSeed (m R : ℕ) (hM : 0 < 2^m) : Bond (nvLu (2^m) R) → SuTwo := BseedNv 2 hM
theorem checked_energy (m R : ℕ) (hm : 1 ≤ m) :
    0 < AdalyFormal.Balaban.RegularUPerturbation.bondEnergy (checkedSeed m R (pow_pos (by norm_num) m)) := by
  have hM : 0 < 2^m := pow_pos (by norm_num) m
  have hdvd : 2 ∣ 2^m := dvd_pow_self 2 (by omega)
  exact (BseedNv_props (R := R) (show 2 ≤ 2 by omega) hdvd hM).2.2.1
#print axioms corrected_domination_fails_pi
#print axioms checked_unit
#print axioms checked_energy
end SolR6Audit
#print axioms AdalyFormal.D1Guarded.G1inv_diff_eq
#print axioms AdalyFormal.D1Guarded.domination_fails_pi
#print axioms AdalyFormal.D1Guarded.Ginv_loc_psd_twist
#print axioms AdalyFormal.D1Guarded.Delta2_eq_zero_of_Jperp
#print axioms AdalyFormal.D1Guarded.JfS_vanish_base
#print axioms AdalyFormal.D1Guarded.G1invS_eq_Ginv_base
#print axioms AdalyFormal.D1Guarded.SG_on_base_flat_family
#print axioms AdalyFormal.D1Literal.literal_Ginv_indefinite
#print axioms AdalyFormal.D1Literal.Fth_pi_neg
#print axioms AdalyFormal.D1Guarded.G1invS_eq_Ginv_theta
#print axioms AdalyFormal.D1Guarded.P428Target8SG_iff_residualT
#print axioms AdalyFormal.D1Guarded.nv_guard_nonvacuous
#print axioms AdalyFormal.D1Guarded.TwoData.Delta2_eq
