-- CREDIT: compute/d1_literal_prosecution_20261018/lean/D1PGen.lean (prosecutor probe PROS-D1LIT-20261018), copied unchanged except this header line; imports D1Cons.
import D1Cons

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NonVac
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- PROSECUTION PROBE: the literal reading fails at EVERY ell >= 2 and every 0 < a < 4 (fixed-ell slice of the headline). -/
theorem not_literal_every_ell (sJ : PlaqSel) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) (ha4 : a < 4) :
    ¬ (∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8S selAll sJ ell (ell ^ m) R (by omega) a) := by
  intro h
  obtain ⟨m₀, hm₀, hm⟩ := h
  obtain ⟨R₀, hR₀⟩ := hm m₀ le_rfl
  have hRge : R₀ ≤ max R₀ 18 := le_max_left _ _
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hcore⟩ := hR₀ (max R₀ 18) hRge
  obtain ⟨R, hRdef⟩ : ∃ R, R = max R₀ 18 := ⟨_, rfl⟩
  rw [← hRdef] at hcore
  have hR18 : 18 ≤ R := by rw [hRdef]; exact le_max_right _ _
  obtain ⟨M, hMdef⟩ : ∃ M, M = ell ^ m₀ := ⟨_, rfl⟩
  rw [← hMdef] at hcore
  have hell0 : 0 < ell := by omega
  have hM : 0 < M := by rw [hMdef]; exact pow_pos hell0 m₀
  have hdvd : ell ∣ M := by rw [hMdef]; exact dvd_pow_self ell (by omega)
  have hellM : ell ≤ M := Nat.le_of_dvd hM hdvd
  have G := slabGeo_inst (ell := ell) hell hM hdvd (show 1 ≤ R by omega)
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nv_widths (ell := ell) hell hM hR18
  have hN : ∀ μ, scaleUp ell 2 (nvLu M R) μ + 1 = nvN ell M R := fun μ => scaleUp_nv hell0 hM μ
  have hAdm : Admissible ell M R 2 (SlabNv ell M R) := slab3_admissible G hN
  have hcov : CoversOm0p ell M 12 2 (SlabNv ell M R) := slab3_coversp G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  obtain ⟨x, hbd⟩ := SlabNv_bdpt hell hdvd hM hR18
  have hroom : 17 * ell ≤ R * M := by nlinarith
  obtain ⟨θ, h0, h1, hnu⟩ := exists_nonunit_Ginv sJ (ell := ell) (M := M) (R := R) (k := 2) (Lu := nvLu M R) hell0
    (S := SlabNv ell M R) a (LamN M R) hAdm hell hroom hbd ha.le ha4
  obtain ⟨α₀, hα0def⟩ : ∃ α₀ : ℝ, α₀ = min (a₀ / (12 * M)) 1 / 2 := ⟨_, rfl⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hα0 : 0 < α₀ := by
    rw [hα0def]
    have : 0 < a₀ / (12 * (M : ℝ)) := by positivity
    have := lt_min this one_pos; positivity
  have hαS : (12 : ℝ) * M * α₀ ≤ a₀ := by
    rw [hα0def]
    have h := min_le_left (a₀ / (12 * (M : ℝ))) 1
    have h2 : (12 : ℝ) * M * (a₀ / (12 * M)) = a₀ := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 12 * M)
    have h0 : 0 ≤ min (a₀ / (12 * (M : ℝ))) 1 := le_min (by positivity) zero_le_one
    nlinarith
  have hηpos : (0 : ℝ) < (((ell : ℝ)) ^ 2)⁻¹ := inv_pos.mpr (pow_pos (by exact_mod_cast hell0) 2)
  have hcls : ClassCoupled ell M 12 2 (SlabNv ell M R) α₀ (((ell : ℝ)) ^ 2)⁻¹ (Uth ((SlabNv ell M R).Om 0) θ) :=
    ⟨hcov, perCubeRegular2_of_one_on_om0 _ hAdm.1 hα0 hM (by norm_num) hell0 hηpos _
      (fun e he _ => Uth_in _ _ e he)⟩
  have hineq := hcore 2 (by norm_num) (nvLu M R) α₀ hα0 (by simpa using hαS) (torusOK_nv hell hdvd hM)
    (SlabNv ell M R) hAdm (LamN M R) (lambdaOK2_nv hell hdvd hM (show 1 ≤ R by omega)) (Uth ((SlabNv ell M R).Om 0) θ) hcls
  obtain ⟨hB1, hB2, hB3, hB4⟩ := BseedNv_props (R := R) hell hdvd hM
  exact not_InstIneqS_of_not_unit selAll sJ ell 2 hell0 a ha.le (nvLu M R) γ₀ hγ (SlabNv ell M R) (LamN M R)
    (Uth ((SlabNv ell M R).Om 0) θ) hnu _ hB1 hB2 hB3 hineq

#print axioms not_literal_every_ell
end AdalyFormal.D1Literal
