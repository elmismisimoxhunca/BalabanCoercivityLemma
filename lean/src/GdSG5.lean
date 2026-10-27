import GdSG4

/-!
# GdSG5 -- the NV three-stratum slab (ell = 2, a = 1, k = 2): for large `m`, `R` and small `α₀`, every boundary-twist configuration `U_θ` is in class, satisfies the
guard gap `GapAt`, and satisfies the guarded literal inequality.  (So the family used by `D1Literal` for the full-guard literal reading cannot supply the gap
failure that `not_SG_of_gapfail` needs.)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.NonVac
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

theorem SG_on_twist_family_nv (sJ : PlaqSel) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ α₀ : ℝ, 0 < α₀ → (12 : ℝ) * ((2 ^ m : ℕ) : ℝ) * α₀ ≤ a₀ → ∀ θ : ℝ,
        ClassCoupled 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R) α₀ (((2 : ℕ) : ℝ) ^ 2)⁻¹ (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) ∧
        GapAt selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R)
          (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) 1 (LamN (2 ^ m) R)) ∧
        InstIneqSG selAll sJ 2 2 (by norm_num) 1 (nvLu (2 ^ m) R) γ₀ (SlabNv 2 (2 ^ m) R) (LamN (2 ^ m) R)
          (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) := by
  obtain ⟨m₀, hm₀, h⟩ := SG_on_twist_family sJ 2 le_rfl 1 one_pos
  refine ⟨m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR⟩ := h m hm
  refine ⟨max R₀ 18, fun R hR' => ?_⟩
  have hR18 : 18 ≤ R := le_trans (le_max_right _ _) hR'
  obtain ⟨a₀, ha₀, γ₀, hγ, hall⟩ := hR R (le_trans (le_max_left _ _) hR')
  refine ⟨a₀, ha₀, γ₀, hγ, fun α₀ hα hαle θ => ?_⟩
  have hM : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hM2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (le_trans hm₀ hm)
  have hdvd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hell : 2 ≤ 2 := le_rfl
  have hell0 : 0 < 2 := by norm_num
  have G := slabGeo_inst (ell := 2) hell hM hdvd (show 1 ≤ R by omega)
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nv_widths (ell := 2) hell hM hR18
  have hN : ∀ μ, scaleUp 2 2 (nvLu (2 ^ m) R) μ + 1 = nvN 2 (2 ^ m) R := fun μ => scaleUp_nv hell0 hM μ
  have hAdm : Admissible 2 (2 ^ m) R 2 (SlabNv 2 (2 ^ m) R) := slab3_admissible G hN
  have hcov : CoversOm0p 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R) := slab3_coversp G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  have hcls : ClassCoupled 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R) α₀ (((2 : ℕ) : ℝ) ^ 2)⁻¹ (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) :=
    ⟨hcov, perCubeRegular2_of_one_on_om0 _ hAdm.1 hα hM (by norm_num) hell0 (by positivity) _
      (fun e he _ => Uth_in _ _ e he)⟩
  have hthick : ∀ σ : Fin 3, 13 * 2 ^ m ≤ nvLu (2 ^ m) R σ + 1 := by
    intro σ
    rw [nvLu_succ hM]
    nlinarith
  have hineq := hall 2 (by norm_num) (nvLu (2 ^ m) R) α₀ hα (by simpa using hαle) (torusOK_nv hell hdvd hM) hthick
    (SlabNv 2 (2 ^ m) R) hAdm (LamN (2 ^ m) R) (lambdaOK2_nv hell hdvd hM (show 1 ≤ R by omega)) (lam_nonempty hM) θ hcls
  obtain ⟨hB1, hB2, hB3, hB4⟩ := BseedNv_props (R := R) hell hdvd hM
  exact ⟨hcls, gap_of_instIneqSG selAll sJ 2 2 hell0 1 zero_le_one (nvLu (2 ^ m) R) γ₀ hγ (SlabNv 2 (2 ^ m) R)
    (LamN (2 ^ m) R) _ _ hB1 hB2 hB3 hineq, hineq⟩

#print axioms SG_on_twist_family_nv

end AdalyFormal.D1Guarded
