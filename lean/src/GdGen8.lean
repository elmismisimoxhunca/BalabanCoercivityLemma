import GdGen7
import GdSG4

/-!
# GdGen8 -- NV three-stratum slab (ell = 2, a = 1, k = 2): for EVERY in-class configuration `U` (large `m`, `R`, small `α₀`) the guarded literal inequality at `U`
holds iff `IsUnit Ginv → IsUnit G1inv` at `U`.
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
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- a positive-energy admissible test field and the localised inequality force the localised units. -/
theorem WellDefAt_loc_of_inst (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 ≤ a) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ) (hγ : 0 < γ₀)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (Bt : Bond Lu → SuTwo) (h1 : OnLambdaTildeIn Lam ell Bt) (h2 : OnLambdaT Lam Bt) (hE : 0 < bondEnergy Bt)
    (hloc : InstIneqS selIn selIn ell k hell a Lu γ₀ S Lam U) :
    WellDefAt selIn selIn (gparams ell k Lu hell S U a Lam) := by
  by_contra hn
  refine not_InstIneqS_of_collapse selIn selIn ell k hell a ha Lu γ₀ hγ S Lam U (fun B => ?_) Bt h1 h2 hE hloc
  exact genFormS_collapse_of_not_wd selIn selIn (gparams ell k Lu hell S U a Lam) hn B

#print axioms WellDefAt_loc_of_inst

theorem nv_SG_iff_G1inv_unit (sJ : PlaqSel) (hsJ : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ L G) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ α₀ : ℝ, 0 < α₀ → (12 : ℝ) * ((2 ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
        ∀ U : LinkCfg (scaleUp 2 2 (nvLu (2 ^ m) R)),
          ClassCoupled 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R) α₀ (((2 : ℕ) : ℝ) ^ 2)⁻¹ U →
          (InstIneqSG selAll sJ 2 2 (by norm_num) 1 (nvLu (2 ^ m) R) γ₀ (SlabNv 2 (2 ^ m) R) (LamN (2 ^ m) R) U ↔
            (IsUnit (dataS selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R) U 1 (LamN (2 ^ m) R))).Ginv →
              IsUnit (G1invS selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R) U 1 (LamN (2 ^ m) R))))) := by
  obtain ⟨m₀, hm₀, hmm⟩ := (pin_target8_iff.mpr AdalyFormal.M2RightInv.p428Target8 : P428Target8S selIn selIn) 2 le_rfl 1 one_pos
  refine ⟨m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR⟩ := hmm m hm
  refine ⟨max R₀ 18, fun R hR' => ?_⟩
  have hR18 : 18 ≤ R := le_trans (le_max_right _ _) hR'
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hcore⟩ := hR R (le_trans (le_max_left _ _) hR')
  refine ⟨a₀, ha₀, γ₀, hγ, fun α₀ hα hαle U hU => ?_⟩
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
  have hroom : 17 * 2 ≤ R * 2 ^ m := by nlinarith
  have hloc := hcore 2 (by norm_num) (nvLu (2 ^ m) R) α₀ hα (by simpa using hαle) (torusOK_nv hell hdvd hM)
    (SlabNv 2 (2 ^ m) R) hAdm (LamN (2 ^ m) R) (lambdaOK2_nv hell hdvd hM (show 1 ≤ R by omega)) U hU
  obtain ⟨hB1, hB2, hB3, hB4⟩ := BseedNv_props (R := R) hell hdvd hM
  have WD2 := WellDefAt_loc_of_inst 2 2 hell0 1 zero_le_one (nvLu (2 ^ m) R) γ₀ hγ (SlabNv 2 (2 ^ m) R) (LamN (2 ^ m) R) U _ hB1 hB2 hB3 hloc
  constructor
  · intro hSG hu
    exact (gap_of_instIneqSG selAll sJ 2 2 hell0 1 zero_le_one (nvLu (2 ^ m) R) γ₀ hγ (SlabNv 2 (2 ^ m) R)
      (LamN (2 ^ m) R) U _ hB1 hB2 hB3 hSG hu).1
  · intro h
    exact InstIneqSG_general selAll sJ hell0 hAdm (by norm_num) hroom zero_le_one hγ (LamN (2 ^ m) R) U
      (fun _ _ => Set.subset_univ _) hsJ hloc WD2 h

#print axioms nv_SG_iff_G1inv_unit

end AdalyFormal.D1Guarded
