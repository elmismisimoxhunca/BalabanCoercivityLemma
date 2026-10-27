import GdR5a

/-!
# GdR5b -- NON-VACUITY of the guard: `Ginv_lit` is a unit at the flat NV configuration and in a neighbourhood of `θ = 0` on the twist family.

* `isUnit_of_psd_ge`: a symmetric operator that dominates, as a form, a positive semidefinite unit is a unit.
* `Fth_zero_isUnit`: at `θ = 0`, `Ginv_lit ≥ Ginv_loc` (form), `Ginv_loc` is PSD (`Ginv_psd_flat`) and a unit (localised units), hence `Ginv_lit(0)` is a unit.
* `Fth_isUnit_near_zero`: units are open and `θ ↦ Ginv_lit(θ)` is continuous (`Fth_cont`), so `Ginv_lit(θ)` is a unit for `|θ| < δ`.
* `nv_guard_nonvacuous`: on the NV slab, for large `m`, `R` and small `α₀`, there is `δ > 0` such that for every `|θ| < δ` the configuration `U_θ` is in class,
  `Ginv_lit` is a unit, `WellDefAt selAll sJ` holds and the (unguarded) literal inequality `InstIneqS selAll sJ` holds.
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

section generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem isOpen_isUnit_clm : IsOpen {F : E →L[ℝ] E | IsUnit F} := by
  have h := Units.isOpen (R := E →L[ℝ] E)
  exact h

theorem isUnit_of_psd_ge {M₁ M₂ : E →L[ℝ] E} (hs₂ : ∀ x y, ⟪M₂ x, y⟫ = ⟪x, M₂ y⟫) (hp₂ : PSD M₂) (hu₂ : IsUnit M₂)
    (hge : ∀ x, ⟪x, M₂ x⟫ ≤ ⟪x, M₁ x⟫) : IsUnit M₁ := by
  have hinj : Function.Injective M₁ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : ⟪x, M₂ x⟫ ≤ 0 := by have := hge x; rw [hx, inner_zero_right] at this; exact this
    have h0 : ⟪x, M₂ x⟫ = 0 := le_antisymm h1 (hp₂ x)
    have hk : M₂ x = 0 := psd_kernel M₂ hs₂ hp₂ x h0
    exact (injective_iff_map_eq_zero _).mp (ContinuousLinearMap.isUnit_iff_bijective.mp hu₂).1 x hk
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (M₁ : E →ₗ[ℝ] E))).mp hinj⟩

end generic

#print axioms isUnit_of_psd_ge

section flat
variable (sJ : PlaqSel) {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
  {S : Tower (scaleUp ell k Lu)} (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))

theorem Fth_zero_isUnit (ha : 0 ≤ a) (WD2 : WellDefAt selIn selIn (Pth ell k Lu hell0 S a Lam 0)) :
    IsUnit (Fth sJ ell k Lu hell0 S a Lam 0) :=
  isUnit_of_psd_ge ((dataS selIn selIn (Pth ell k Lu hell0 S a Lam 0)).Ginv_symm (dataS_laws selIn selIn _))
    (Ginv_psd_flat hell0 a Lam selIn selIn ha) WD2.1
    (fun w => Ginv_form_mono_flat hell0 a Lam sJ selIn w)

theorem Fth_isUnit_near_zero (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (ha : 0 ≤ a)
    (WD2 : WellDefAt selIn selIn (Pth ell k Lu hell0 S a Lam 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ θ : ℝ, |θ| < δ → IsUnit (Fth sJ ell k Lu hell0 S a Lam θ) := by
  have hc := Fth_cont sJ hell0 a Lam hS hell hroom
  have hopen : IsOpen {F : ↥(bondSupp (geomOf ell k S)) →L[ℝ] ↥(bondSupp (geomOf ell k S)) | IsUnit F} := isOpen_isUnit_clm
  have hpre := hopen.preimage hc
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hpre 0 (Fth_zero_isUnit sJ hell0 a Lam ha WD2)
  refine ⟨δ, hδ, fun θ hθ => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  exact hθ

#print axioms Fth_zero_isUnit
#print axioms Fth_isUnit_near_zero

end flat

theorem nv_guard_nonvacuous (sJ : PlaqSel) (hsJ : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ L G) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ α₀ : ℝ, 0 < α₀ → (12 : ℝ) * ((2 ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ θ : ℝ, |θ| < δ →
          ClassCoupled 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R) α₀ (((2 : ℕ) : ℝ) ^ 2)⁻¹ (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) ∧
          IsUnit (dataS selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R)
            (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) 1 (LamN (2 ^ m) R))).Ginv ∧
          WellDefAt selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R)
            (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) 1 (LamN (2 ^ m) R)) ∧
          InstIneqS selAll sJ 2 2 (by norm_num) 1 (nvLu (2 ^ m) R) γ₀ (SlabNv 2 (2 ^ m) R) (LamN (2 ^ m) R)
            (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) := by
  obtain ⟨m₁, hm₁, hmm⟩ := (pin_target8_iff.mpr AdalyFormal.M2RightInv.p428Target8 : P428Target8S selIn selIn) 2 le_rfl 1 one_pos
  refine ⟨m₁, hm₁, fun m hm => ?_⟩
  obtain ⟨R₂, hR₂⟩ := hmm m hm
  refine ⟨max R₂ 18, fun R hR' => ?_⟩
  have hR18 : 18 ≤ R := le_trans (le_max_right _ _) hR'
  obtain ⟨-, a₂, ha₂, γ₂, hγ₂, hcore⟩ := hR₂ R (le_trans (le_max_left _ _) hR')
  refine ⟨a₂, ha₂, γ₂, hγ₂, fun α₀ hα hαle => ?_⟩
  have hM : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hM2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (le_trans hm₁ hm)
  have hdvd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hell : 2 ≤ 2 := le_rfl
  have hell0 : 0 < 2 := by norm_num
  have G := slabGeo_inst (ell := 2) hell hM hdvd (show 1 ≤ R by omega)
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nv_widths (ell := 2) hell hM hR18
  have hN : ∀ μ, scaleUp 2 2 (nvLu (2 ^ m) R) μ + 1 = nvN 2 (2 ^ m) R := fun μ => scaleUp_nv hell0 hM μ
  have hAdm : Admissible 2 (2 ^ m) R 2 (SlabNv 2 (2 ^ m) R) := slab3_admissible G hN
  have hcov : CoversOm0p 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R) := slab3_coversp G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  have hroom : 17 * 2 ≤ R * 2 ^ m := by nlinarith
  have hcls : ∀ θ : ℝ, ClassCoupled 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R) α₀ (((2 : ℕ) : ℝ) ^ 2)⁻¹ (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) :=
    fun θ => ⟨hcov, perCubeRegular2_of_one_on_om0 _ hAdm.1 hα hM (by norm_num) hell0 (by positivity) _
      (fun e he _ => Uth_in _ _ e he)⟩
  obtain ⟨hB1, hB2, hB3, hB4⟩ := BseedNv_props (R := R) hell hdvd hM
  have hloc : ∀ θ : ℝ, InstIneqS selIn selIn 2 2 hell0 1 (nvLu (2 ^ m) R) γ₂ (SlabNv 2 (2 ^ m) R) (LamN (2 ^ m) R)
      (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) := fun θ =>
    hcore 2 (by norm_num) (nvLu (2 ^ m) R) α₀ hα (by simpa using hαle) (torusOK_nv hell hdvd hM)
      (SlabNv 2 (2 ^ m) R) hAdm (LamN (2 ^ m) R) (lambdaOK2_nv hell hdvd hM (show 1 ≤ R by omega)) _ (hcls θ)
  have hWD2 : ∀ θ : ℝ, WellDefAt selIn selIn (gparams 2 2 (nvLu (2 ^ m) R) hell0 (SlabNv 2 (2 ^ m) R)
      (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) 1 (LamN (2 ^ m) R)) := fun θ =>
    WellDefAt_loc_of_inst 2 2 hell0 1 zero_le_one (nvLu (2 ^ m) R) γ₂ hγ₂ (SlabNv 2 (2 ^ m) R) (LamN (2 ^ m) R) _ _ hB1 hB2 hB3 (hloc θ)
  obtain ⟨δ, hδ, hunit⟩ := Fth_isUnit_near_zero sJ hell0 1 (LamN (2 ^ m) R) hAdm hell hroom zero_le_one (hWD2 0)
  refine ⟨δ, hδ, fun θ hθ => ?_⟩
  have hu : IsUnit (dataS selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) hell0 (SlabNv 2 (2 ^ m) R)
      (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) 1 (LamN (2 ^ m) R))).Ginv := hunit θ hθ
  have h3 : 3 ≤ R * 2 ^ m := by nlinarith
  have hG1 : IsUnit (G1invS selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) hell0 (SlabNv 2 (2 ^ m) R)
      (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) 1 (LamN (2 ^ m) R))) := by
    rw [G1invS_eq_Ginv_theta selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) hell0 (SlabNv 2 (2 ^ m) R)
      (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) 1 (LamN (2 ^ m) R)) hAdm hell0 h3 θ rfl]
    exact hu
  have hgap := GapAt_of_loc (gparams 2 2 (nvLu (2 ^ m) R) hell0 (SlabNv 2 (2 ^ m) R)
      (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) 1 (LamN (2 ^ m) R)) hAdm hell0 hroom selAll sJ
      (fun _ _ => Set.subset_univ _) hsJ (hWD2 θ) (fun _ => hG1)
  exact ⟨hcls θ, hu, ⟨hu, hG1, (hgap hu).2⟩,
    InstIneqSG_general selAll sJ hell0 hAdm (by norm_num) hroom zero_le_one hγ₂ (LamN (2 ^ m) R) _
      (fun _ _ => Set.subset_univ _) hsJ (hloc θ) (hWD2 θ) (fun _ => hG1) hu⟩

#print axioms nv_guard_nonvacuous

end AdalyFormal.D1Guarded
