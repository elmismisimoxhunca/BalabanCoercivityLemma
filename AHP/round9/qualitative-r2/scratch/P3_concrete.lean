
/-! ## The actual operators: canonical vacuum crossings, and the reduced premise

Everything below concerns the actual pinned assemblies of the round-4/5 dilated family.
* Along an analytic exterior path every matrix coefficient of the actual carrier is
  real-analytic in the path parameter (frozen exterior path formula and the analytic
  plaquette chain above), so its non-units are isolated as soon as it is a unit somewhere.
* At the trivial configuration the all-plaquette carrier dominates the localized one, which is
  positive semidefinite, and a unit at every large scale and radius by the FROZEN localized
  theorem `M2RightInv.p428Target8`.  So the vacuum carrier of the exterior twist is positive
  definite at angle `0`; round 5 gives a negative direction at angle `π`.
* Hence at every large scale and radius the vacuum twist has a canonical crossing (the end of
  its initial positive semidefinite interval) with positive definite carriers arbitrarily close
  before it and negative directions arbitrarily close after it, for the twist run forwards
  (`Uth t`) and backwards (`Uth (-t)`).  Round 9.1 assumed this; here it is proved.
* Joint continuity in curvature and angle follows from continuity in the curvature, at the
  untwisted angle, of the carrier and of the dressing `W`.
* The literal round-8 family may use negative angles.  A positive coupling on the backward
  side gives a pre-crossing separation there, so no post-crossing analysis is needed.
What remains unproved is soft regularity of the interior family at the flat interior and a
definite first-order coupling on the canonical vacuum kernel. -/
namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.D1Literal (PSD)

/-! ### Analyticity in the exterior angle -/

/-- An analytic exterior path, a fixed profile and a fixed curvature give an analytic family. -/
theorem pathU_anFam (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) : AnFam (pathU q R V f ε) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [pathU, maskedU, if_pos he]
    exact hV e
  · simp only [pathU, maskedU, if_neg he]
    exact anM_const _

theorem uthPath_anFam (q R : ℕ) : AnFam (uthPath q R) := anFam_Uth _

/-- The frozen exterior twist run backwards. -/
noncomputable def uthPathNeg (q R : ℕ) : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun s => uthPath q R (-s)

theorem uthPathNeg_cont (q R : ℕ) : AdalyFormal.D1Literal.ContFam (uthPathNeg q R) :=
  fun e => (uthPath_cont q R e).comp continuous_neg

theorem uthPathNeg_anFam (q R : ℕ) : AnFam (uthPathNeg q R) := by
  intro e θ₀ i j
  have hn : AnalyticAt ℝ (fun θ : ℝ => -θ) θ₀ := by fun_prop
  exact AnalyticAt.comp (g := fun θ => ((uthPath q R θ e : AdalyFormal.D1Literal.SU2m) :
    Matrix (Fin 2) (Fin 2) ℂ) i j) (uthPath_anFam q R e (-θ₀) i j) hn

theorem uthPath_zero (q R : ℕ) : uthPath q R 0 = fun _ => 1 :=
  AdalyFormal.D1Literal.Uth_zero _

theorem uthPathNeg_zero (q R : ℕ) : uthPathNeg q R 0 = fun _ => 1 := by
  show uthPath q R (-0) = _
  rw [neg_zero]
  exact uthPath_zero q R

/-- Along an analytic exterior path, every matrix coefficient of the actual all-plaquette
carrier is real-analytic in the path parameter. -/
theorem pathA_anR {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ)
    (x y : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    AnR (fun t => ⟪x, pathA q R V f ε a t y⟫) := by
  have h : ∀ t, pathA q R V f ε a t = pathA q R V f ε a 0 +
      (pE (geomOf 2 1 (dilTower q R))).comp (((ContinuousLinearMap.adjoint
        (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε 0) Set.univ)).comp
          (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a))).comp
        (iE (geomOf 2 1 (dilTower q R)))) :=
    fun t => exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      a (dilLam q R) (pathU q R V f ε) (fun s e he => path_agrees q R V f ε s 0 e he) selAll t
  have he : ∀ t, ⟪x, pathA q R V f ε a t y⟫ = ⟪x, pathA q R V f ε a 0 y⟫ +
      (⟪Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a (iE (geomOf 2 1 (dilTower q R)) x),
          AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε t) Set.univ
            (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a
              (iE (geomOf 2 1 (dilTower q R)) y))⟫ -
        ⟪Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a (iE (geomOf 2 1 (dilTower q R)) x),
          AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε 0) Set.univ
            (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a
              (iE (geomOf 2 1 (dilTower q R)) y))⟫) := by
    intro t
    rw [h t]
    simp only [add_apply, ContinuousLinearMap.comp_apply, inner_add_right, pE_inner_right,
      ContinuousLinearMap.adjoint_inner_right, sub_apply, inner_sub_right]
  rw [funext he]
  exact (anR_const _).add
    ((an_inner_delta (pathU_anFam q R hV f ε) Set.univ _ _).sub (anR_const _))

/-- Isolated non-units along an analytic exterior path, at every curvature and profile. -/
theorem pathA_isolated {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ) {t₀ : ℝ}
    (hu : IsUnit (pathA q R V f ε a t₀)) (t : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (pathA q R V f ε a s) :=
  isUnit_punctured (fun x y θ₀ => pathA_anR hq hR hroom hV f ε a x y θ₀) hu t

/-- The corrected carrier along an analytic exterior path also has isolated non-units (the
correction does not depend on the exterior). -/
theorem pathC_isolated {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ) {t₀ : ℝ}
    (hu : IsUnit (pathA q R V f ε a t₀ - pathD q R V f ε a t₀)) (t : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η →
      IsUnit (pathA q R V f ε a s - pathD q R V f ε a s) := by
  have hD : ∀ s, pathD q R V f ε a s = pathD q R V f ε a 0 :=
    fun s => pathD_constant hq hR hroom V f ε a s
  have hu' : IsUnit (pathA q R V f ε a t₀ - pathD q R V f ε a 0) := by rw [← hD t₀]; exact hu
  obtain ⟨η, hη, hb⟩ := isUnit_punctured (A := fun s => pathA q R V f ε a s - pathD q R V f ε a 0)
    (fun x y θ₀ => by
      have e : (fun θ => ⟪x, (pathA q R V f ε a θ - pathD q R V f ε a 0) y⟫) =
          fun θ => ⟪x, pathA q R V f ε a θ y⟫ - ⟪x, pathD q R V f ε a 0 y⟫ := by
        funext θ; rw [sub_apply, inner_sub_right]
      rw [e]
      exact (pathA_anR hq hR hroom hV f ε a x y θ₀).fun_sub analyticAt_const) hu' t
  exact ⟨η, hη, fun s hs hst => by rw [hD s]; exact hb s hs hst⟩

/-! ### The vacuum carrier at angle zero is positive definite -/

theorem inner_Ginv_dataS (sD sJ : PlaqSel) (P : IngrBParams) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS sD sJ P).Ginv x⟫ =
      ⟪Wop P.G P.U P.a (iE P.G x), AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (sD _ P.G)
        (Wop P.G P.U P.a (iE P.G x))⟫ + ‖(dataS sD sJ P).T x‖ ^ 2 +
      ⟪x, (dataS sD sJ P).Mass x⟫ := by
  have hD : ⟪x, (dataS sD sJ P).Dpi x⟫ = ⟪Wop P.G P.U P.a (iE P.G x),
      AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (sD _ P.G) (Wop P.G P.U P.a (iE P.G x))⟫ := by
    show ⟪x, ((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) x⟫ = _
    simp only [ContinuousLinearMap.comp_apply, DpiFullS, DeltaS]
    rw [pE_inner_right, ContinuousLinearMap.adjoint_inner_right]
  rw [BaseDataS.inner_Ginv, hD]

/-- At the trivial background the plaquette Hessian is monotone in the plaquette set. -/
theorem flat_delta_le_univ {L : PeriodicLatticeExtent} (P : Set (PeriodicLatticePlaquette L))
    (y : BondFnL2 L) :
    ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM (fun _ => 1) P y⟫ ≤
      ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM (fun _ => 1) Set.univ y⟫ := by
  have h1 : AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) P y y = 0 :=
    AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc_trivialU P _ _
  have h2 : AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) Set.univ y y = 0 :=
    AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc_trivialU Set.univ _ _
  change ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) P y⟫ ≤
    ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) Set.univ y⟫
  rw [AdalyFormal.StatementLaneR6.inner_deltaKLocCLM,
    AdalyFormal.StatementLaneR6.inner_deltaKLocCLM, h1, h2, add_zero, add_zero,
    AdalyFormal.StatementLaneR6.plaqMask_univ]
  simp only [PiLp.inner_apply, AdalyFormal.StatementLaneR6.plaqMask_apply]
  refine Finset.sum_le_sum (fun p _ => ?_)
  by_cases hp : p ∈ P
  · simp only [hp, if_true, le_refl]
  · simp only [hp, if_false, inner_zero_left]
    exact real_inner_self_nonneg

theorem mass_nonneg_dataS (sD sJ : PlaqSel) (P : IngrBParams) (ha : 0 ≤ P.a)
    (x : ↥(bondSupp P.G)) : 0 ≤ ⟪x, (dataS sD sJ P).Mass x⟫ := by
  show 0 ≤ ⟪x, ((pE P.G).comp ((MassFull P.G P.a P.sector).comp (iE P.G))) x⟫
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, pE_inner_right,
    inner_MassFull]
  refine Finset.sum_nonneg (fun p _ => ?_)
  have h1 : (0 : ℝ) ≤ (P.G.ell : ℝ) ^ (p.1 : ℕ) := pow_nonneg (Nat.cast_nonneg _) _
  exact mul_nonneg (mul_nonneg ha h1) (sq_nonneg _)

/-- At the trivial background the localized carrier is positive semidefinite. -/
theorem Ginv_loc_psd_flat (P : IngrBParams) (hU : P.U = fun _ => 1) (ha : 0 ≤ P.a) :
    PSD (dataS selIn selIn P).Ginv := by
  intro x
  rw [inner_Ginv_dataS]
  have h1 : 0 ≤ ⟪Wop P.G P.U P.a (iE P.G x), AdalyFormal.StatementLaneR6.deltaKLocCLM P.U
      (selIn _ P.G) (Wop P.G P.U P.a (iE P.G x))⟫ := by
    generalize Wop P.G P.U P.a (iE P.G x) = y
    rw [hU]
    exact AdalyFormal.StatementLaneR6.deltaKLocCLM_flat_nonneg _ y
  have h2 := mass_nonneg_dataS selIn selIn P ha x
  have h3 := sq_nonneg ‖(dataS selIn selIn P).T x‖
  linarith

/-- At the trivial background the all-plaquette carrier dominates the localized one. -/
theorem Ginv_loc_le_all_flat (P : IngrBParams) (hU : P.U = fun _ => 1)
    (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selIn selIn P).Ginv x⟫ ≤ ⟪x, (dataS selAll selAll P).Ginv x⟫ := by
  rw [inner_Ginv_dataS, inner_Ginv_dataS]
  have hT : (dataS selIn selIn P).T = (dataS selAll selAll P).T := rfl
  have hM : (dataS selIn selIn P).Mass = (dataS selAll selAll P).Mass := rfl
  rw [hT, hM]
  have key : ∀ y, ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (selIn _ P.G) y⟫ ≤
      ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (selAll _ P.G) y⟫ := by
    intro y
    rw [hU]
    exact flat_delta_le_univ _ y
  linarith [key (Wop P.G P.U P.a (iE P.G x))]

/-- A unit localized carrier at the trivial background makes the all-plaquette carrier
positive definite. -/
theorem Ginv_all_pd_flat (P : IngrBParams) (hU : P.U = fun _ => 1) (ha : 0 ≤ P.a)
    (hu : IsUnit (dataS selIn selIn P).Ginv) :
    ∀ x, x ≠ 0 → 0 < ⟪x, (dataS selAll selAll P).Ginv x⟫ := by
  intro x hx
  have h1 := pos_of_psd_unit _ ((dataS selIn selIn P).Ginv_symm (dataS_laws selIn selIn P))
    (Ginv_loc_psd_flat P hU ha) hu x hx
  exact lt_of_lt_of_le h1 (Ginv_loc_le_all_flat P hU x)

/-- The trivial configuration of the dilated geometry, mass `1`. -/
noncomputable def flatP (q R : ℕ) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R)

theorem dilU_flat (q R : ℕ) : dilU q R 0 (fun _ => 1) = fun _ => 1 := by
  classical
  funext e
  simp only [dilU, ite_self, Ug_zero]

/-- **The frozen localized theorem at the trivial configuration.**  At every large scale and
every large even radius the localized carrier of the trivial configuration is a unit
(`M2RightInv.p428Target8`, through the instance inequality and `WellDefAt_loc_of_inst`). -/
theorem flat_loc_unit_eventually :
    ∃ j₁ : ℕ, ∀ j : ℕ, j₁ ≤ j → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → 2 ∣ R → 18 ≤ R →
      IsUnit (dataS selIn selIn (flatP (2^j) R)).Ginv := by
  obtain ⟨m₂, -, hmm⟩ := (AdalyFormal.D1Literal.pin_target8_iff.mpr
    AdalyFormal.M2RightInv.p428Target8 : AdalyFormal.D1Literal.P428Target8S
      AdalyFormal.D1Literal.selIn AdalyFormal.D1Literal.selIn) 2 le_rfl 1 one_pos
  refine ⟨m₂, fun j hj => ?_⟩
  obtain ⟨R₂, hR₂⟩ := hmm (j+1) (by omega)
  refine ⟨R₂, fun R hR hR2 hR18 => ?_⟩
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hcore⟩ := hR₂ R hR
  let q := 2^j
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(j+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let α : ℝ := min (a₀/(24*q)) 1/2
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ) * ((2^(j+1) : ℕ) : ℝ) * α ≤ a₀ := by
    have hm : α ≤ a₀/(24*q) := by
      have hp : 0 < min (a₀/(24*q)) 1 := by positivity
      dsimp [α]; linarith [min_le_left (a₀/(24*q)) 1]
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 24*q)).mp hm
    rw [hpow]; push_cast; nlinarith
  have hT : TorusOK 2 (2^(j+1)) (dilLu q R) := by rw [hpow]; exact dil_torus hq R
  have hS : Admissible 2 (2^(j+1)) R 1 (dilTower q R) := by
    rw [hpow]; exact dil_admissible hq hR2
  have hL : LambdaOK2 2 (2^(j+1)) R 1 (dilTower q R) (dilLam q R) := by
    rw [hpow]; exact dil_lambda hq hR2
  have hreg := dil_regular hq hR2 hα (ε := 0) (by rw [abs_zero]; positivity) (fun _ => 1)
  rw [dilU_flat] at hreg
  have hcl : ClassCoupled 2 (2^(j+1)) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (fun _ => 1) := by
    rw [hpow]; exact ⟨dil_coverage hq hR2 (by omega), hreg⟩
  have hloc := hcore 1 le_rfl (dilLu q R) α hα hcap hT (dilTower q R) hS (dilLam q R) hL _ hcl
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR2
  exact (AdalyFormal.D1Guarded.WellDefAt_loc_of_inst 2 1 (by norm_num) 1 zero_le_one
    (dilLu q R) γ₀ hγ (dilTower q R) (dilLam q R) _ (dilBt hq R) hBt1 hBt2 hE hloc).1

theorem pathU_flat_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    pathU q R V f 0 0 = fun _ => 1 := by
  classical
  funext e
  simp only [pathU, maskedU, hV0, zero_mul, Ug_zero, ite_self]

theorem vacA_zero_flat (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) : vacA q R V 1 0 = (dataS selAll selAll (flatP q R)).Ginv := by
  unfold vacA pathA pathP flatP
  rw [pathU_flat_base q R hV0 (fun _ => 0)]

/-- The vacuum carrier is positive definite at the base point of an exterior path that starts
at the trivial field, as soon as the localized carrier of the trivial configuration is a
unit. -/
theorem vacA_pd_zero {q R : ℕ} {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv) :
    ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 0 x⟫ := by
  rw [vacA_zero_flat q R hV0]
  exact Ginv_all_pd_flat (flatP q R) rfl zero_le_one hloc

/-! ### Negative endpoints and the canonical crossing -/

theorem vacA_uth_pi_negative {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q)) :
    ∃ w, ⟪w, vacA q R (uthPath q R) 1 Real.pi w⟫ < 0 := by
  obtain ⟨w, hw⟩ := twistA_pi_negative hq hR hroom 0
  refine ⟨w, ?_⟩
  rw [twistA_eq_path, pathA_zero] at hw
  exact hw

theorem uθ_neg_pi : AdalyFormal.D1Literal.uθ (-Real.pi) = AdalyFormal.D1Literal.uθ Real.pi := by
  apply Subtype.ext
  show AdalyFormal.D1Literal.uMat (-Real.pi) = AdalyFormal.D1Literal.uMat Real.pi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Complex.exp_neg, Complex.exp_pi_mul_I]

theorem uthPath_neg_pi (q R : ℕ) : uthPath q R (-Real.pi) = uthPath q R Real.pi := by
  funext e
  simp only [uthPath, AdalyFormal.D1Literal.Uth, uθ_neg_pi]

theorem vacA_uthNeg_pi_negative {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) : ∃ w, ⟪w, vacA q R (uthPathNeg q R) 1 Real.pi w⟫ < 0 := by
  obtain ⟨w, hw⟩ := vacA_uth_pi_negative hq hR hroom
  refine ⟨w, ?_⟩
  have hU : pathU q R (uthPathNeg q R) (fun _ => 0) 0 Real.pi =
      pathU q R (uthPath q R) (fun _ => 0) 0 Real.pi := by
    show maskedU q R _ (uthPath q R (-Real.pi)) = maskedU q R _ (uthPath q R Real.pi)
    rw [uthPath_neg_pi]
  have h : vacA q R (uthPathNeg q R) 1 Real.pi = vacA q R (uthPath q R) 1 Real.pi := by
    unfold vacA pathA pathP
    rw [hU]
  rw [h]
  exact hw

/-- The canonical crossing angle of the vacuum carrier along an exterior path: the end of its
initial positive semidefinite interval in `[0, π]`. -/
noncomputable def vacEdge (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : ℝ :=
  psdEdge (vacA q R V 1) 0 Real.pi

/-- The vacuum carrier along `V` crosses at `ts`: it is positive semidefinite and singular
there, positive definite at angles arbitrarily close before `ts`, and has a negative
direction at angles arbitrarily close after `ts`. -/
def VacuumCrossesAt (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (ts : ℝ) : Prop :=
  0 < ts ∧ ts < Real.pi ∧ PSD (vacA q R V 1 ts) ∧ ¬ IsUnit (vacA q R V 1 ts) ∧
    (∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 t₀ x⟫) ∧
    (∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w, ⟪w, vacA q R V 1 t₁ w⟫ < 0)

/-- **The canonical vacuum crossing.**  Along a continuous, analytic exterior path whose vacuum
carrier is positive definite at `0` and has a negative direction at `π`, the vacuum carrier
crosses at `vacEdge`. -/
theorem vacuum_crossing {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hVc : AdalyFormal.D1Literal.ContFam V)
    (hVa : AnFam V) (hpd0 : ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 0 x⟫)
    (hneg : ∃ w, ⟪w, vacA q R V 1 Real.pi w⟫ < 0) :
    VacuumCrossesAt q R V (vacEdge q R V) := by
  obtain ⟨w, hw⟩ := hneg
  have hc : Continuous (vacA q R V 1) := pathA_continuous hq hR hroom hVc (fun _ => 0) 0 1
  have hs : ∀ t x y, ⟪vacA q R V 1 t x, y⟫ = ⟪x, vacA q R V 1 t y⟫ := by
    intro t x y
    exact (dataS selAll selAll (pathP q R V (fun _ => 0) 0 1 t)).Ginv_symm
      (dataS_laws selAll selAll _) x y
  have hiso : ∀ t, ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (vacA q R V 1 s) :=
    fun t => pathA_isolated hq hR hroom hVa (fun _ => 0) 0 1 (t₀ := 0) (unit_of_pd _ hpd0) t
  obtain ⟨h1, h2, h3, h4, -, h6, h7⟩ :=
    psdEdge_spec (vacA q R V 1) hc hs Real.pi_pos hpd0 w hw hiso
  exact ⟨h1, h2, h3, h4, h6, h7⟩

/-- **Unconditional.**  At every large scale and every large even radius the vacuum carrier of
the actual exterior twist crosses at its canonical angle, forwards and backwards. -/
theorem twist_vacuum_crossing :
    ∃ j₁ : ℕ, ∀ j : ℕ, j₁ ≤ j → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → 2 ∣ R → 18 ≤ R →
      VacuumCrossesAt (2^j) R (uthPath (2^j) R) (vacEdge (2^j) R (uthPath (2^j) R)) ∧
      VacuumCrossesAt (2^j) R (uthPathNeg (2^j) R) (vacEdge (2^j) R (uthPathNeg (2^j) R)) := by
  obtain ⟨j₁, hj₁⟩ := flat_loc_unit_eventually
  refine ⟨j₁, fun j hj => ?_⟩
  obtain ⟨R₁, hR₁⟩ := hj₁ j hj
  refine ⟨R₁, fun R hR hR2 hR18 => ?_⟩
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  have hloc := hR₁ R hR hR2 hR18
  exact ⟨vacuum_crossing hq hR2 hroom (uthPath_cont _ _) (uthPath_anFam _ _)
      (vacA_pd_zero (uthPath_zero _ _) hloc) (vacA_uth_pi_negative hq hR2 hroom),
    vacuum_crossing hq hR2 hroom (uthPathNeg_cont _ _) (uthPathNeg_anFam _ _)
      (vacA_pd_zero (uthPathNeg_zero _ _) hloc) (vacA_uthNeg_pi_negative hq hR2 hroom)⟩

/-- **Unconditional.**  At every curvature the non-units of the actual curved twist, and of its
corrected carrier, are isolated in the angle once the respective carrier is a unit somewhere. -/
theorem twist_isolated_nonunits {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    (ε : ℝ) :
    ((∃ t₀, IsUnit (twistA q R ε 1 t₀)) → ∀ t, ∃ η : ℝ, 0 < η ∧
      ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (twistA q R ε 1 s)) ∧
    ((∃ t₀, IsUnit (twistA q R ε 1 t₀ - twistD q R ε 1 t₀)) → ∀ t, ∃ η : ℝ, 0 < η ∧
      ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (twistA q R ε 1 s - twistD q R ε 1 s)) := by
  constructor
  · rintro ⟨t₀, hu⟩ t
    rw [twistA_eq_path] at hu
    obtain ⟨η, hη, hb⟩ := pathA_isolated hq hR hroom (uthPath_anFam q R) (dilMask q R) ε 1 hu t
    exact ⟨η, hη, fun s hs hst => by rw [twistA_eq_path]; exact hb s hs hst⟩
  · rintro ⟨t₀, hu⟩ t
    rw [twistA_eq_path, twistD_eq_path] at hu
    obtain ⟨η, hη, hb⟩ := pathC_isolated hq hR hroom (uthPath_anFam q R) (dilMask q R) ε 1 hu t
    exact ⟨η, hη, fun s hs hst => by rw [twistA_eq_path, twistD_eq_path]; exact hb s hs hst⟩

/-! ### Joint continuity from interior continuity -/

theorem uMat_continuous' : Continuous fun θ : ℝ => AdalyFormal.D1Literal.uMat θ := by
  unfold AdalyFormal.D1Literal.uMat
  refine continuous_matrix (fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- The abelian link `Ug t = exp(i t σ₃)` is `diag(e^{it}, e^{-it})`. -/
theorem Ug_coe_uMat (t : ℝ) :
    ((Ug t : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      AdalyFormal.D1Literal.uMat t := by
  show NormedSpace.exp (Xm t) = _
  have hX : Xm t = Matrix.diagonal ![(t : ℂ) * Complex.I, -((t : ℂ) * Complex.I)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Xm, sig, Matrix.diagonal]
  rw [hX, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.diagonal, ← Complex.exp_eq_exp_ℂ]

/-- Path families are jointly continuous in (curvature, path parameter), link by link. -/
theorem pathU_contFamY (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContFamY (fun p : ℝ × ℝ => pathU q R V f p.1 p.2) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [pathU, maskedU, if_pos he]
    exact (hV e).comp continuous_snd
  · simp only [pathU, maskedU, if_neg he, Ug_coe_uMat]
    exact uMat_continuous'.comp (continuous_fst.mul continuous_const)

/-- Joint continuity of the carrier in (curvature, angle) at zero curvature, from continuity in
the curvature of the carrier at the path's base point and of the dressing `W` there. -/
theorem pathA_jointly_continuousAt {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (hA0 : ContinuousAt (fun ε : ℝ => pathA q R V f ε 1 0) 0)
    (hW0 : ContinuousAt (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) 1) 0)
    (t : ℝ) : ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) (0, t) := by
  let G := geomOf 2 1 (dilTower q R)
  let Wf : ℝ → BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ] BondFnL2 (scaleUp 2 1 (dilLu q R)) :=
    fun ε => Wop G (pathU q R V f ε 0) 1
  let Δf : ℝ × ℝ → BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ] BondFnL2 (scaleUp 2 1 (dilLu q R)) :=
    fun p => AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f p.1 p.2) Set.univ
  have hpath : ∀ p : ℝ × ℝ, pathA q R V f p.1 1 p.2 = pathA q R V f p.1 1 0 +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wf p.1)).comp
        ((Δf p - Δf (p.1, 0)).comp (Wf p.1))).comp (iE G)) := fun p =>
    exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      1 (dilLam q R) (pathU q R V f p.1) (fun s e he => path_agrees q R V f p.1 s 0 e he)
      selAll p.2
  rw [show (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) = fun p => pathA q R V f p.1 1 0 +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wf p.1)).comp
        ((Δf p - Δf (p.1, 0)).comp (Wf p.1))).comp (iE G)) from funext hpath]
  have hΔ : Continuous Δf := contY_deltaKLocCLM (pathU_contFamY q R hV f) _
  have hA : ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 0) (0, t) :=
    ContinuousAt.comp (f := Prod.fst) (x := ((0 : ℝ), t)) hA0 continuousAt_fst
  have hW : ContinuousAt (fun p : ℝ × ℝ => Wf p.1) (0, t) :=
    ContinuousAt.comp (f := Prod.fst) (x := ((0 : ℝ), t)) hW0 continuousAt_fst
  have hadj : Continuous (fun M : BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R)) => ContinuousLinearMap.adjoint M) :=
    (ContinuousLinearMap.adjoint : (BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R))) ≃ₗᵢ⋆[ℝ] (BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R)))).continuous
  have hWa : ContinuousAt (fun p : ℝ × ℝ => ContinuousLinearMap.adjoint (Wf p.1)) (0, t) :=
    hadj.continuousAt.comp hW
  have hD : ContinuousAt (fun p : ℝ × ℝ => Δf p - Δf (p.1, 0)) (0, t) :=
    hΔ.continuousAt.sub ((hΔ.comp (continuous_fst.prodMk continuous_const)).continuousAt)
  have hmid : ContinuousAt (fun p : ℝ × ℝ => (ContinuousLinearMap.adjoint (Wf p.1)).comp
      ((Δf p - Δf (p.1, 0)).comp (Wf p.1))) (0, t) := hWa.clm_comp (hD.clm_comp hW)
  have hout : Continuous fun M : BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R)) => (pE G).comp (M.comp (iE G)) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  exact hA.add (hout.continuousAt.comp hmid)

/-! ### The reduced premise: soft regularity of the interior family and the coupling -/

/-- The curved interior with the trivial exterior field. -/
noncomputable def bulkU (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  maskedU q R (fun e => ε * f e) (fun _ => 1)

noncomputable def bulkP (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)

/-- The actual all-plaquette carrier of the interior family. -/
noncomputable def bulkA (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selAll selAll (bulkP q R f ε)).Ginv

/-- The actual localized correction of the interior family. -/
noncomputable def bulkD (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selIn selIn (bulkP q R f ε)).Delta2 (dataS_laws selIn selIn _)

/-- **Soft regularity of the interior family** `ε ↦ maskedU (ε f) 1` (curved interior, trivial
exterior) at the flat interior: the carrier and the dressing `W` are continuous at `ε = 0`
and the correction has derivative `De` there.  No exterior angle appears.  NOT proved here. -/
def InteriorSoft (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ContinuousAt (fun ε : ℝ => bulkA q R f ε) 0 ∧
  ContinuousAt (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (bulkU q R f ε) 1) 0 ∧
  HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0

theorem pathU_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    pathU q R V f ε 0 = bulkU q R f ε := by
  unfold pathU bulkU
  rw [hV0]

theorem pathP_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    pathP q R V f ε 1 0 = bulkP q R f ε := by
  unfold pathP bulkP
  rw [pathU_base q R hV0 f ε]

theorem pathA_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    pathA q R V f ε 1 0 = bulkA q R f ε := by
  unfold pathA pathP bulkA bulkP
  rw [pathU_base q R hV0 f ε]

theorem pathD_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    pathD q R V f ε 1 0 = bulkD q R f ε := by
  have hd : dataS selIn selIn (pathP q R V f ε 1 0) = dataS selIn selIn (bulkP q R f ε) := by
    unfold pathP bulkP
    rw [pathU_base q R hV0 f ε]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

theorem joint_of_soft {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hVc : AdalyFormal.D1Literal.ContFam V)
    (hV0 : V 0 = fun _ => 1) {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) (t : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) (0, t) := by
  obtain ⟨hA, hW, -⟩ := hs
  refine pathA_jointly_continuousAt hq hR hroom hVc f ?_ ?_ t
  · rw [show (fun ε : ℝ => pathA q R V f ε 1 0) = fun ε => bulkA q R f ε
      from funext (pathA_base q R hV0 f)]
    exact hA
  · rw [show (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) 1) =
        fun ε => Wop (geomOf 2 1 (dilTower q R)) (bulkU q R f ε) 1
      from funext (fun ε => by rw [pathU_base q R hV0 f ε])]
    exact hW

theorem deriv_of_soft {q R : ℕ} {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) : HasDerivAt (fun ε : ℝ => pathD q R V f ε 1 0) De 0 := by
  rw [show (fun ε : ℝ => pathD q R V f ε 1 0) = fun ε => bulkD q R f ε
    from funext (pathD_base q R hV0 f)]
  exact hs.2.2

/-- The first-order coefficient is definite, of either sign, on the kernel of the vacuum carrier
at the canonical crossing of `V`.  NOT proved here. -/
def CanonicalCoupling (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ((∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) ∨
      (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫))

/-- The first-order coefficient is positive definite on the kernel of the vacuum carrier at the
canonical crossing of `V`.  NOT proved here. -/
def CanonicalCouplingPos (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫

/-- Soft regularity and a definite coupling give round 9.1's `VacuumCoupling`; the vacuum
crossing clauses are now theorems. -/
theorem vacuumCoupling_of_soft {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hVc : AdalyFormal.D1Literal.ContFam V)
    (hVa : AnFam V) (hV0 : V 0 = fun _ => 1)
    (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv)
    (hneg : ∃ w, ⟪w, vacA q R V 1 Real.pi w⟫ < 0)
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) (hc : CanonicalCoupling q R V De) : VacuumCoupling q R V f := by
  obtain ⟨-, -, -, -, hbef, haft⟩ :=
    vacuum_crossing hq hR hroom hVc hVa (vacA_pd_zero hV0 hloc) hneg
  obtain ⟨c, hc0, hsign⟩ := hc
  exact ⟨vacEdge q R V, c, De, hbef, haft,
    ⟨1, one_pos, fun t _ => joint_of_soft hq hR hroom hVc hV0 hs t⟩,
    deriv_of_soft hV0 hs, hc0, hsign⟩

/-- Pre-crossing separation at every small curvature from soft regularity and a positive
coupling at the canonical crossing (the profile itself, no reflection). -/
theorem pathSeparation_eventually_of_soft {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hVc : AdalyFormal.D1Literal.ContFam V) (hVa : AnFam V) (hV0 : V 0 = fun _ => 1)
    (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv)
    (hneg : ∃ w, ⟪w, vacA q R V 1 Real.pi w⟫ < 0)
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) (hc : CanonicalCouplingPos q R V De) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSeparation q R V f ε := by
  obtain ⟨-, -, -, -, hbef, haft⟩ :=
    vacuum_crossing hq hR hroom hVc hVa (vacA_pd_zero hV0 hloc) hneg
  obtain ⟨c, hc0, hpos⟩ := hc
  have h3 : 3 ≤ R * (2*q) := by omega
  have hj : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - vacEdge q R V| < η₀ → ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ ∀ ε s : ℝ, |ε| < r → |s - t| < r →
        ‖pathA q R V f ε 1 s - pathA q R V f 0 1 t‖ < δ :=
    ⟨1, one_pos, fun t _ => metric_of_continuousAt (fun ε t => pathA q R V f ε 1 t) t
      (joint_of_soft hq hR hroom hVc hV0 hs t)⟩
  have hDx := expansion_of_hasDerivAt (fun ε => pathD q R V f ε 1 0) De
    (pathD_zero hq hR h3 V f 1 0) (deriv_of_soft hV0 hs)
  refine eventually_pathSeparation_pos hq hR hroom hVc f (vacEdge q R V) c De hbef haft hj ?_
    hc0 hpos
  intro μ hμ
  obtain ⟨r, hr, hb⟩ := hDx μ hμ
  refine ⟨r, hr, fun ε hε hεr => ?_⟩
  have h1 := hb ε (by rw [abs_of_pos hε]; exact hεr)
  rw [abs_of_pos hε] at h1
  exact h1

theorem twistSeparation_of_uth {q R : ℕ} {ε : ℝ}
    (h : PathSeparation q R (uthPath q R) (dilMask q R) ε) : TwistSeparation q R ε := by
  obtain ⟨t, hu, hnu⟩ := h
  refine ⟨t, ?_, ?_⟩
  · rw [twistA_eq_path]; exact hu
  · rw [twistA_eq_path, twistD_eq_path]; exact hnu

/-- A separation of the backward twist is a separation of the literal family at a negative
angle. -/
theorem twistSeparation_of_uthNeg {q R : ℕ} {ε : ℝ}
    (h : PathSeparation q R (uthPathNeg q R) (dilMask q R) ε) : TwistSeparation q R ε := by
  obtain ⟨s, hu, hnu⟩ := h
  refine ⟨-s, ?_, ?_⟩
  · rw [twistA_eq_path]; exact hu
  · rw [twistA_eq_path, twistD_eq_path]; exact hnu

/-! ### The literal round-8 target -/

/-- **The remaining premise for the literal round-8 family at `(q,R)`.**  Soft regularity of
the single-defect interior family at the flat interior, and a positive first-order coupling on
the kernel of the vacuum carrier at the canonical crossing of the twist run forwards OR run
backwards.  NOT proved here. -/
def TwistSoftCoupling (q R : ℕ) : Prop :=
  ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
    InteriorSoft q R (dilMask q R) De ∧
      (CanonicalCouplingPos q R (uthPath q R) De ∨ CanonicalCouplingPos q R (uthPathNeg q R) De)

theorem twistSeparation_eventually {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv) (h : TwistSoftCoupling q R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → TwistSeparation q R ε := by
  have hroom : 17*2 ≤ R*(2*q) := by nlinarith
  obtain ⟨De, hs, hc | hc⟩ := h
  · obtain ⟨ε₀, hε₀, hall⟩ := pathSeparation_eventually_of_soft hq hR hroom (uthPath_cont q R)
      (uthPath_anFam q R) (uthPath_zero q R) hloc (vacA_uth_pi_negative hq hR hroom) hs hc
    exact ⟨ε₀, hε₀, fun ε h1 h2 => twistSeparation_of_uth (hall ε h1 h2)⟩
  · obtain ⟨ε₀, hε₀, hall⟩ := pathSeparation_eventually_of_soft hq hR hroom
      (uthPathNeg_cont q R) (uthPathNeg_anFam q R) (uthPathNeg_zero q R) hloc
      (vacA_uthNeg_pi_negative hq hR hroom) hs hc
    exact ⟨ε₀, hε₀, fun ε h1 h2 => twistSeparation_of_uthNeg (hall ε h1 h2)⟩

/-- The cofinal form of the reduced premise, with the pinned quantifiers. -/
def CofinalTwistSoftCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    TwistSoftCoupling (2^j) R

/-- **Main reduction (literal target).**  The reduced premise implies round 8's
`CofinalTwistSeparation`.  The vacuum crossing, the joint continuity in curvature and angle
and the sign of the separation side are theorems; the premise keeps only interior soft
regularity and a positive coupling on one of the two canonical vacuum kernels. -/
theorem cofinalTwistSeparation_of_cofinalTwistSoftCoupling (h : CofinalTwistSoftCoupling) :
    CofinalTwistSeparation := by
  obtain ⟨j₁, hj₁⟩ := flat_loc_unit_eventually
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h (max j₀ j₁)
  obtain ⟨R₁, hR₁⟩ := hj₁ j (le_trans (le_max_right _ _) hj)
  refine ⟨j, le_trans (le_max_left _ _) hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hsc⟩ := hRs (max R₀ R₁)
  refine ⟨R, le_trans (le_max_left _ _) hRR, hR, hR18, fun δ hδ => ?_⟩
  have hq : 0 < 2^j := by positivity
  obtain ⟨ε₀, hε₀, hall⟩ := twistSeparation_eventually hq hR hR18
    (hR₁ R (le_trans (le_max_right _ _) hRR) hR hR18) hsc
  have hm : 0 < min δ ε₀ := lt_min hδ hε₀
  exact ⟨min δ ε₀ / 2, by positivity, by linarith [min_le_left δ ε₀],
    hall (min δ ε₀ / 2) (by positivity) (by linarith [min_le_right δ ε₀])⟩

theorem goalNeg2_of_cofinalTwistSoftCoupling (h : CofinalTwistSoftCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_cofinalTwistSoftCoupling h)

theorem not_cofinalTwistSoftCoupling_of_goalPos1 (h : GoalPos1) : ¬ CofinalTwistSoftCoupling :=
  fun h' => goalNeg2_of_cofinalTwistSoftCoupling h' (goalPos2_iff_goalPos1.mpr h)

/-! ### Free profile, either sign -/

/-- **The weakest premise of this round at `(q,R)`.**  Some bounded interior profile whose
interior family is softly regular, with a definite first-order coupling (of either sign) on
the canonical vacuum kernel of the twist run forwards or backwards.  NOT proved here. -/
def PathSoftCoupling (q R : ℕ) : Prop :=
  ∃ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
    ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      InteriorSoft q R f De ∧
        (CanonicalCoupling q R (uthPath q R) De ∨ CanonicalCoupling q R (uthPathNeg q R) De)

def CofinalPathSoftCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    PathSoftCoupling (2^j) R

theorem pathSoftCoupling_of_twist {q R : ℕ} (h : TwistSoftCoupling q R) : PathSoftCoupling q R := by
  obtain ⟨De, hs, hc | hc⟩ := h
  · obtain ⟨c, hc0, hpos⟩ := hc
    exact ⟨dilMask q R, dilMask_bound q R, De, hs, Or.inl ⟨c, hc0, Or.inl hpos⟩⟩
  · obtain ⟨c, hc0, hpos⟩ := hc
    exact ⟨dilMask q R, dilMask_bound q R, De, hs, Or.inr ⟨c, hc0, Or.inl hpos⟩⟩

theorem cofinalPathSoftCoupling_of_twist (h : CofinalTwistSoftCoupling) :
    CofinalPathSoftCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, pathSoftCoupling_of_twist hv⟩

theorem cofinalVacuumCoupling_of_cofinalPathSoftCoupling (h : CofinalPathSoftCoupling) :
    CofinalVacuumCoupling := by
  obtain ⟨j₁, hj₁⟩ := flat_loc_unit_eventually
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h (max j₀ j₁)
  obtain ⟨R₁, hR₁⟩ := hj₁ j (le_trans (le_max_right _ _) hj)
  refine ⟨j, le_trans (le_max_left _ _) hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, f, hf, De, hs, hc⟩ := hRs (max R₀ R₁)
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  have hloc := hR₁ R (le_trans (le_max_right _ _) hRR) hR hR18
  rcases hc with hc | hc
  · exact ⟨R, le_trans (le_max_left _ _) hRR, hR, hR18, uthPath (2^j) R, uthPath_cont _ _, f, hf,
      vacuumCoupling_of_soft hq hR hroom (uthPath_cont _ _) (uthPath_anFam _ _)
        (uthPath_zero _ _) hloc (vacA_uth_pi_negative hq hR hroom) hs hc⟩
  · exact ⟨R, le_trans (le_max_left _ _) hRR, hR, hR18, uthPathNeg (2^j) R, uthPathNeg_cont _ _,
      f, hf, vacuumCoupling_of_soft hq hR hroom (uthPathNeg_cont _ _) (uthPathNeg_anFam _ _)
        (uthPathNeg_zero _ _) hloc (vacA_uthNeg_pi_negative hq hR hroom) hs hc⟩

/-- **Main reduction (weakest premise).** -/
theorem goalNeg2_of_cofinalPathSoftCoupling (h : CofinalPathSoftCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalVacuumCoupling (cofinalVacuumCoupling_of_cofinalPathSoftCoupling h)

theorem not_cofinalPathSoftCoupling_of_goalPos1 (h : GoalPos1) : ¬ CofinalPathSoftCoupling :=
  fun h' => goalNeg2_of_cofinalPathSoftCoupling h' (goalPos2_iff_goalPos1.mpr h)

#print axioms pathU_anFam
#print axioms uthPath_anFam
#print axioms uthPathNeg
#print axioms uthPathNeg_cont
#print axioms uthPathNeg_anFam
#print axioms uthPath_zero
#print axioms uthPathNeg_zero
#print axioms pathA_anR
#print axioms pathA_isolated
#print axioms pathC_isolated
#print axioms inner_Ginv_dataS
#print axioms flat_delta_le_univ
#print axioms mass_nonneg_dataS
#print axioms Ginv_loc_psd_flat
#print axioms Ginv_loc_le_all_flat
#print axioms Ginv_all_pd_flat
#print axioms flatP
#print axioms dilU_flat
#print axioms flat_loc_unit_eventually
#print axioms pathU_flat_base
#print axioms vacA_zero_flat
#print axioms vacA_pd_zero
#print axioms vacA_uth_pi_negative
#print axioms uθ_neg_pi
#print axioms uthPath_neg_pi
#print axioms vacA_uthNeg_pi_negative
#print axioms vacEdge
#print axioms VacuumCrossesAt
#print axioms vacuum_crossing
#print axioms twist_vacuum_crossing
#print axioms twist_isolated_nonunits
#print axioms uMat_continuous'
#print axioms Ug_coe_uMat
#print axioms pathU_contFamY
#print axioms pathA_jointly_continuousAt
#print axioms bulkU
#print axioms bulkP
#print axioms bulkA
#print axioms bulkD
#print axioms InteriorSoft
#print axioms pathU_base
#print axioms pathP_base
#print axioms pathA_base
#print axioms pathD_base
#print axioms joint_of_soft
#print axioms deriv_of_soft
#print axioms CanonicalCoupling
#print axioms CanonicalCouplingPos
#print axioms vacuumCoupling_of_soft
#print axioms pathSeparation_eventually_of_soft
#print axioms twistSeparation_of_uth
#print axioms twistSeparation_of_uthNeg
#print axioms TwistSoftCoupling
#print axioms twistSeparation_eventually
#print axioms CofinalTwistSoftCoupling
#print axioms cofinalTwistSeparation_of_cofinalTwistSoftCoupling
#print axioms goalNeg2_of_cofinalTwistSoftCoupling
#print axioms not_cofinalTwistSoftCoupling_of_goalPos1
#print axioms PathSoftCoupling
#print axioms CofinalPathSoftCoupling
#print axioms pathSoftCoupling_of_twist
#print axioms cofinalPathSoftCoupling_of_twist
#print axioms cofinalVacuumCoupling_of_cofinalPathSoftCoupling
#print axioms goalNeg2_of_cofinalPathSoftCoupling
#print axioms not_cofinalPathSoftCoupling_of_goalPos1

end AdalyFormal.Round9.Guarded.QualitativeR2
