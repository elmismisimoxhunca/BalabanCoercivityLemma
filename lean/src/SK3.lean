import SK2

/-!
# SK3 -- W4 at the printed-class `U` from the named inputs (lane m2_skeleton_20261015)

`holRegime_rho1` : the class holonomy regime (MR5 `holRegime_class`) at the M1 constant `rho1 12 M α₁`, `α₁ = ℓ³·2α₀`.
`w4_class`       : `cwW4 · wnormSq ≤ ⟪A, Ginv A⟫` at the class `U` (no gauge), from `SiteS1`, `RowBound`, `MassComm`, `InterfaceCharts` (`IsUnit LP`, `0 < cs ≤ 1` and the inverse `Gi` are derived here).
Same constants `cW, a₀, D` as `patchCoercive_class_exists` / `w4_M1_patched`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false
namespace AdalyFormal.M2Skel

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp OnLambdaTildeIn TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled OnLambdaT PerCubeRegular2 CoversPlaqOm0c)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.M1Site AdalyFormal.M1IMS
open AdalyFormal.M1GaugeW4
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar)
open AdalyFormal.M1NonFlat (epsNF PkA thetaN)

theorem alpha1_nonneg (ell : ℕ) {α₀ : ℝ} (h : 0 ≤ α₀) : 0 ≤ alpha1 ell α₀ := by
  unfold alpha1; positivity

theorem HolRegime.mono {Lf : PeriodicLatticeExtent} {S : Tower Lf} {ell k : ℕ} {U : Cfg Lf} {ρ ρ' : ℝ}
    (h : HolRegime S ell k U ρ) (hρ : ρ ≤ ρ') : HolRegime S ell k U ρ' := by
  intro j0 hj0 p h1 h2 h3 h4
  refine (h j0 hj0 p h1 h2 h3 h4).trans ?_
  exact div_le_div_of_nonneg_right hρ (by positivity)

theorem holRegime_rho1 {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 1 ≤ ell)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀)
    (ha1 : ((12 : ℕ) : ℝ) * M * α₀ ≤ 1) {U : LinkCfg (scaleUp ell k Lu)}
    (hU : ClassCoupled ell M 12 k S α₀ η U) :
    HolRegime S ell k U (rho1 12 M (alpha1 ell α₀)) := by
  refine HolRegime.mono (AdalyFormal.M2Route.holRegime_class hS hell hη hα ha1 hU.2 hU.1.2) ?_
  unfold rho1 alpha1
  have hl : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  set b : ℝ := ((12 : ℕ) : ℝ) * M * α₀ with hb
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hpi := Real.pi_pos
  have e : (4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)))
      = (4 * Real.pi + 4) * (2 * (ell : ℝ) ^ 3 * b) := by rw [hb]; ring
  rw [e]
  have h2 : (ell : ℝ) ^ 2 ≤ (ell : ℝ) ^ 3 := pow_le_pow_right₀ hl (by norm_num)
  have hb2 : b ^ 2 ≤ b := by nlinarith
  have h3 : 2 * b + (4 * Real.pi + 2) * b ^ 2 ≤ (4 * Real.pi + 4) * 2 * b := by
    have := mul_le_mul_of_nonneg_left hb2 (by positivity : (0:ℝ) ≤ 4 * Real.pi + 2)
    nlinarith
  have h4 : (ell : ℝ) ^ 2 * (2 * b + (4 * Real.pi + 2) * b ^ 2) ≤ (ell : ℝ) ^ 3 * ((4 * Real.pi + 4) * 2 * b) := by
    have h5 : 0 ≤ 2 * b + (4 * Real.pi + 2) * b ^ 2 := by positivity
    calc (ell : ℝ) ^ 2 * (2 * b + (4 * Real.pi + 2) * b ^ 2) ≤ (ell : ℝ) ^ 3 * (2 * b + (4 * Real.pi + 2) * b ^ 2) :=
          mul_le_mul_of_nonneg_right h2 h5
      _ ≤ (ell : ℝ) ^ 3 * ((4 * Real.pi + 4) * 2 * b) := mul_le_mul_of_nonneg_left h3 (by positivity)
  nlinarith

theorem csOf_pos {a ρ : ℝ} (ha : 0 < a) (h216 : 216 * ρ ^ 2 < 1) : 0 < csOf a ρ := by
  unfold csOf
  exact div_pos (by linarith) (lt_max_of_lt_left (by norm_num))

theorem csOf_le_one {a ρ : ℝ} (ha : 0 < a) : csOf a ρ ≤ 1 := by
  unfold csOf
  have hM : (0 : ℝ) < max 6 (16 / (3 * a)) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  rw [div_le_one hM]
  have h6 : (6 : ℝ) ≤ max 6 (16 / (3 * a)) := le_max_left _ _
  nlinarith [sq_nonneg ρ]

/-- `IsUnit LP` from the S1 bound (the proof of `MS6.isUnit_LP_strat`, with the S1 bound as hypothesis). -/
theorem isUnit_LP_of_S1 {Lf : PeriodicLatticeExtent} (G : TowerGeom Lf) (hell : 1 ≤ G.ell) (U : Cfg Lf) (a cs : ℝ)
    (hcs0 : 0 < cs) (hcs1 : cs ≤ 1) (hS1 : ∀ f, cs * wNormSq G f ≤ ⟪f, DelpA G U a f⟫) : IsUnit (LP G U a) := by
  set N : ℝ := ((G.ell : ℝ) ^ G.k) ^ 2 with hN
  have hN0 : 0 < N := by
    have : (0 : ℝ) < G.ell := by exact_mod_cast hell
    positivity
  set c : ℝ := min (cs / N) 1 with hc
  have hc0 : 0 < c := lt_min (div_pos hcs0 hN0) one_pos
  have hcoer : ∀ f : SiteL2 Lf, c * ‖siteMask G.Om0 f‖ ^ 2 ≤ ⟪f, DelpA G U a f⟫ := by
    intro f
    have hwg := wNormSq_ge G hell f
    have h1 : c * ‖siteMask G.Om0 f‖ ^ 2 ≤ cs * (‖siteMask G.Om0 f‖ ^ 2 / N) := by
      have := min_le_left (cs / N) 1
      have e : cs * (‖siteMask G.Om0 f‖ ^ 2 / N) = (cs / N) * ‖siteMask G.Om0 f‖ ^ 2 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have h2 : cs * (‖siteMask G.Om0 f‖ ^ 2 / N) ≤ cs * wNormSq G f := mul_le_mul_of_nonneg_left hwg hcs0.le
    linarith [hS1 f]
  exact (AdalyFormal.SiteCoercivity.unit_Gp_of_masked_coercive G U a hc0 (min_le_right _ _) hcoer).1

/-- the inverse `Gi` of `X*X` from the sharp row bound (`exists_Gami_of_lower` with `β ≡ 1`, `c = 1/(γ²+1)`). -/
theorem gi_of_rowBound {Lf : PeriodicLatticeExtent} (G : TowerGeom Lf) (hell : 1 ≤ G.ell) (U : Cfg Lf) (a γ : ℝ)
    (hγ : ∀ u, ‖ypWt G (sigG G) u‖ ≤ γ * ‖Xop G U a u‖) :
    ∃ Gi : YP G →L[ℝ] YP G,
      (∀ u, (ContinuousLinearMap.adjoint (Xop G U a) ∘L Xop G U a) (Gi u) = u) ∧
      (∀ u, Gi ((ContinuousLinearMap.adjoint (Xop G U a) ∘L Xop G U a) u) = u) := by
  refine exists_Gami_of_lower G U a (fun _ => 1) (fun _ => one_pos) (1 / (γ ^ 2 + 1)) (by positivity) (fun v => ?_)
  have hl1 : (1 : ℝ) ≤ G.ell := by exact_mod_cast hell
  have hsig : ∀ p : PIdx G, 1 ≤ Real.exp (sigG G (rowSite p)) := by
    intro p
    apply Real.one_le_exp
    unfold sigG
    have : 0 ≤ Real.log (G.ell : ℝ) := Real.log_nonneg hl1
    positivity
  have hv : ‖v‖ ^ 2 ≤ ‖ypWt G (sigG G) v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum (fun p _ => ?_)
    rw [ypWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), mul_pow]
    have h1 : (1 : ℝ) ≤ Real.exp (sigG G (rowSite p)) ^ 2 := one_le_pow₀ (hsig p)
    calc ‖v p‖ ^ 2 = 1 * ‖v p‖ ^ 2 := (one_mul _).symm
      _ ≤ Real.exp (sigG G (rowSite p)) ^ 2 * ‖v p‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have h2 : ‖ypWt G (sigG G) v‖ ^ 2 ≤ γ ^ 2 * ‖Xop G U a v‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) (hγ v) 2
    rwa [mul_pow] at this
  have hX0 : 0 ≤ ‖Xop G U a v‖ ^ 2 := sq_nonneg _
  have hsum : ∑ p, ‖v p‖ ^ 2 / (1 : ℝ) = ‖v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]; simp
  rw [hsum, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith

theorem hatPack_of_S1 {ell M k W : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
    {U : LinkCfg (scaleUp ell k Lu)} {a α : ℝ} (hell : 1 ≤ ell) (ha : 0 < a) {ε1 : ℝ}
    (hN : W4Num ell M 12 W a α ε1) (h216 : 216 * rhoT ell 12 M α ^ 2 < 1)
    (hS1 : SiteS1 ell k S U a (csOf a (rhoT ell 12 M α))) :
    HatPack (ell := ell) (k := k) (S := S) (W := W) U a (csOf a (rhoT ell 12 M α)) :=
  ⟨ha, isUnit_LP_of_S1 (geomOf ell k S) hell U a _ (csOf_pos ha h216) (csOf_le_one ha) hS1,
    csOf_pos ha h216, csOf_le_one ha, hS1, hN.hsm, hN.hsmD⟩

theorem w4_class {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ D : ℕ, 12 * ell + 10 ≤ D ∧
    (∀ d, D ≤ d → epsNF ell (PkA a) (thetaN ell) d ≤ cW / 2) ∧
    ∀ {M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
      {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hM : 0 < M) (hR1 : 1 ≤ R)
      (hR24 : 24 ≤ R) (hRl : 3 * 12 ≤ R * ell) (hR4 : (5 + 4) * 1 * ell ≤ R) (hroom : 17 * ell ≤ R * M)
      {d : ℕ} (hdD : D ≤ d) (hdM : d + 64 * ell ^ 2 + 2 ≤ M)
      {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
      (U : LinkCfg (scaleUp ell k Lu)) {α₀ : ℝ} (hα0 : 0 < α₀) (hαa : (12 : ℝ) * M * α₀ ≤ a₀)
      (hU : ClassCoupled ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
      (ha1 : ((12 : ℕ) : ℝ) * M * α₀ ≤ 1)
      (Lam : Set (PeriodicLatticeSite Lu)) (ε1 ε2 : ℝ) (hε1 : 0 < ε1) (hε2 : 0 < ε2)
      (hN : W4Num ell M 12 W a (alpha1 ell α₀) ε1)
      (h216 : 216 * rhoT ell 12 M (alpha1 ell α₀) ^ 2 < 1)
      (hat : SiteS1 ell k S U a (csOf a (rhoT ell 12 M (alpha1 ell α₀))))
      (gd : RowBound ell k S U a (gamC ell a (rhoT ell 12 M (alpha1 ell α₀))
        (epsXnum ell W a (rhoT ell 12 M (alpha1 ell α₀)))))
      (mc : MassComm ell M k 1 5 S U a (CMcStar ell M 1 5 a (SstarM ell 12 M (alpha1 ell α₀))))
      (hI : AdalyFormal.M2Route.InterfaceCharts ell M k d S U ((ell : ℝ) ^ k)⁻¹ ((12 : ℕ) * M * α₀))
      (A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G)),
      cwW4 ell M 1 5 W a (rhoT ell 12 M (alpha1 ell α₀)) (rho1 12 M (alpha1 ell α₀)) ε1 ε2
          (cPnf ell W d a cW (alpha1 ell α₀) ε1 12 M)
          (epsXnum ell W a (rhoT ell 12 M (alpha1 ell α₀))) (CMcStar ell M 1 5 a (SstarM ell 12 M (alpha1 ell α₀)))
        * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
        ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ := by
  obtain ⟨cW, hcW, a₀, ha₀, D, hD, hDle, hmain⟩ := AdalyFormal.M2Route.patchCoercive_class_exists hell ha
  refine ⟨cW, hcW, a₀, ha₀, D, hD, hDle, ?_⟩
  intro M R k Lu hell0 S hS hM hR1 hR24 hRl hR4 hroom d hdD hdM W hW hWR U α₀ hα0 hαa hU ha1 Lam ε1 ε2 hε1 hε2 hN h216 hat gd mc hI A
  have hηk : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  set α₁ := alpha1 ell α₀ with hα1
  have hα1p : 0 ≤ α₁ := alpha1_nonneg ell hα0.le
  have hρ := AdalyFormal.M1GaugeW4.rhoT_nonneg ell 12 M α₁ hα1p
  have hρh : 0 ≤ rho1 12 M α₁ := AdalyFormal.TowerLoc.rho1_nonneg 12 M α₁ hα1p
  have hp := hatPack_of_S1 (show 1 ≤ ell by omega) ha hN h216 hat
  have hreg := holRegime_rho1 (show 1 ≤ ell by omega) hS hηk hα0.le ha1 hU
  have hP := hmain hell0 hS hM hR1 hR24 hRl hR4 hroom hdD hdM hW hWR U (csOf a (rhoT ell 12 M α₁)) Lam hp
    (rho1 12 M α₁) hρh hreg ε1 hε1 hN.hη ((ell : ℝ) ^ k)⁻¹ hηk α₀ hα0 hU.2 ((12 : ℕ) * M * α₀) le_rfl
    (by simpa using hαa) hI
  obtain ⟨Gi, hG1, hG2⟩ := gi_of_rowBound (geomOf ell k S) (show 1 ≤ ell by omega) U a _ gd
  have hγ := gd
  have hD' : 0 < (1 - 12 * rhoT ell 12 M α₁) ^ 2 - Real.sqrt (max a 1) * ((1 + 12 * rhoT ell 12 M α₁) ^ 2
      + (512 * rhoT ell 12 M α₁ ^ 2 + 4704) / a) * epsXnum ell W a (rhoT ell 12 M α₁) := by
    have := hN.hgs; linarith
  have hγ0 : 0 ≤ gamC ell a (rhoT ell 12 M α₁) (epsXnum ell W a (rhoT ell 12 M α₁)) := by
    unfold gamC
    apply div_nonneg _ hD'.le
    have : 0 ≤ Real.sqrt (max a 1) := Real.sqrt_nonneg _
    have hr1 : 0 ≤ (512 * rhoT ell 12 M α₁ ^ 2 + 4704) / a := by positivity
    positivity
  have hCM : 0 ≤ CMcStar ell M 1 5 a (SstarM ell 12 M α₁) := by
    unfold AdalyFormal.TowerLoc.CMcStar AdalyFormal.TowerLoc.Estar
    have := AdalyFormal.M1IMS.KG_nonneg ell M 1 5
    positivity
  have hR : (5 + 3) * 1 * ell ≤ R := by omega
  exact ginv_weighted_coercive hell0 hS one_pos hM hell hR1 hR (le_refl 5) hW hWR U a (csOf a (rhoT ell 12 M α₁)) Lam hp
    Gi hG1 hG2 _ hγ0 hγ (rho1 12 M α₁) hρh hreg _ hCM mc ε1 ε2 hε1 hε2 hN.hη _ hP A

end AdalyFormal.M2Skel

#print axioms AdalyFormal.M2Skel.holRegime_rho1
#print axioms AdalyFormal.M2Skel.w4_class
