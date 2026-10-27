import NsCvO16

/-!
# CvO17 -- `Q` and `C⁽²⁾` of the one-step raw map on sigma_3 fields, at a Cartan background (lane omega)

`aF θ = (θ_b, 0, 0)_b` is the sigma_3-valued coordinate field of angles `θ`.  For a Cartan background `cartanOf φ` whose loops all have `|angle| < π`
(`hφ`) and which is regular (`RegBg2`):
* `qStepX_sigma3_eventually`: `qStepX s ell (cartanOf φ) (aF θ) = aF (Rsig θ)` for all `θ` near `0`;
* `QlinStepX_sigma3`: `QlinStepX s ell (cartanOf φ) (aF θ) = aF (Rsig θ)` -- the linear part on sigma_3 fields IS the abelian `Rsig`, independent of `φ`;
* `C2StepX_sigma3`: `C2StepX s ell (cartanOf φ) (aF θ) = 0` -- the second-order term vanishes on sigma_3 fields.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2 (XS toM2 fromM2 expCfgX qStepX QlinStepX C2StepX rawStep fromM2_toM2)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.SmoothLog (fderiv_fderiv_comp)

variable {L : PeriodicLatticeExtent}

/-- sigma_3-valued coordinate field. -/
def aF (θ : PeriodicLatticeEdge L → ℝ) : XS L := fun b => ![θ b, 0, 0]

/-- `aF` as a continuous linear map. -/
noncomputable def aFL : (PeriodicLatticeEdge L → ℝ) →L[ℝ] XS L :=
  LinearMap.toContinuousLinearMap
    { toFun := aF
      map_add' := fun θ θ' => by funext b; ext i; fin_cases i <;> simp [aF]
      map_smul' := fun r θ => by funext b; ext i; fin_cases i <;> simp [aF] }

theorem aFL_apply (θ : PeriodicLatticeEdge L → ℝ) : aFL θ = aF θ := rfl

theorem toM2_aF (x : ℝ) : toM2 ![x, 0, 0] = dg x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toM2, dg, mul_comm]

theorem expCfgX_aF (θ : PeriodicLatticeEdge L → ℝ) : expCfgX (aF θ) = cartanOf θ := by
  funext b; simp only [expCfgX, aF, cartanOf, toM2_aF, su2Exp_dg]

theorem fromM2_dg (x : ℝ) : fromM2 (dg x) = ![x, 0, 0] := by
  ext i; fin_cases i <;> simp [fromM2, dg]

theorem pathAngG_continuous (s : ℕ) (p : List (Fin 3)) (y : PeriodicLatticeSite L) :
    Continuous (fun θ : PeriodicLatticeEdge L → ℝ => pathAngG s θ y p) := by
  induction p generalizing y with
  | nil => simp only [pathAngG]; exact continuous_const
  | cons μ rest ih => simp only [pathAngG]; exact (continuous_apply _).add (ih _)

theorem loopAngG_continuous (s ell : ℕ) (y : PeriodicLatticeSite L) (μ : Fin 3) (x : PeriodicLatticeSite L) :
    Continuous (fun θ : PeriodicLatticeEdge L → ℝ => loopAngG s ell θ y μ x) := by
  unfold loopAngG
  exact (((pathAngG_continuous s _ y).add (pathAngG_continuous s _ x)).sub (pathAngG_continuous s _ _)).sub (pathAngG_continuous s _ y)

theorem blockAngG_continuous (s ell : ℕ) (y : PeriodicLatticeSite L) (μ : Fin 3) :
    Continuous (fun θ : PeriodicLatticeEdge L → ℝ => blockAngG s ell θ y μ) := by
  unfold blockAngG
  exact (continuous_const.mul (continuous_finsetSum _ (fun x _ => loopAngG_continuous s ell y μ x))).add (pathAngG_continuous s _ y)

theorem sAngG_continuous (s ell : ℕ) (y : PeriodicLatticeSite L) :
    Continuous (fun θ : PeriodicLatticeEdge L → ℝ => sAngG s ell θ y) := by
  unfold sAngG
  exact continuous_const.mul (continuous_finsetSum _ (fun x _ => pathAngG_continuous s _ y))

theorem Rsig_continuous (s ell : ℕ) (c : PeriodicLatticeEdge L) :
    Continuous (fun θ : PeriodicLatticeEdge L → ℝ => Rsig s ell θ c) := by
  unfold Rsig
  exact (((sAngG_continuous s ell _).neg).add (blockAngG_continuous s ell _ _)).add (sAngG_continuous s ell _)

theorem eventually_abs_lt_of_cont {f : (PeriodicLatticeEdge L → ℝ) → ℝ} (hf : Continuous f) (h0 : |f 0| < Real.pi) :
    ∀ᶠ θ in 𝓝 (0 : PeriodicLatticeEdge L → ℝ), |f θ| < Real.pi :=
  (hf.abs.continuousAt (x := 0)).eventually (gt_mem_nhds h0 |>.mono (fun _ h => h))


theorem sAngG_zero (s ell : ℕ) (y : PeriodicLatticeSite L) : sAngG s ell (0 : PeriodicLatticeEdge L → ℝ) y = 0 := by
  unfold sAngG; simp [pathAngG_zero]

theorem blockAngG_zero (s ell : ℕ) (y : PeriodicLatticeSite L) (μ : Fin 3) :
    blockAngG s ell (0 : PeriodicLatticeEdge L → ℝ) y μ = 0 := by
  unfold blockAngG; simp [loopAngG_zero, pathAngG_zero]

theorem Rsig_zero (s ell : ℕ) (c : PeriodicLatticeEdge L) : Rsig s ell (0 : PeriodicLatticeEdge L → ℝ) c = 0 := by
  unfold Rsig; simp [sAngG_zero, blockAngG_zero]

theorem loopAngG_smul (s ell : ℕ) (r : ℝ) (θ : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L) (μ : Fin 3) (x : PeriodicLatticeSite L) :
    loopAngG s ell (r • θ) y μ x = r * loopAngG s ell θ y μ x := by
  unfold loopAngG; rw [pathAngG_smul, pathAngG_smul, pathAngG_smul, pathAngG_smul]; ring

theorem Rsig_smul (s ell : ℕ) (r : ℝ) (θ : PeriodicLatticeEdge L → ℝ) : Rsig s ell (r • θ) = r • Rsig s ell θ := by
  funext c
  simp only [Rsig, sAngG, blockAngG, loopAngG_smul, pathAngG_smul, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- `Rsig` as a continuous linear map. -/
noncomputable def RsigL (s ell : ℕ) : (PeriodicLatticeEdge L → ℝ) →L[ℝ] (PeriodicLatticeEdge L → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := Rsig s ell
      map_add' := Rsig_add s ell
      map_smul' := fun r θ => Rsig_smul s ell r θ }

theorem RsigL_apply (s ell : ℕ) (θ : PeriodicLatticeEdge L → ℝ) : RsigL s ell θ = Rsig s ell θ := rfl

theorem qStepX_sigma3_eventually (s ell : ℕ) (φ : PeriodicLatticeEdge L → ℝ)
    (hφ : ∀ c : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf c.1 s ell, |loopAngG s ell φ c.1 c.2 x| < Real.pi) :
    ∀ᶠ θ in 𝓝 (0 : PeriodicLatticeEdge L → ℝ), qStepX s ell (cartanOf φ) (aF θ) = aF (Rsig s ell θ) := by
  have h1 : ∀ᶠ θ in 𝓝 (0 : PeriodicLatticeEdge L → ℝ), ∀ c : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf c.1 s ell,
      |loopAngG s ell (θ + φ) c.1 c.2 x| < Real.pi := by
    rw [Filter.eventually_all]; intro c
    rw [Filter.eventually_all_finset]; intro x hx
    exact eventually_abs_lt_of_cont ((loopAngG_continuous s ell c.1 c.2 x).comp (continuous_id.add continuous_const))
      (by simpa using hφ c x hx)
  have h2 : ∀ᶠ θ in 𝓝 (0 : PeriodicLatticeEdge L → ℝ), ∀ c : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf c.1 s ell,
      |pathAngG s θ c.1 (coarseGammaPath s c.1 x)| < Real.pi := by
    rw [Filter.eventually_all]; intro c
    rw [Filter.eventually_all_finset]; intro x hx
    exact eventually_abs_lt_of_cont (pathAngG_continuous s _ c.1) (by simp [pathAngG_zero, Real.pi_pos])
  have h3 : ∀ᶠ θ in 𝓝 (0 : PeriodicLatticeEdge L → ℝ), ∀ c : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf (cPlusS s ell c) s ell,
      |pathAngG s θ (cPlusS s ell c) (coarseGammaPath s (cPlusS s ell c) x)| < Real.pi := by
    rw [Filter.eventually_all]; intro c
    rw [Filter.eventually_all_finset]; intro x hx
    exact eventually_abs_lt_of_cont (pathAngG_continuous s _ _) (by simp [pathAngG_zero, Real.pi_pos])
  have h4 : ∀ᶠ θ in 𝓝 (0 : PeriodicLatticeEdge L → ℝ), ∀ c : PeriodicLatticeEdge L, |Rsig s ell θ c| < Real.pi := by
    rw [Filter.eventually_all]; intro c
    exact eventually_abs_lt_of_cont (Rsig_continuous s ell c) (by simp [Rsig_zero, Real.pi_pos])
  filter_upwards [h1, h2, h3, h4] with θ a1 a2 a3 a4
  funext c
  show fromM2 (su2Log (rawStep s ell (cartanOf φ) (expCfgX (aF θ)) c)) = aF (Rsig s ell θ) c
  rw [expCfgX_aF, rawStep_cartanOf s ell φ θ c (hφ c) (a1 c) (a2 c) (a3 c), su2Log_cartan _ (a4 c)]
  simp only [aF]
  exact fromM2_dg _


open AdalyFormal.IngredientFamilyR2 (SG)
open AdalyFormal.CoverOmega in
/-- `qStepX ∘ aFL` and `aFL ∘ RsigL` agree near `0`. -/
theorem qStepX_comp_aFL_eventually (s ell : ℕ) (φ : PeriodicLatticeEdge L → ℝ)
    (hφ : ∀ c : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf c.1 s ell, |loopAngG s ell φ c.1 c.2 x| < Real.pi) :
    (fun θ : PeriodicLatticeEdge L → ℝ => qStepX s ell (cartanOf φ) (aFL θ)) =ᶠ[𝓝 0]
      fun θ => aFL (RsigL s ell θ) := by
  filter_upwards [qStepX_sigma3_eventually s ell φ hφ] with θ h
  simpa [aFL_apply, RsigL_apply] using h

/-- **the linear part of the raw step on sigma_3 fields**: `QlinStepX s ell (cartanOf φ) (aF θ) = aF (Rsig θ)`. -/
theorem QlinStepX_sigma3 (s ell : ℕ) (φ : PeriodicLatticeEdge L → ℝ)
    (hφ : ∀ c : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf c.1 s ell, |loopAngG s ell φ c.1 c.2 x| < Real.pi)
    (hreg : RegBg2 s ell (cartanOf φ)) (θ : PeriodicLatticeEdge L → ℝ) :
    QlinStepX s ell (cartanOf φ) (aF θ) = aF (Rsig s ell θ) := by
  have hd : DifferentiableAt ℝ (qStepX s ell (cartanOf φ)) (aFL (0 : PeriodicLatticeEdge L → ℝ)) := by
    rw [map_zero]; exact (qStepX_contDiffAt2 s ell _ hreg).differentiableAt (by simp)
  have h1 := hd.hasFDerivAt.comp (0 : PeriodicLatticeEdge L → ℝ) aFL.hasFDerivAt
  have h2 : HasFDerivAt (fun θ => aFL (RsigL s ell θ)) ((aFL (L := L)).comp (RsigL (L := L) s ell)) 0 := ((aFL (L := L)).comp (RsigL (L := L) s ell)).hasFDerivAt
  have h3 := h2.congr_of_eventuallyEq (qStepX_comp_aFL_eventually s ell φ hφ)
  have h4 := h1.unique h3
  have h5 := congrArg (fun D => D θ) h4
  simp only [ContinuousLinearMap.comp_apply] at h5
  rw [map_zero] at h5
  show (fderiv ℝ (qStepX s ell (cartanOf φ)) 0) (aF θ) = _
  rw [← aFL_apply, h5, aFL_apply, RsigL_apply]

/-- **the second-order term vanishes on sigma_3 fields**: `C2StepX s ell (cartanOf φ) (aF θ) = 0`. -/
theorem C2StepX_sigma3 (s ell : ℕ) (φ : PeriodicLatticeEdge L → ℝ)
    (hφ : ∀ c : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf c.1 s ell, |loopAngG s ell φ c.1 c.2 x| < Real.pi)
    (hreg : RegBg2 s ell (cartanOf φ)) (θ : PeriodicLatticeEdge L → ℝ) :
    C2StepX s ell (cartanOf φ) (aF θ) = 0 := by
  have hf2 : ContDiffAt ℝ 2 (qStepX s ell (cartanOf φ)) (aFL (0 : PeriodicLatticeEdge L → ℝ)) := by
    rw [map_zero]; exact (qStepX_contDiffAt2 s ell _ hreg).of_le (by simp)
  have hg2 : ContDiffAt ℝ 2 (⇑(aFL (L := L))) 0 := (aFL (L := L)).contDiff.contDiffAt
  have hc := fderiv_fderiv_comp (qStepX s ell (cartanOf φ)) aFL 0 hf2 hg2 θ θ
  have hev := qStepX_comp_aFL_eventually s ell φ hφ
  have e1 : fderiv ℝ (fderiv ℝ (fun θ : PeriodicLatticeEdge L → ℝ => qStepX s ell (cartanOf φ) (aFL θ))) 0 =
      fderiv ℝ (fderiv ℝ (fun θ : PeriodicLatticeEdge L → ℝ => aFL (RsigL s ell θ))) 0 :=
    (hev.fderiv).fderiv_eq
  have e2 : fderiv ℝ (fun θ : PeriodicLatticeEdge L → ℝ => aFL (RsigL s ell θ)) = fun _ => (aFL (L := L)).comp (RsigL (L := L) s ell) := by
    funext x; exact ((aFL (L := L)).comp (RsigL (L := L) s ell)).fderiv
  have e3 : fderiv ℝ (fderiv ℝ (fun θ : PeriodicLatticeEdge L → ℝ => aFL (RsigL s ell θ))) 0 = 0 := by
    rw [e2]; exact fderiv_const_apply _
  have e4 : fderiv ℝ (aFL : (PeriodicLatticeEdge L → ℝ) →L[ℝ] XS L) = fun _ => aFL := by
    funext x; exact aFL.fderiv
  have e5 : fderiv ℝ (fderiv ℝ (aFL : (PeriodicLatticeEdge L → ℝ) →L[ℝ] XS L)) 0 = 0 := by
    rw [e4]; exact fderiv_const_apply _
  have e6 : (fun θ : PeriodicLatticeEdge L → ℝ => qStepX s ell (cartanOf φ) (aFL θ)) =
      qStepX s ell (cartanOf φ) ∘ aFL := rfl
  rw [e6] at e1
  rw [e1, e3, e5, e4] at hc
  simp only [zero_apply, map_zero, add_zero] at hc
  unfold C2StepX
  rw [← aFL_apply]
  rw [← hc, smul_zero]

#print axioms qStepX_sigma3_eventually
#print axioms QlinStepX_sigma3
#print axioms C2StepX_sigma3

end AdalyFormal.CoverOmega
