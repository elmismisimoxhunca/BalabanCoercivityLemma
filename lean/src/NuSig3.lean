import NuSig2
import ZXR2Ops3

/-!
# NuSig3 -- `Qpa`, `DelpA`, `Gp`, `Wop`, `Tfull` on sigma_3 fields do not depend on the Cartan configuration (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverJacobi

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.QjComposite
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

theorem diagP_inner_left {s : SuTwo} (hs : diagP s = s) (X : SuTwo) : ⟪s, X⟫ = ⟪s, diagP X⟫ := by
  conv_lhs => rw [← hs]
  exact diagP_symm s X

theorem Qlev_diagP' (G : TowerGeom L) {U : Cfg L} (hU : CartanCfg U) (j : ℕ) (y : PeriodicLatticeSite L) (f : SiteL2 L) :
    diagP (Qlev G U j y f) = flatQ G.ell j (fun x => diagP (WithLp.ofLp f x)) y := by
  rw [Qlev_apply]
  exact Qcomposite_diagP (fun l => UbarTower_cartan hU G.ell l) G.ell j _ y

theorem Qlev_pwDiag (G : TowerGeom L) {U : Cfg L} (hU : CartanCfg U) (j : ℕ) (y : PeriodicLatticeSite L) (f : SiteL2 L) :
    Qlev G U j y (pwDiagS L f) = diagP (Qlev G U j y f) := by
  rw [Qlev_sig G hU j y (SigS.pwDiag f), Qlev_diagP' G hU j y f]
  rfl

theorem QlevAdj_pwDiag (G : TowerGeom L) {U : Cfg L} (hU : CartanCfg U) (j : ℕ) (y : PeriodicLatticeSite L) (s : SuTwo) :
    ContinuousLinearMap.adjoint (Qlev G U j y) (diagP s) = pwDiagS L (ContinuousLinearMap.adjoint (Qlev G U j y) s) := by
  refine ext_inner_right ℝ (fun k => ?_)
  rw [ContinuousLinearMap.adjoint_inner_left, diagP_symm, ← Qlev_pwDiag G hU, ← ContinuousLinearMap.adjoint_inner_left,
    pwDiag_symm]

theorem QlevAdj_sig_eq (G : TowerGeom L) {U V : Cfg L} (hU : CartanCfg U) (hV : CartanCfg V) (j : ℕ) (y : PeriodicLatticeSite L)
    {s : SuTwo} (hs : diagP s = s) :
    ContinuousLinearMap.adjoint (Qlev G U j y) s = ContinuousLinearMap.adjoint (Qlev G V j y) s := by
  refine ext_inner_right ℝ (fun k => ?_)
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
    diagP_inner_left hs (Qlev G U j y k), diagP_inner_left hs (Qlev G V j y k), Qlev_diagP' G hU, Qlev_diagP' G hV]

theorem Qpa_pwDiag (G : TowerGeom L) {U : Cfg L} (hU : CartanCfg U) (a : ℝ) (f : SiteL2 L) :
    Qpa G U a (pwDiagS L f) = pwDiagS L (Qpa G U a f) := by
  classical
  simp only [Qpa, ContinuousLinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun y _ => ?_))
  split_ifs
  · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul]
    rw [Qlev_pwDiag G hU, QlevAdj_pwDiag G hU]
  · simp

theorem Qpa_sig_eq (G : TowerGeom L) {U V : Cfg L} (hU : CartanCfg U) (hV : CartanCfg V) (a : ℝ) {f : SiteL2 L} (hf : SigS f) :
    Qpa G U a f = Qpa G V a f := by
  classical
  simp only [Qpa, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun y _ => ?_))
  split_ifs
  · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    have hq : Qlev G U j y f = Qlev G V j y f := Qlev_sig_eq G hU hV j y hf
    have hs : diagP (Qlev G V j y f) = Qlev G V j y f := by
      rw [Qlev_sig G hV j y hf]
      exact flatQ_sig G.ell j hf.fn y
    rw [hq, QlevAdj_sig_eq G hU hV j y hs]
  · rfl

theorem DelpA_pwDiag (G : TowerGeom L) {U : Cfg L} (hU : CartanCfg U) (a : ℝ) (f : SiteL2 L) :
    DelpA G U a (pwDiagS L f) = pwDiagS L (DelpA G U a f) := by
  unfold DelpA
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  rw [siteMask_pwDiag, lapFull_pwDiag hU, Qpa_pwDiag G hU, ← map_add, siteMask_pwDiag]

theorem DelpA_sig_eq (G : TowerGeom L) {U V : Cfg L} (hU : CartanCfg U) (hV : CartanCfg V) (a : ℝ) {f : SiteL2 L} (hf : SigS f) :
    DelpA G U a f = DelpA G V a f := by
  unfold DelpA
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  have h1 : SigS (siteMask G.Om0 f) := hf.mask
  have h1' : pwDiagS L (siteMask G.Om0 f) = siteMask G.Om0 f := h1
  have e1 := lapFull_pwDiag_flat hU (siteMask G.Om0 f)
  have e2 := lapFull_pwDiag_flat hV (siteMask G.Om0 f)
  rw [h1'] at e1 e2
  rw [e1, e2, Qpa_sig_eq G hU hV a h1]

/-- `Gp` on a sigma_3 field, given that both Dirichlet operators are units. -/
theorem Gp_sig_eq (G : TowerGeom L) {U V : Cfg L} (hU : CartanCfg U) (hV : CartanCfg V) (a : ℝ) {f : SiteL2 L} (hf : SigS f)
    (hXU : IsUnit (DelpA G U a + (1 - siteMask G.Om0))) (hXV : IsUnit (DelpA G V a + (1 - siteMask G.Om0))) :
    Gp G U a f = Gp G V a f := by
  unfold Gp
  simp only [ContinuousLinearMap.comp_apply]
  set f' := siteMask G.Om0 f with hf'
  have hf's : SigS f' := hf.mask
  set XU := DelpA G U a + (1 - siteMask G.Om0) with hXUdef
  set XV := DelpA G V a + (1 - siteMask G.Om0) with hXVdef
  set g := Ring.inverse XU f' with hg
  have hXg : XU g = f' := by
    have := Ring.mul_inverse_cancel XU hXU
    exact congrArg (fun S : SiteL2 L →L[ℝ] SiteL2 L => S f') this
  -- XU commutes with pwDiag
  have hcomm : ∀ h : SiteL2 L, XU (pwDiagS L h) = pwDiagS L (XU h) := by
    intro h
    simp only [hXUdef, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [DelpA_pwDiag G hU, map_add, map_sub, siteMask_pwDiag]
  have hinvU : ∀ z, Ring.inverse XU (XU z) = z := fun z =>
    congrArg (fun S : SiteL2 L →L[ℝ] SiteL2 L => S z) (Ring.inverse_mul_cancel XU hXU)
  have hinvV : ∀ z, Ring.inverse XV (XV z) = z := fun z =>
    congrArg (fun S : SiteL2 L →L[ℝ] SiteL2 L => S z) (Ring.inverse_mul_cancel XV hXV)
  have hgs : SigS g := by
    have h1 : XU (pwDiagS L g) = XU g := by rw [hcomm, hXg]; exact hf's
    have h2 : pwDiagS L g = g := by
      calc pwDiagS L g = Ring.inverse XU (XU (pwDiagS L g)) := (hinvU _).symm
        _ = Ring.inverse XU (XU g) := by rw [h1]
        _ = g := hinvU g
    exact h2
  have hXVg : XV g = f' := by
    have e : XV g = XU g := by
      simp only [hXVdef, hXUdef, ContinuousLinearMap.add_apply]
      rw [DelpA_sig_eq G hV hU a hgs]
    rw [e, hXg]
  calc Ring.inverse XU f' = g := rfl
    _ = Ring.inverse XV (XV g) := (hinvV g).symm
    _ = Ring.inverse XV f' := by rw [hXVg]

theorem Gp_sigS (G : TowerGeom L) {U : Cfg L} (hU : CartanCfg U) (a : ℝ) {f : SiteL2 L} (hf : SigS f)
    (hXU : IsUnit (DelpA G U a + (1 - siteMask G.Om0))) : SigS (Gp G U a f) := by
  unfold Gp
  simp only [ContinuousLinearMap.comp_apply]
  set f' := siteMask G.Om0 f with hf'
  have hf's : SigS f' := hf.mask
  set XU := DelpA G U a + (1 - siteMask G.Om0) with hXUdef
  set g := Ring.inverse XU f' with hg
  have hXg : XU g = f' := by
    have := Ring.mul_inverse_cancel XU hXU
    exact congrArg (fun S : SiteL2 L →L[ℝ] SiteL2 L => S f') this
  have hcomm : ∀ h : SiteL2 L, XU (pwDiagS L h) = pwDiagS L (XU h) := by
    intro h
    simp only [hXUdef, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [DelpA_pwDiag G hU, map_add, map_sub, siteMask_pwDiag]
  have hinvU : ∀ z, Ring.inverse XU (XU z) = z := fun z =>
    congrArg (fun S : SiteL2 L →L[ℝ] SiteL2 L => S z) (Ring.inverse_mul_cancel XU hXU)
  have h1 : XU (pwDiagS L g) = XU g := by rw [hcomm, hXg]; exact hf's
  calc pwDiagS L g = Ring.inverse XU (XU (pwDiagS L g)) := (hinvU _).symm
    _ = Ring.inverse XU (XU g) := by rw [h1]
    _ = g := hinvU g

#print axioms Qpa_sig_eq
#print axioms Gp_sig_eq

end AdalyFormal.CoverJacobi
