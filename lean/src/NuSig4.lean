import NuSig3

/-!
# NuSig4 -- `Wop` and `Tfull` on sigma_3 bond fields do not depend on the Cartan configuration (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverJacobi

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

/-- sigma_3 bond field. -/
def SigB' (x : BondFnL2 L) : Prop := pwDiagB L x = x

theorem gradAdj_sig {U : Cfg L} (hU : CartanCfg U) {x : BondFnL2 L} (hx : SigB' x) : SigS (gradAdj U x) := by
  unfold SigS
  have h := gradAdj_pwDiag hU x
  rw [hx] at h
  exact h.symm

theorem gradAdj_sig_eq {U V : Cfg L} (hU : CartanCfg U) (hV : CartanCfg V) {x : BondFnL2 L} (hx : SigB' x) :
    gradAdj U x = gradAdj V x := by
  have h1 : pwDiagS L (gradAdj U x) = gradAdj U x := gradAdj_sig hU hx
  have h2 : pwDiagS L (gradAdj V x) = gradAdj V x := gradAdj_sig hV hx
  calc gradAdj U x = pwDiagS L (gradAdj U x) := h1.symm
    _ = pwDiagS L (gradAdj (fun _ : Bond L => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) x) := pwDiagS_gradAdj_flat hU x
    _ = pwDiagS L (gradAdj V x) := (pwDiagS_gradAdj_flat hV x).symm
    _ = gradAdj V x := h2

theorem gradL2_sig_eq {U V : Cfg L} (hU : CartanCfg U) (hV : CartanCfg V) {g : SiteL2 L} (hg : SigS g) :
    gradL2 U g = gradL2 V g := by
  have h : pwDiagS L g = g := hg
  have e1 := gradL2_pwDiag_flat hU g
  have e2 := gradL2_pwDiag_flat hV g
  rw [h] at e1 e2
  rw [e1, e2]

theorem Wop_sig_eq (G : TowerGeom L) {U V : Cfg L} (hU : CartanCfg U) (hV : CartanCfg V) (a : ℝ) {x : BondFnL2 L} (hx : SigB' x)
    (hXU : IsUnit (DelpA G U a + (1 - siteMask G.Om0))) (hXV : IsUnit (DelpA G V a + (1 - siteMask G.Om0))) :
    Wop G U a x = Wop G V a x := by
  simp only [Wop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
  congr 1
  have hd : gradAdj U x = gradAdj V x := gradAdj_sig_eq hU hV hx
  have hds : SigS (gradAdj V x) := gradAdj_sig hV hx
  rw [hd, Rproj_sig_eq G hU hV hds]
  have hrs : SigS (Rproj G V (gradAdj V x)) := Rproj_sig G hV hds
  rw [Gp_sig_eq G hU hV a hrs hXU hXV]
  exact gradL2_sig_eq hU hV (Gp_sigS G hV a hrs hXV)

theorem Tfull_sig_eq (G : TowerGeom L) {U V : Cfg L} (hU : CartanCfg U) (hV : CartanCfg V) {x : BondFnL2 L} (hx : SigB' x) :
    Tfull G U x = Tfull G V x := by
  simp only [Tfull, ContinuousLinearMap.comp_apply]
  rw [gradAdj_sig_eq hU hV hx, Rproj_sig_eq G hU hV (gradAdj_sig hV hx)]

#print axioms Wop_sig_eq
#print axioms Tfull_sig_eq

end AdalyFormal.CoverJacobi
