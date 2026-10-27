import NuSig1

/-!
# NuSig2 -- `lapDir`, `NQp`, `RImage`, `Rproj`, `Qpa`, `DelpA`, `Gp`, `Wop`, `Tfull` on sigma_3 fields do not depend on the Cartan configuration (lane ncwdh_ell2_20261018)
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

variable {L : PeriodicLatticeExtent}

theorem siteMask_pwDiag (S : Set (PeriodicLatticeSite L)) (f : SiteL2 L) :
    siteMask S (pwDiagS L f) = pwDiagS L (siteMask S f) := by
  classical
  refine PiLp.ext (fun x => ?_)
  rw [siteMask_apply, pwDiag_apply, pwDiag_apply, siteMask_apply]
  split_ifs
  · rfl
  · exact (map_zero diagP).symm

theorem SigS.pwDiag (f : SiteL2 L) : SigS (pwDiagS L f) := pwDiag_idem _ f

theorem SigS.mask {S : Set (PeriodicLatticeSite L)} {f : SiteL2 L} (hf : SigS f) : SigS (siteMask S f) := by
  unfold SigS at *
  rw [← siteMask_pwDiag, hf]

theorem inner_sig_left {s : SiteL2 L} (hs : SigS s) (w : SiteL2 L) : ⟪s, w⟫ = ⟪s, pwDiagS L w⟫ := by
  conv_lhs => rw [← hs]
  exact pwDiag_symm _ s w

theorem lapDir_pwDiag (G : TowerGeom L) {U : Cfg L} (hU : CartanCfg U) (f : SiteL2 L) :
    lapDir G U (pwDiagS L f) = pwDiagS L (lapDir G U f) := by
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply]
  rw [siteMask_pwDiag, lapFull_pwDiag hU, siteMask_pwDiag]

theorem lapDir_sig_eq (G : TowerGeom L) {U V : Cfg L} (hU : CartanCfg U) (hV : CartanCfg V) {f : SiteL2 L} (hf : SigS f) :
    lapDir G U f = lapDir G V f := by
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply]
  have h1 : SigS (siteMask G.Om0 f) := hf.mask
  have h1' : pwDiagS L (siteMask G.Om0 f) = siteMask G.Om0 f := h1
  have e1 := lapFull_pwDiag_flat hU (siteMask G.Om0 f)
  have e2 := lapFull_pwDiag_flat hV (siteMask G.Om0 f)
  rw [h1'] at e1 e2
  rw [e1, e2]

theorem NQp_pwDiag (G : TowerGeom L) {U : Cfg L} (hU : CartanCfg U) {n : SiteL2 L} (hn : n ∈ NQp G U) :
    pwDiagS L n ∈ NQp G U := by
  refine ⟨fun x hx => ?_, fun j hj y hy => ?_⟩
  · rw [pwDiag_apply, hn.1 x hx, map_zero]
  · rw [Qlev_sig G hU j y (SigS.pwDiag n)]
    have h1 := hn.2 j hj y hy
    rw [Qlev_apply] at h1
    have h2 : diagP (Qcomposite (bgTower G U) G.ell j (WithLp.ofLp n) y) = flatQ G.ell j (fun x => diagP (WithLp.ofLp n x)) y :=
      Qcomposite_diagP (fun l => UbarTower_cartan hU G.ell l) G.ell j _ y
    rw [h1, map_zero] at h2
    have h3 : (WithLp.ofLp (pwDiagS L n)) = fun x => diagP (WithLp.ofLp n x) := by
      funext x; exact pwDiag_apply _ n x
    rw [h3]
    exact h2.symm

theorem NQp_sig_iff (G : TowerGeom L) {U V : Cfg L} (hU : CartanCfg U) (hV : CartanCfg V) {f : SiteL2 L} (hf : SigS f) :
    f ∈ NQp G U ↔ f ∈ NQp G V := by
  constructor
  · intro h
    exact ⟨h.1, fun j hj y hy => by rw [← Qlev_sig_eq G hU hV j y hf]; exact h.2 j hj y hy⟩
  · intro h
    exact ⟨h.1, fun j hj y hy => by rw [Qlev_sig_eq G hU hV j y hf]; exact h.2 j hj y hy⟩

theorem RImage_pwDiag (G : TowerGeom L) {U : Cfg L} (hU : CartanCfg U) {w : SiteL2 L} (hw : w ∈ RImage G U) :
    pwDiagS L w ∈ RImage G U := by
  obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hw
  refine Submodule.mem_map.mpr ⟨pwDiagS L m, NQp_pwDiag G hU hm, ?_⟩
  exact lapDir_pwDiag G hU m

theorem Rproj_sig (G : TowerGeom L) {U : Cfg L} (hU : CartanCfg U) {f : SiteL2 L} (hf : SigS f) :
    SigS (Rproj G U f) := by
  have hmem : pwDiagS L ((RImage G U).starProjection f) ∈ RImage G U :=
    RImage_pwDiag G hU (Submodule.starProjection_apply_mem (RImage G U) f)
  have hfix : pwDiagS L f = f := hf
  have key : (RImage G U).starProjection f = pwDiagS L ((RImage G U).starProjection f) := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem (fun w hw => ?_)
    have h1 : f - pwDiagS L ((RImage G U).starProjection f) = pwDiagS L (f - (RImage G U).starProjection f) := by
      rw [map_sub, hfix]
    rw [h1, pwDiag_symm]
    exact Submodule.starProjection_inner_eq_zero f _ (RImage_pwDiag G hU hw)
  exact key.symm

theorem Rproj_sig_eq (G : TowerGeom L) {U V : Cfg L} (hU : CartanCfg U) (hV : CartanCfg V) {f : SiteL2 L} (hf : SigS f) :
    Rproj G U f = Rproj G V f := by
  set r := Rproj G V f with hr
  have hrs : SigS r := Rproj_sig G hV hf
  have hrK : r ∈ RImage G V := Submodule.starProjection_apply_mem (RImage G V) f
  -- r ∈ RImage U
  have hrU : r ∈ RImage G U := by
    obtain ⟨n, hn, hnr⟩ := Submodule.mem_map.mp hrK
    have hn' : pwDiagS L n ∈ NQp G V := NQp_pwDiag G hV hn
    have hn'U : pwDiagS L n ∈ NQp G U := (NQp_sig_iff G hU hV (SigS.pwDiag n)).mpr hn'
    refine Submodule.mem_map.mpr ⟨pwDiagS L n, hn'U, ?_⟩
    have e1 : lapDir G U (pwDiagS L n) = lapDir G V (pwDiagS L n) := lapDir_sig_eq G hU hV (SigS.pwDiag n)
    have e2 : lapDir G V (pwDiagS L n) = pwDiagS L (lapDir G V n) := lapDir_pwDiag G hV n
    have e3 : (lapDir G V n) = r := hnr
    show lapDir G U (pwDiagS L n) = r
    rw [e1, e2, e3]
    exact hrs
  -- orthogonality
  have horth : ∀ w ∈ RImage G U, ⟪f - r, w⟫ = 0 := by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hw
    have hfr : SigS (f - r) := by
      unfold SigS at *
      rw [map_sub, hf, hrs]
    rw [inner_sig_left hfr]
    show ⟪f - r, pwDiagS L (lapDir G U m)⟫ = 0
    have e1 : pwDiagS L (lapDir G U m) = lapDir G U (pwDiagS L m) := (lapDir_pwDiag G hU m).symm
    have hm' : pwDiagS L m ∈ NQp G U := NQp_pwDiag G hU hm
    have hmV : pwDiagS L m ∈ NQp G V := (NQp_sig_iff G hU hV (SigS.pwDiag m)).mp hm'
    have e2 : lapDir G U (pwDiagS L m) = lapDir G V (pwDiagS L m) := lapDir_sig_eq G hU hV (SigS.pwDiag m)
    have hwV : lapDir G V (pwDiagS L m) ∈ RImage G V := Submodule.mem_map.mpr ⟨_, hmV, rfl⟩
    rw [e1, e2]
    exact Submodule.starProjection_inner_eq_zero f _ hwV
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero hrU horth

#print axioms Rproj_sig_eq

end AdalyFormal.CoverJacobi
