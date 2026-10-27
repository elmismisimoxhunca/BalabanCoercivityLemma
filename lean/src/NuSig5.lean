import NuSig4
import NtCvO23

/-!
# NuSig5 -- the sigma_3 block of `Delta` and of `Ginv` is affine in the layer plaquette weight (lane ncwdh_ell2_20261018)

For a Cartan configuration `U` whose plaquette cosines are `holCos U p = if p ∈ Pl then ω else 1`:
`⟨w, Δ_U z⟩ = Σ_{p ∈ plaqIn Ω₀} ⟨curl w p, curl z p⟩ + (ω - 1) b_Pl(w, z)`  for sigma_3 `w, z`, with the `U`-free form
`b_Pl(w, z) = Σ_{p ∈ plaqIn Ω₀ ∩ Pl} ⟨curl_1 w p, curl_1 z p⟩`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverJacobi

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.StatementLaneR6
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

/-- the lemma `inner_deltaKLocCLM_sigma3` is stated with an unused `[CfData]` (section variable); any instance works. -/
local instance cfDefaultInst : CfData := ⟨10, le_refl 10⟩

/-- the flat link configuration. -/
abbrev flatC (L : PeriodicLatticeExtent) : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L :=
  fun _ : Bond L => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)

open Classical in
/-- the `U`-free layer form. -/
noncomputable def bPl (S : Set (PeriodicLatticePlaquette L)) (Pl : Set (PeriodicLatticePlaquette L)) (w z : BondFnL2 L) : ℝ :=
  ∑ p : PeriodicLatticePlaquette L,
    if p ∈ S ∧ p ∈ Pl then hsInner (curlValueCovariant (flatC L) (WithLp.ofLp w) p) (curlValueCovariant (flatC L) (WithLp.ofLp z) p) else 0

open Classical in
/-- the `U`-free base form. -/
noncomputable def bAll (S : Set (PeriodicLatticePlaquette L)) (w z : BondFnL2 L) : ℝ :=
  ∑ p : PeriodicLatticePlaquette L,
    if p ∈ S then hsInner (curlValueCovariant (flatC L) (WithLp.ofLp w) p) (curlValueCovariant (flatC L) (WithLp.ofLp z) p) else 0

open Classical in
theorem delta_form_affine {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U)
    (S Pl : Set (PeriodicLatticePlaquette L)) {ω : ℝ} (hω : ∀ p, holCos U p = if p ∈ Pl then ω else 1)
    {w z : BondFnL2 L} (hw : SigB' w) (hz : SigB' z) :
    (inner ℝ w (deltaKLocCLM U S z) : ℝ) = bAll S w z + (ω - 1) * bPl S Pl w z := by
  classical
  have hzf : ∀ b, diagP (WithLp.ofLp z b) = WithLp.ofLp z b := fun b => by
    have := congrArg (fun g : BondFnL2 L => g b) hz
    simpa [pwDiag_apply] using this
  have hwf : ∀ b, diagP (WithLp.ofLp w b) = WithLp.ofLp w b := fun b => by
    have := congrArg (fun g : BondFnL2 L => g b) hw
    simpa [pwDiag_apply] using this
  have hz' : z = WithLp.toLp 2 (WithLp.ofLp z) := rfl
  rw [hz', AdalyFormal.CoverOmega.inner_deltaKLocCLM_sigma3 hU S w (WithLp.ofLp z) hzf]
  unfold bAll bPl
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [curl_sigma3_flat hU (WithLp.ofLp w) hwf p, curl_sigma3_flat hU (WithLp.ofLp z) hzf p, hω p]
  by_cases hS : p ∈ S <;> by_cases hP : p ∈ Pl <;> simp [hS, hP] <;> ring

/-- the bilinear form of `Ginv` on `E₀`. -/
theorem inner_Ginv_bilin (G : TowerGeom L) (U : Cfg L) (a : ℝ) (Sec : BondSector G) (Jf : BondFnL2 L)
    (x' x : ↥(bondSupp G)) :
    ⟪x', (baseData G U a Sec Jf).Ginv x⟫ =
      ⟪Wop G U a (iE G x'), Delta G U (Wop G U a (iE G x))⟫ + ⟪Tfull G U (iE G x'), Tfull G U (iE G x)⟫ +
        ⟪Sec.Qfull (iE G x'), diagW G (massW G a) (Sec.Qfull (iE G x))⟫ := by
  simp only [BaseDataS.Ginv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, inner_add_right, baseData]
  have h1 : ⟪x', pE G (DpiFull G U a (iE G x))⟫ = ⟪Wop G U a (iE G x'), Delta G U (Wop G U a (iE G x))⟫ := by
    rw [pE_inner_right]
    simp only [DpiFull, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  have h2 : ⟪x', ContinuousLinearMap.adjoint ((Tfull G U).comp (iE G)) (Tfull G U (iE G x))⟫ =
      ⟪Tfull G U (iE G x'), Tfull G U (iE G x)⟫ := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp
  have h3 : ⟪x', pE G (MassFull G a Sec (iE G x))⟫ = ⟪Sec.Qfull (iE G x'), diagW G (massW G a) (Sec.Qfull (iE G x))⟫ := by
    rw [pE_inner_right]
    simp only [MassFull, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [h1, h2, h3]

theorem Wop_sigB' (G : TowerGeom L) {U : Cfg L} (hU : CartanCfg U) (a : ℝ) {x : BondFnL2 L} (hx : SigB' x)
    (hXU : IsUnit (DelpA G U a + (1 - siteMask G.Om0))) : SigB' (Wop G U a x) := by
  simp only [Wop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
  have hds : SigS (gradAdj U x) := gradAdj_sig hU hx
  have hrs : SigS (Rproj G U (gradAdj U x)) := Rproj_sig G hU hds
  have hgs : SigS (Gp G U a (Rproj G U (gradAdj U x))) := Gp_sigS G hU a hrs hXU
  have h1 : pwDiagB L (gradL2 U (Gp G U a (Rproj G U (gradAdj U x)))) = gradL2 U (Gp G U a (Rproj G U (gradAdj U x))) := by
    rw [← gradL2_pwDiag hU]
    exact congrArg (gradL2 U) hgs
  unfold SigB' at *
  rw [map_sub, hx, h1]

open Classical in
theorem Ginv_family_affine (G : TowerGeom L) (a : ℝ) {U U0 : Cfg L} (hU : CartanCfg U) (hU0 : CartanCfg U0)
    (Sec Sec0 : BondSector G) (Jf Jf0 : BondFnL2 L)
    (hXU : IsUnit (DelpA G U a + (1 - siteMask G.Om0))) (hXU0 : IsUnit (DelpA G U0 a + (1 - siteMask G.Om0)))
    (hQfl : ∀ x : BondFnL2 L, SigB' x → Sec.Qfull x = Sec0.Qfull x)
    (Pl : Set (PeriodicLatticePlaquette L)) {ω ω0 : ℝ}
    (hω : ∀ p, holCos U p = if p ∈ Pl then ω else 1) (hω0 : ∀ p, holCos U0 p = if p ∈ Pl then ω0 else 1)
    (x' x : ↥(bondSupp G)) (hx' : SigB' (iE G x')) (hx : SigB' (iE G x)) :
    ⟪x', (baseData G U a Sec Jf).Ginv x⟫ =
      ⟪x', (baseData G U0 a Sec0 Jf0).Ginv x⟫ +
        (ω - ω0) * bPl (plaqIn G.Om0) Pl (Wop G U0 a (iE G x')) (Wop G U0 a (iE G x)) := by
  rw [inner_Ginv_bilin, inner_Ginv_bilin]
  have eW' : Wop G U a (iE G x') = Wop G U0 a (iE G x') := Wop_sig_eq G hU hU0 a hx' hXU hXU0
  have eW : Wop G U a (iE G x) = Wop G U0 a (iE G x) := Wop_sig_eq G hU hU0 a hx hXU hXU0
  have eT' : Tfull G U (iE G x') = Tfull G U0 (iE G x') := Tfull_sig_eq G hU hU0 hx'
  have eT : Tfull G U (iE G x) = Tfull G U0 (iE G x) := Tfull_sig_eq G hU hU0 hx
  have hw' : SigB' (Wop G U0 a (iE G x')) := Wop_sigB' G hU0 a hx' hXU0
  have hw : SigB' (Wop G U0 a (iE G x)) := Wop_sigB' G hU0 a hx hXU0
  have d1 := delta_form_affine hU (plaqIn G.Om0) Pl hω hw' hw
  have d0 := delta_form_affine hU0 (plaqIn G.Om0) Pl hω0 hw' hw
  have eD : ⟪Wop G U0 a (iE G x'), Delta G U (Wop G U0 a (iE G x))⟫ - ⟪Wop G U0 a (iE G x'), Delta G U0 (Wop G U0 a (iE G x))⟫ =
      (ω - ω0) * bPl (plaqIn G.Om0) Pl (Wop G U0 a (iE G x')) (Wop G U0 a (iE G x)) := by
    have e1 : (Delta G U (Wop G U0 a (iE G x)) : BondFnL2 L) = deltaKLocCLM U (plaqIn G.Om0) (Wop G U0 a (iE G x)) := rfl
    have e0 : (Delta G U0 (Wop G U0 a (iE G x)) : BondFnL2 L) = deltaKLocCLM U0 (plaqIn G.Om0) (Wop G U0 a (iE G x)) := rfl
    rw [e1, e0, d1, d0]; ring
  rw [eW', eW, eT', eT, hQfl _ hx', hQfl _ hx]
  linarith [eD]

#print axioms Ginv_family_affine

#print axioms inner_Ginv_bilin

#print axioms delta_form_affine

end AdalyFormal.CoverJacobi
