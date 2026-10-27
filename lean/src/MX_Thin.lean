import MX_Base
import MX_CJ
import TL22a
import TL1n

/-!
# MX_Thin -- thin-torus lift of the MIXED hybrid class (lane mixed_20261017)

`coversSites_liftΦ`, `coversPlaq_liftΦ` (text copies of TL1m with the covering cube any cube of factor in Φ), `perCube_liftHΦ` (from `perCube_lift` at each factor via `toOrig`/`congr_bound`),
`classCoupled_liftHΦ`, `geometry_liftHΦ` (AC_Thin.geometry_liftH for Φ), `jetReg_of_classHΦ`, `unitReg_of_classHΦ` (TL22a with the mixed `classRows_readΦ`, `classRows_unitΦ`).
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
namespace MXP.Thin
open AdalyFormal.Thin
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.IngredientFamilyR2
open MXP.AllC

theorem coversSites_liftΦ {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (hstrict : ∀ μ : Fin 3, L μ + 1 < Lt μ + 1)
    {ell M R k : ℕ} {Φ : Set ℕ} [CubeFactorSet Φ] {S : Tower L} (hS : Admissible ell M R k S) 
    (hCov : CoversOmcΦ ell M Φ k S) : CoversOmcΦ ell M Φ k (liftTower h S) := by
  intro x hx
  obtain ⟨C, j, hCΦ, hxC⟩ := hCov (projS h x) hx
  obtain ⟨c, hcΦ, hC⟩ := hCΦ
  have hc : 2 ≤ c := by have := CubeFactorSet.ge (Φ := Φ) c hcΦ; omega
  obtain ⟨hj, ⟨z, hgrid, rfl⟩, -, -⟩ := hC.1
  have hb := bigSide_pos hS hj
  have hbs : bigSide M ell j < c * bigSide M ell j := by nlinarith
  obtain ⟨zt, hgt, hcomp, hper⟩ := corner_site h hstrict (bigSide M ell j) (c * bigSide M ell j) hb hbs
    (fun μ => hS.2.2.1 j hj μ) z hgrid x (fun _ => 0) (fun μ => hxC μ) (fun μ hp => by simp at hp)
  have hdesc := described_lift h hC.1 hgt hcomp
  exact ⟨siteBox zt (c * bigSide M ell j), j,
    ⟨c, hcΦ, isClassCube_of_described (S := liftTower h S) (liftTower_mono h hS.1) hdesc⟩, fun μ => (hper μ).1⟩

theorem coversPlaq_liftΦ {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (hstrict : ∀ μ : Fin 3, L μ + 1 < Lt μ + 1)
    {ell M R k : ℕ} {Φ : Set ℕ} [CubeFactorSet Φ] {S : Tower L} (hS : Admissible ell M R k S) 
    (hCov : CoversPlaqΦ ell M Φ k S) : CoversPlaqΦ ell M Φ k (liftTower h S) := by
  intro pt hpt
  obtain ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩ := pt
  let p : PeriodicLatticePlaquette L := (projS h x, ⟨(μ, ν), hμν⟩)
  have hbd : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e := by
    intro e he
    rw [edge_mem'] at he
    have m1 := cubeBond_om_lift h (hpt (x, μ) ((edge_mem' _ _).mpr (Or.inl rfl)))
    have m2 := cubeBond_om_lift h (hpt (periodicLatticeShift x μ, ν) ((edge_mem' _ _).mpr (Or.inr (Or.inl rfl))))
    have m3 := cubeBond_om_lift h (hpt (periodicLatticeShift x ν, μ) ((edge_mem' _ _).mpr (Or.inr (Or.inr (Or.inl rfl)))))
    have m4 := cubeBond_om_lift h (hpt (x, ν) ((edge_mem' _ _).mpr (Or.inr (Or.inr (Or.inr rfl)))))
    simp only [projE, projS_shift] at m1 m2 m3 m4
    rcases he with rfl | rfl | rfl | rfl
    · exact m1
    · exact m2
    · exact m3
    · exact m4
  obtain ⟨C, j, hCΦ, hall⟩ := hCov p hbd
  obtain ⟨c, hcΦ, hC⟩ := hCΦ
  have hc : 2 ≤ c := by have := CubeFactorSet.ge (Φ := Φ) c hcΦ; omega
  obtain ⟨hj, ⟨z, hgrid, rfl⟩, -, -⟩ := hC.1
  have hb := bigSide_pos hS hj
  have hbs : bigSide M ell j < c * bigSide M ell j := by nlinarith
  have hne : ν ≠ μ := ne_of_gt hμν
  have c1 := hall (projS h x, μ) ((edge_mem' _ _).mpr (Or.inl rfl))
  have c4 := hall (projS h x, ν) ((edge_mem' _ _).mpr (Or.inr (Or.inr (Or.inr rfl))))
  have proj_succ : ∀ ρ : Fin 3, ((projS h x ρ).val + 1) % (L ρ + 1) = ((x ρ).val + 1) % (L ρ + 1) := by
    intro ρ; simp only [projS_val]; rw [Nat.mod_add_mod]
  obtain ⟨zt, hgt, hcomp, hper⟩ := corner_site h hstrict (bigSide M ell j) (c * bigSide M ell j) hb hbs
    (fun ρ => hS.2.2.1 j hj ρ) z hgrid x (fun ρ => if ρ = μ ∨ ρ = ν then 1 else 0)
    (fun ρ => c1.1 ρ) (fun ρ hρ => by
      by_cases h1 : ρ = μ
      · subst h1
        have := c1.2 ρ
        simp only [periodicLatticeShift, Function.update_self, fin_add_one_val] at this
        rw [← proj_succ]; exact this
      · have h2 : ρ = ν := by
          by_contra h2; simp [h1, h2] at hρ
        subst h2
        have := c4.2 ρ
        simp only [periodicLatticeShift, Function.update_self, fin_add_one_val] at this
        rw [← proj_succ]; exact this)
  have hdesc := described_lift h hC.1 hgt hcomp
  refine ⟨siteBox zt (c * bigSide M ell j), j,
    ⟨c, hcΦ, isClassCube_of_described (S := liftTower h S) (liftTower_mono h hS.1) hdesc⟩, ?_⟩
  have hb0 : ∀ ρ : Fin 3, off (Lt ρ + 1) (zt ρ).val (x ρ).val < c * bigSide M ell j := fun ρ => (hper ρ).1
  have hflag : ∀ ρ : Fin 3, (ρ = μ ∨ ρ = ν) → off (Lt ρ + 1) (zt ρ).val (((x ρ).val + 1) % (Lt ρ + 1)) < c * bigSide M ell j :=
    fun ρ hρ => (hper ρ).2 (by simp [hρ])
  have hbm := inBox_shift hb0 μ (hflag μ (Or.inl rfl))
  have hbn := inBox_shift hb0 ν (hflag ν (Or.inr rfl))
  have hbmn := inBox_shift hbm ν (by
    have : (periodicLatticeShift x μ) ν = x ν := by simp [periodicLatticeShift, Function.update_of_ne hne]
    rw [this]; exact hflag ν (Or.inr rfl))
  have hbnm := inBox_shift hbn μ (by
    have : (periodicLatticeShift x ν) μ = x μ := by simp [periodicLatticeShift, Function.update_of_ne hne.symm]
    rw [this]; exact hflag μ (Or.inl rfl))
  intro e he
  rw [edge_mem'] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨hb0, hbm⟩
  · exact ⟨hbm, hbmn⟩
  · exact ⟨hbn, hbnm⟩
  · exact ⟨hb0, hbn⟩


theorem perCube_liftHΦ {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell M R b k : ℕ} {Φ : Set ℕ} [CubeFactorSet Φ] {S : Tower L}
    {α₀ η : ℝ} {U : LinkCfg L} (hS : Admissible ell M R k S) (hU : PerCubeRegular2HΦ ell M Φ b k S α₀ η U) :
    PerCubeRegular2HΦ ell M Φ b k (liftTower h S) α₀ η (liftU h U) := by
  intro f hf
  have hfpos := CubeFactorSet.pos hf
  have e := AdalyFormal.AllC.bound_eq (M := M) (b := b) hfpos α₀
  have h4 := perCube_lift h hS ((hU f hf).toOrig hfpos)
  exact (AdalyFormal.AllC.PerCubeRegular2H.congr_bound (b := f) (b' := b) (α₀ := (b : ℝ) * α₀ / f) (α₀' := α₀) e).1 h4

theorem classCoupled_liftHΦ {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (hstrict : ∀ μ : Fin 3, L μ + 1 < Lt μ + 1)
    {ell M R b k : ℕ} {Φ : Set ℕ} [CubeFactorSet Φ] {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} (hS : Admissible ell M R k S)
    (hCU : ClassCoupledHΦ ell M Φ b k S α₀ η U) :
    ClassCoupledHΦ ell M Φ b k (liftTower h S) α₀ η (liftU h U) :=
  ⟨⟨coversSites_liftΦ h hstrict hS hCU.1.1, coversPlaq_liftΦ h hstrict hS hCU.1.2⟩, perCube_liftHΦ h hS hCU.2⟩

theorem geometry_liftHΦ {ell M R b k : ℕ} {Φ : Set ℕ} [CubeFactorSet Φ] {hell : 0 < ell} {Lut Lu : PeriodicLatticeExtent}
    (g : GeomLift ell k hell Lut Lu)
    (hT : TorusOK ell M Lu) {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK2 ell M R k S Lam)
    {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)}
    (hCU : ClassCoupledHΦ ell M Φ b k S α₀ ((ell : ℝ) ^ k)⁻¹ U) :
    TorusOK ell M Lut ∧ Admissible ell M R k (liftTower g.fine S) ∧
      LambdaOK2 ell M R k (liftTower g.fine S) (projS g.cover ⁻¹' Lam) ∧
      ClassCoupledHΦ ell M Φ b k (liftTower g.fine S) α₀ ((ell : ℝ) ^ k)⁻¹ (liftU g.fine U) :=
  ⟨torusOK_lift g.cover hT, admissible_lift g.fine hS,
    ⟨lambdaOK_lift g.cover hell hT hL.1, lamBlockSum_lift g.cover hell hT.1 hL.2⟩,
    classCoupled_liftHΦ g.fine (covers_scaleUp_strict ell k hell g.strict) hS hCU⟩

section reg
open AdalyFormal.ClassJets (ClassSmall ReadRow classRows_read classRows_unit)

theorem jetReg_of_classHΦ {ell M R k bf : ℕ} {Φ : Set ℕ} [CubeFactorSet Φ] {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ}
    {U : LinkCfg (scaleUp ell k Lu)} (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S)
    (hT : TorusOK ell M Lu) (hU : ClassCoupledHΦ ell M Φ bf k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hsm : ClassSmall ell ((bf : ℝ) * M * α₀)) :
    JetReg ell k S (UbarTower su2LogExp ell U) := by
  intro j hj b hb l e hr
  have hj1 : 1 ≤ j := by
    have := hr.1
    omega
  exact (MXP.ClassJets.classRows_readΦ hell hroom hS hT hU hsm hj1 hj hb hr).of_le (by exact_mod_cast le_top)

theorem unitReg_of_classHΦ {Lut Lu : PeriodicLatticeExtent} (hu : Covers Lut Lu) {ell M R k bf : ℕ} {Φ : Set ℕ} [CubeFactorSet Φ] (hell0 : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) {α₀ : ℝ}
    (hell : 2 ≤ ell) (hk : 1 ≤ k) (hroom : 17 * ell ≤ R * M)
    (hS : Admissible ell M R k (towerPull (covers_scaleUp ell k hell0 hu) (fun _ => 0) S)) (hT : TorusOK ell M Lut)
    (hL : LambdaOK2 ell M R k (towerPull (covers_scaleUp ell k hell0 hu) (fun _ => 0) S) (phiS hu (fun _ => 0) ⁻¹' Lam))
    (hU : ClassCoupledHΦ ell M Φ bf k (towerPull (covers_scaleUp ell k hell0 hu) (fun _ => 0) S) α₀ ((ell : ℝ) ^ k)⁻¹
      (pullCfg (covers_scaleUp ell k hell0 hu) (fun _ => 0) U))
    (hsm : ClassSmall ell ((bf : ℝ) * M * α₀)) :
    UnitReg hu hell0 S U a Lam := by
  intro cb hc
  exact (MXP.ClassJets.classRows_unitΦ hell0 hell hk hroom hS hT hL hU hsm cb hc).of_le (by exact_mod_cast le_top)

end reg

end MXP.Thin

#print axioms MXP.Thin.geometry_liftHΦ
#print axioms MXP.Thin.jetReg_of_classHΦ
#print axioms MXP.Thin.unitReg_of_classHΦ
