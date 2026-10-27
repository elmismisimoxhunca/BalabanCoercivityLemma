import MXQ_Base
import MXQ_CJ
import TL22a
import TL1n

/-!
# MXQ_Thin -- thin-torus lift of the FAMILY class (lane mixed_20261017, round 2)

`liftFam L Fm` : the lifted family on a covering torus: a triple `(sites', j, f)` belongs to it iff `sites'` projects ONTO a member `(sites0, j, f)` of `Fm L`.
`coversSites_liftQ`, `coversPlaq_liftQ` (text copies of TL1m; the lifted cube projects onto the covering base cube), `regBody_lift` (tail of TL1l.perCube_lift at ONE cube),
`perCube_liftHQ`, `classCoupled_liftHQ`, `geometry_liftHQ`, `jetReg_of_classHQ`, `unitReg_of_classHQ` (TL22a with `classRows_readΦ`, `classRows_unitΦ`).
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
namespace MXQ.Thin
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
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open MXQ.AllC

/-- membership in the lifted family. -/
def LiftMem (L : PeriodicLatticeExtent) (Fm : CF) {L'' : PeriodicLatticeExtent} (t : Set (PeriodicLatticeSite L'') × ℕ × ℕ) : Prop :=
  ∃ (hLL : Covers L'' L) (sites0 : Set (PeriodicLatticeSite L)), (sites0, t.2.1, t.2.2) ∈ Fm L ∧
    (∀ x ∈ t.1, projS hLL x ∈ sites0) ∧ (∀ y ∈ sites0, ∃ x ∈ t.1, projS hLL x = y)

def liftFam (L : PeriodicLatticeExtent) (Fm : CF) : CF := fun _ => {t | LiftMem L Fm t}

theorem mem_liftFam {L : PeriodicLatticeExtent} {Fm : CF} {L'' : PeriodicLatticeExtent} {s : Set (PeriodicLatticeSite L'')} {j f : ℕ} :
    (s, j, f) ∈ liftFam L Fm L'' ↔ ∃ (hLL : Covers L'' L) (sites0 : Set (PeriodicLatticeSite L)), (sites0, j, f) ∈ Fm L ∧
      (∀ x ∈ s, projS hLL x ∈ sites0) ∧ (∀ y ∈ sites0, ∃ x ∈ s, projS hLL x = y) := Iff.rfl

instance liftFam_ok {L : PeriodicLatticeExtent} {Fm : CF} [h : CubeFamOK Fm] : CubeFamOK (liftFam L Fm) :=
  ⟨fun L'' s j f hm => by
    obtain ⟨hLL, s0, hm0, -, -⟩ := (mem_liftFam).1 hm
    exact h.ge L s0 j f hm0⟩

theorem coversSites_liftQ {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (hstrict : ∀ μ : Fin 3, L μ + 1 < Lt μ + 1)
    {ell M R k : ℕ} {Fm : CF} [CubeFamOK Fm] {S : Tower L} (hS : Admissible ell M R k S) 
    (hCov : CoversOmcQ ell M Fm k S) : CoversOmcQ ell M (liftFam L Fm) k (liftTower h S) := by
  intro x hx
  obtain ⟨C, j, hCΦ, hxC⟩ := hCov (projS h x) hx
  obtain ⟨c, hcΦ, hC⟩ := hCΦ
  have hc : 2 ≤ c := by have := CubeFamOK.ge _ _ _ _ hcΦ; omega
  obtain ⟨hj, ⟨z, hgrid, rfl⟩, -, -⟩ := hC.1
  have hb := bigSide_pos hS hj
  have hbs : bigSide M ell j < c * bigSide M ell j := by nlinarith
  obtain ⟨zt, hgt, hcomp, hper⟩ := corner_site h hstrict (bigSide M ell j) (c * bigSide M ell j) hb hbs
    (fun μ => hS.2.2.1 j hj μ) z hgrid x (fun _ => 0) (fun μ => hxC μ) (fun μ hp => by simp at hp)
  have hdesc := described_lift h hC.1 hgt hcomp
  exact ⟨siteBox zt (c * bigSide M ell j), j,
    ⟨c, (mem_liftFam).2 ⟨h, siteBox z (c * bigSide M ell j), hcΦ, fun x hx => compat_subset h hcomp hx, fun y hy => compat_surj h hcomp hy⟩,
      isClassCube_of_described (S := liftTower h S) (liftTower_mono h hS.1) hdesc⟩, fun μ => (hper μ).1⟩

theorem coversPlaq_liftQ {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (hstrict : ∀ μ : Fin 3, L μ + 1 < Lt μ + 1)
    {ell M R k : ℕ} {Fm : CF} [CubeFamOK Fm] {S : Tower L} (hS : Admissible ell M R k S) 
    (hCov : CoversPlaqQ ell M Fm k S) : CoversPlaqQ ell M (liftFam L Fm) k (liftTower h S) := by
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
  have hc : 2 ≤ c := by have := CubeFamOK.ge _ _ _ _ hcΦ; omega
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
    ⟨c, (mem_liftFam).2 ⟨h, siteBox z (c * bigSide M ell j), hcΦ, fun x hx => compat_subset h hcomp hx, fun y hy => compat_surj h hcomp hy⟩,
      isClassCube_of_described (S := liftTower h S) (liftTower_mono h hS.1) hdesc⟩, ?_⟩
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


theorem regBody_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell M b : ℕ} {zt : PeriodicLatticeSite Lt} {s j : ℕ}
    {α₀ η : ℝ} {U : LinkCfg L} (hReg : RegBodyH ell M b (siteBox (projS h zt) s) j α₀ η U) :
    RegBodyH ell M b (siteBox zt s) j α₀ η (liftU h U) := by
  obtain ⟨g, A, hA1, hA2, hA3⟩ := hReg
  refine ⟨fun x => g (projS h x), liftA h A, fun e he => ?_, fun μ ν x hx1 hx2 => ?_, fun μ x hx => ?_⟩
  · obtain ⟨c1, c2, c3⟩ := hA1 (projE h e) (cubeBond_lift h he)
    refine ⟨c1, ?_, c3⟩
    rw [gauge_lift]; exact c2
  · have hx1' := cubeBond_lift h hx1
    have hx2' := cubeBond_lift h hx2
    simp only [projE, projS_shift] at hx1' hx2'
    have := hA2 μ ν (projS h x) hx1' hx2'
    simp only [liftA, projE, projS_shift]
    exact this
  · have := hA3 μ (projS h x) (fun ν hν => by
      have h1 := curlReads_lift h (hx ν hν).1
      have h2 := curlReads_lift h (hx ν hν).2
      rw [projS_shiftBack] at h1
      exact ⟨h1, h2⟩)
    rw [ddA_lift]; exact this

theorem perCube_liftHQ {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell M R b k : ℕ} {Fm : CF} [CubeFamOK Fm] {S : Tower L}
    {α₀ η : ℝ} {U : LinkCfg L} (hS : Admissible ell M R k S) (hU : PerCubeRegular2HQ ell M Fm b k S α₀ η U) :
    PerCubeRegular2HQ ell M (liftFam L Fm) b k (liftTower h S) α₀ η (liftU h U) := by
  intro f Ct j hmem hCt
  obtain ⟨hLL, sites0, hm0, hsub, hsurj⟩ := (mem_liftFam).1 hmem
  obtain ⟨hmono, -, hbd, -, -, -⟩ := hS
  obtain ⟨hj, ⟨zt, hgrid, rfl⟩, hsub', ⟨y, hy1, hy2⟩⟩ := hCt.1
  set s := f * bigSide M ell j with hs
  have hgrid' : GridCorner (bigSide M ell j) (projS h zt) := by
    intro μ
    show (zt μ).val % (L μ + 1) % bigSide M ell j = 0
    rw [Nat.mod_mod_of_dvd _ (hbd j hj μ)]; exact hgrid μ
  have hdesc : DescribedAt ell M f k S (siteBox (projS h zt) s) j := by
    refine ⟨hj, ⟨_, hgrid', rfl⟩, fun x hx => ?_, ?_⟩
    · obtain ⟨xt, hxt, hxx⟩ := box_proj_surj h zt x s hx
      have := hsub' hxt
      rw [← hxx]; exact this
    · exact ⟨projS h y, box_proj_subset h zt y s hy1, hy2⟩
  have hset : sites0 = siteBox (projS h zt) s := by
    ext y'
    constructor
    · intro hy'
      obtain ⟨x, hx, hxy⟩ := hsurj y' hy'
      have := box_proj_subset h zt x s hx
      rw [← hxy]; exact this
    · intro hy'
      obtain ⟨x, hx, hxy⟩ := box_proj_surj h zt y' s hy'
      have := hsub x hx
      rw [← hxy]; exact this
  have hq0 : IsClassCube ell M f k S (siteBox (projS h zt) s) j := isClassCube_of_described hmono hdesc
  have hm0' : (siteBox (projS h zt) s, j, f) ∈ Fm L := by rw [← hset]; exact hm0
  exact regBody_lift h (hU f _ j hm0' hq0)

theorem classCoupled_liftHQ {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (hstrict : ∀ μ : Fin 3, L μ + 1 < Lt μ + 1)
    {ell M R b k : ℕ} {Fm : CF} [CubeFamOK Fm] {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} (hS : Admissible ell M R k S)
    (hCU : ClassCoupledHQ ell M Fm b k S α₀ η U) :
    ClassCoupledHQ ell M (liftFam L Fm) b k (liftTower h S) α₀ η (liftU h U) :=
  ⟨⟨coversSites_liftQ h hstrict hS hCU.1.1, coversPlaq_liftQ h hstrict hS hCU.1.2⟩, perCube_liftHQ h hS hCU.2⟩

theorem geometry_liftHQ {ell M R b k : ℕ} {Fm : CF} [CubeFamOK Fm] {hell : 0 < ell} {Lut Lu : PeriodicLatticeExtent}
    (g : GeomLift ell k hell Lut Lu)
    (hT : TorusOK ell M Lu) {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK2 ell M R k S Lam)
    {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)}
    (hCU : ClassCoupledHQ ell M Fm b k S α₀ ((ell : ℝ) ^ k)⁻¹ U) :
    TorusOK ell M Lut ∧ Admissible ell M R k (liftTower g.fine S) ∧
      LambdaOK2 ell M R k (liftTower g.fine S) (projS g.cover ⁻¹' Lam) ∧
      ClassCoupledHQ ell M (liftFam (scaleUp ell k Lu) Fm) b k (liftTower g.fine S) α₀ ((ell : ℝ) ^ k)⁻¹ (liftU g.fine U) :=
  ⟨torusOK_lift g.cover hT, admissible_lift g.fine hS,
    ⟨lambdaOK_lift g.cover hell hT hL.1, lamBlockSum_lift g.cover hell hT.1 hL.2⟩,
    classCoupled_liftHQ g.fine (covers_scaleUp_strict ell k hell g.strict) hS hCU⟩

section reg
open AdalyFormal.ClassJets (ClassSmall ReadRow classRows_read classRows_unit)

theorem jetReg_of_classHQ {ell M R k bf : ℕ} {Fm : CF} [CubeFamOK Fm] {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ}
    {U : LinkCfg (scaleUp ell k Lu)} (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S)
    (hT : TorusOK ell M Lu) (hU : ClassCoupledHQ ell M Fm bf k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hsm : ClassSmall ell ((bf : ℝ) * M * α₀)) :
    JetReg ell k S (UbarTower su2LogExp ell U) := by
  intro j hj b hb l e hr
  have hj1 : 1 ≤ j := by
    have := hr.1
    omega
  exact (MXQ.ClassJets.classRows_readΦ hell hroom hS hT hU hsm hj1 hj hb hr).of_le (by exact_mod_cast le_top)

theorem unitReg_of_classHQ {Lut Lu : PeriodicLatticeExtent} (hu : Covers Lut Lu) {ell M R k bf : ℕ} {Fm : CF} [CubeFamOK Fm] (hell0 : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) {α₀ : ℝ}
    (hell : 2 ≤ ell) (hk : 1 ≤ k) (hroom : 17 * ell ≤ R * M)
    (hS : Admissible ell M R k (towerPull (covers_scaleUp ell k hell0 hu) (fun _ => 0) S)) (hT : TorusOK ell M Lut)
    (hL : LambdaOK2 ell M R k (towerPull (covers_scaleUp ell k hell0 hu) (fun _ => 0) S) (phiS hu (fun _ => 0) ⁻¹' Lam))
    (hU : ClassCoupledHQ ell M Fm bf k (towerPull (covers_scaleUp ell k hell0 hu) (fun _ => 0) S) α₀ ((ell : ℝ) ^ k)⁻¹
      (pullCfg (covers_scaleUp ell k hell0 hu) (fun _ => 0) U))
    (hsm : ClassSmall ell ((bf : ℝ) * M * α₀)) :
    UnitReg hu hell0 S U a Lam := by
  intro cb hc
  exact (MXQ.ClassJets.classRows_unitΦ hell0 hell hk hroom hS hT hL hU hsm cb hc).of_le (by exact_mod_cast le_top)

end reg

end MXQ.Thin

#print axioms MXQ.Thin.geometry_liftHQ
#print axioms MXQ.Thin.jetReg_of_classHQ
#print axioms MXQ.Thin.unitReg_of_classHQ
