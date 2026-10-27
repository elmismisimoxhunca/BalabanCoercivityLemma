import TL20a

/-!
# TL20b -- unit-level objects of the genuine ingredient family are natural
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.IngredientFamilyR2

section unitlv
variable {Lut Lu : PeriodicLatticeExtent} (hu : Covers Lut Lu) {ell k : ℕ} (hell : 0 < ell)
variable (S : Tower (scaleUp ell k Lu)) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))

/-- the data of the lifted parameter set -/
noncomputable abbrev Pt : IngrBParams :=
  gparams ell k Lut hell (towerPull (covers_scaleUp ell k hell hu) (fun _ => 0) S)
    (pullCfg (covers_scaleUp ell k hell hu) (fun _ => 0) U) a (phiS hu (fun _ => 0) ⁻¹' Lam)

noncomputable abbrev P0 : IngrBParams := gparams ell k Lu hell S U a Lam

theorem unitBgU_nat (hp : PhiOK (covers_scaleUp ell k hell hu) (fun _ => 0) (ell ^ k)) :
    (Pt hu hell S U a Lam).unitBgU = fun e => (P0 hell S U a Lam).unitBgU (phiE hu (fun _ => 0) e) := by
  have hbg : AgreeAligned (covers_scaleUp ell k hell hu) (fun _ => 0) (ell ^ k)
      (UbarTower su2LogExp ell (pullCfg (covers_scaleUp ell k hell hu) (fun _ => 0) U) k) (UbarTower su2LogExp ell U k) :=
    UbarTower_nat su2LogExp hell U k hp
  have := unitBg_nat hu ell k hell (fun _ => 0) (by simpa using hp) (by simpa using hbg)
  exact this

/-- `C²` regularity of the unit-level one-step averaging rows at the cover -/
def UnitReg : Prop :=
  ∀ c : CoarseBond Lut ell, CRowIn ell (phiS hu (fun _ => 0) ⁻¹' Lam) c →
    ContDiffAt ℝ 2 (qStepComp 1 ell (Pt hu hell S U a Lam).unitBgU (c.1.1, c.2)) 0

theorem phiOK_unit (hT : TorusOK ell 1 Lu) : PhiOK hu (fun _ => 0) ell := ⟨hT.1, fun _ => dvd_zero _⟩

theorem Q1_nat (hT1 : ∀ μ : Fin 3, ell ∣ Lu μ + 1) (hpk : PhiOK (covers_scaleUp ell k hell hu) (fun _ => 0) (ell ^ k))
    (hreg : UnitReg hu hell S U a Lam) (B : Bond Lu → SuTwo) (c : CoarseBond Lut ell)
    (hc : CRowIn ell (phiS hu (fun _ => 0) ⁻¹' Lam) c) :
    (Pt hu hell S U a Lam).Q1 (fun e => B (phiE hu (fun _ => 0) e)) c =
      (P0 hell S U a Lam).Q1 B (cbMap (hu := hu) (o := fun _ => 0) ⟨hT1, fun _ => dvd_zero _⟩ c) := by
  have hU := unitBgU_nat hu hell S U a Lam hpk
  show Q1jet ell (Pt hu hell S U a Lam).unitBgU _ c = Q1jet ell (P0 hell S U a Lam).unitBgU B _
  exact Q1jet_nat ⟨hT1, fun _ => dvd_zero _⟩ hell (fun e _ => by rw [hU]) B c
    ((hreg c hc).differentiableAt (by norm_num))

end unitlv


end AdalyFormal.Thin
