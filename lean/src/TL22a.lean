import TL21b
import OG10
import CJ5

/-!
# TL22a -- supplying `CoverHyp` at a class configuration of the large torus.

* `guardsUnit_of_fields` : `GuardsUnit` (units of `Δ'_a|Ω₀ + (1-Ω₀)`, `Ginv`, `Q G Q*`) from `SiteS1`, the coercivity `hcoer`
  and injectivity of `Q*` (the three guards of `WellDefG`).
* `jetReg_of_class`, `unitReg_of_class` : read-restricted regularity from CJ4/CJ5 (the class supplies it only on read rows).
* `coverHyp_of_wd` : `CoverHyp` from `WellDefG` of the lifted parameters and the two regularities.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.IngredientFamilyR2

section gu
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
  (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))

theorem guardsUnit_of_fields {cs cw : ℝ} (hcs0 : 0 < cs) (hcs1 : cs ≤ 1)
    (hS1 : AdalyFormal.M2Skel.SiteS1 ell k S U a cs) (hcw : 0 < cw)
    (hcoer : ∀ A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
      cw * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
        ≤ ⟪A, (gparams ell k Lu hell S U a Lam).data.Ginv A⟫)
    (hQs : Function.Injective (gparams ell k Lu hell S U a Lam).data.Qs) :
    GenP.GuardsUnit (gparams ell k Lu hell S U a Lam) := by
  have hl : (0 : ℝ) < ell := by exact_mod_cast hell
  have hc : 0 < cw * (((ell : ℝ) ^ k)⁻¹ ^ 2) := by positivity
  have hco : ∀ x : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
      (cw * (((ell : ℝ) ^ k)⁻¹ ^ 2)) * ‖x‖ ^ 2 ≤ ⟪x, (gparams ell k Lu hell S U a Lam).data.Ginv x⟫ := by
    intro x
    have h1 := AdalyFormal.M1IMS.wnormSq_ge S (show 1 ≤ ell from hell) k (x : BondFnL2 (scaleUp ell k Lu))
    have h2 := hcoer x
    have h3 : ‖(x : BondFnL2 (scaleUp ell k Lu))‖ = ‖x‖ := rfl
    rw [h3] at h1
    calc (cw * (((ell : ℝ) ^ k)⁻¹ ^ 2)) * ‖x‖ ^ 2 = cw * ((((ell : ℝ) ^ k)⁻¹) ^ 2 * ‖x‖ ^ 2) := by ring
      _ ≤ cw * AdalyFormal.M1.wnormSq S ell k (x : BondFnL2 (scaleUp ell k Lu)) := mul_le_mul_of_nonneg_left h1 hcw.le
      _ ≤ _ := h2
  refine ⟨?_, ?_, ?_⟩
  · exact AdalyFormal.M2Skel.isUnit_LP_of_S1 (geomOf ell k S) (show 1 ≤ (geomOf ell k S).ell from hell) U a cs hcs0 hcs1 hS1
  · exact isUnit_of_coercive _ hc hco
  · exact isUnit_Q_inv_Qs (fun x y => (gparams ell k Lu hell S U a Lam).data.Ginv_symm
      (gparams ell k Lu hell S U a Lam).data_laws x y) hc hco (gparams ell k Lu hell S U a Lam).data.Q_adj hQs

end gu

section reg
open AdalyFormal.ClassJets (ClassSmall ReadRow classRows_read classRows_unit)

theorem jetReg_of_class {ell M R k c : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ}
    {U : LinkCfg (scaleUp ell k Lu)} (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S)
    (hT : TorusOK ell M Lu) (hU : ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hsm : ClassSmall ell ((c : ℝ) * M * α₀)) :
    JetReg ell k S (UbarTower su2LogExp ell U) := by
  intro j hj b hb l e hr
  have hj1 : 1 ≤ j := by
    have := hr.1
    omega
  exact (classRows_read hell hroom hS hT hU hsm hj1 hj hb hr).of_le (by exact_mod_cast le_top)

theorem unitReg_of_class {Lut Lu : PeriodicLatticeExtent} (hu : Covers Lut Lu) {ell M R k c : ℕ} (hell0 : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) {α₀ : ℝ}
    (hell : 2 ≤ ell) (hk : 1 ≤ k) (hroom : 17 * ell ≤ R * M)
    (hS : Admissible ell M R k (towerPull (covers_scaleUp ell k hell0 hu) (fun _ => 0) S)) (hT : TorusOK ell M Lut)
    (hL : LambdaOK2 ell M R k (towerPull (covers_scaleUp ell k hell0 hu) (fun _ => 0) S) (phiS hu (fun _ => 0) ⁻¹' Lam))
    (hU : ClassCoupled ell M c k (towerPull (covers_scaleUp ell k hell0 hu) (fun _ => 0) S) α₀ ((ell : ℝ) ^ k)⁻¹
      (pullCfg (covers_scaleUp ell k hell0 hu) (fun _ => 0) U))
    (hsm : ClassSmall ell ((c : ℝ) * M * α₀)) :
    UnitReg hu hell0 S U a Lam := by
  intro cb hc
  exact (classRows_unit hell0 hell hk hroom hS hT hL hU hsm cb hc).of_le (by exact_mod_cast le_top)

end reg

theorem coverHyp_of_wd {Lut Lu : PeriodicLatticeExtent} (hu : Covers Lut Lu) {ell k : ℕ} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hp : PhiOK (covers_scaleUp ell k hell hu) (fun _ => 0) (ell ^ k))
    (hT1 : ∀ μ : Fin 3, ell ∣ Lu μ + 1)
    (hreg : JetReg ell k (towerPull (covers_scaleUp ell k hell hu) (fun _ => 0) S)
      (UbarTower su2LogExp ell (pullCfg (covers_scaleUp ell k hell hu) (fun _ => 0) U)))
    (hureg : UnitReg hu hell S U a Lam) (hWD : GenP.WellDefG (Pt hu hell S U a Lam)) :
    CoverHyp hu hell S U a Lam hp :=
  ⟨hT1, hreg, hureg, hWD.2.1, hWD.2.2.1, hWD.2.2.2, hWD.1.2.1, hWD.1.2.2, hWD.1.1⟩

end AdalyFormal.Thin

#print axioms AdalyFormal.Thin.guardsUnit_of_fields
#print axioms AdalyFormal.Thin.jetReg_of_class
#print axioms AdalyFormal.Thin.unitReg_of_class
#print axioms AdalyFormal.Thin.coverHyp_of_wd
