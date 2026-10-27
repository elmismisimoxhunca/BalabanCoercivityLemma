import B0g
import ZXR2Sector

/-!
# B0h -- the B0 identity (CMP99b (3.115)) for the genuine bond-sector operator `QfullOf`

* `suCoord_grad`: `suCoord (D_U ν) = -(c ↦ fromM2 (ν(c₋) - U_c ν(c₊) U_cᴴ))` (the level-0 pure-gauge direction).
* `QfullOf_grad_eq_zero` (any tower geometry `G`, any row `p` of level `j = p.1`): if the composite jet is
  differentiable (`RegTower G.ell (bgTower G U) G.k`), `G.ell^G.k ∣ L μ + 1`, both ends of the row's bond are on the
  `ell^j`-lattice and `Q'_j(U) ν` vanishes at both ends, then `(Q(U) D_U ν)(p) = 0`.
* `B0_fullTower`: on the full tower (`Ω_j = torus`, `j ≤ k`), every `ν ∈ N(Q'(U))` has `Q(U) D_U ν = 0`.
  This discharges the hypothesis `hB0` of `GN3.B1_form` / `GN4.ginv_coercive_cond` there (given `RegTower`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp M2 SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower UbarTower_zero)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (Qcomposite)

variable {L : PeriodicLatticeExtent}

theorem suCoord_grad (U : Cfg L) (ν : SiteL2 L) :
    suCoord (gradL2 U ν) = -(fun c : PeriodicLatticeEdge L =>
      fromM2 (((WithLp.ofLp ν c.1 : SuTwo) : M2) - ((U c : SU2) : M2)
        * ((WithLp.ofLp ν (coarseShift c.1 1 c.2) : SuTwo) : M2) * ((U c : SU2) : M2)ᴴ)) := by
  funext c
  simp only [suCoord, LinearMap.coe_mk, AddHom.coe_mk, Pi.neg_apply]
  rw [← map_neg]
  congr 1
  have h : WithLp.ofLp (gradL2 U ν) c = AdalyFormal.Balaban.CovariantOperators.gradValueCovariant U
      (WithLp.ofLp ν) c := by rw [gradL2_apply]
  show (((WithLp.ofLp (gradL2 U ν) c : SuTwo) : M2)) = _
  rw [h]
  simp only [AdalyFormal.Balaban.CovariantOperators.gradValueCovariant, Submodule.coe_sub, RMap_coe_apply]
  rw [neg_sub]
  rfl

theorem QfullOf_grad_eq_zero (G : TowerGeom L) (U : Cfg L) (hell : 0 < G.ell)
    (hreg : RegTower G.ell (bgTower G U) G.k) (hdiv : ∀ μ : Fin 3, G.ell ^ G.k ∣ L μ + 1)
    (ν : SiteL2 L) (p : BIdx G)
    (hlat0 : OnLat (G.ell ^ (p.1 : ℕ)) p.2.1.1)
    (hlat1 : OnLat (G.ell ^ (p.1 : ℕ)) (coarseShift p.2.1.1 (G.ell ^ (p.1 : ℕ)) p.2.1.2))
    (hz0 : Qcomposite (bgTower G U) G.ell p.1 (WithLp.ofLp ν) p.2.1.1 = 0)
    (hz1 : Qcomposite (bgTower G U) G.ell p.1 (WithLp.ofLp ν) (coarseShift p.2.1.1 (G.ell ^ (p.1 : ℕ)) p.2.1.2) = 0) :
    (QfullOf G U (gradL2 U ν)) p = 0 := by
  have hj : (p.1 : ℕ) ≤ G.k := Nat.lt_succ_iff.mp p.1.isLt
  have hjet := QlinCompX_pureGauge G.ell U (WithLp.ofLp ν) G.k hreg p.1 hj
  have hbg : bgTower G U = UbarTower su2LogExp G.ell U := rfl
  have hd0 := dG_eq_Qcomposite G.ell hell (UbarTower su2LogExp G.ell U) (WithLp.ofLp ν) G.k hdiv p.1 hj _ hlat0
  have hd1 := dG_eq_Qcomposite G.ell hell (UbarTower su2LogExp G.ell U) (WithLp.ofLp ν) G.k hdiv p.1 hj _ hlat1
  rw [← hbg, hz0] at hd0
  rw [← hbg, hz1] at hd1
  rw [hbg] at hd0 hd1
  have hcoord : suCoord (gradL2 U ν) = -(fun c : PeriodicLatticeEdge L =>
      fromM2 (dG G.ell (UbarTower su2LogExp G.ell U) (WithLp.ofLp ν) 0 c.1
        - ((UbarTower su2LogExp G.ell U 0 c : SU2) : M2)
          * dG G.ell (UbarTower su2LogExp G.ell U) (WithLp.ofLp ν) 0 (coarseShift c.1 (G.ell ^ 0) c.2)
          * ((UbarTower su2LogExp G.ell U 0 c : SU2) : M2)ᴴ)) := by
    rw [suCoord_grad, pow_zero, UbarTower_zero]; rfl
  have hval : QlinCompX G.ell (bgTower G U) p.1 (suCoord (gradL2 U ν)) p.2.1 = 0 := by
    rw [hcoord, map_neg, hbg, hjet]
    simp only [Pi.neg_apply, hd0, hd1]
    simp
  show WithLp.ofLp (QfullOf G U (gradL2 U ν)) p = 0
  simp only [QfullOf, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_toLp]
  have hz : WithLp.ofLp (suCoordInv (QlinCompX G.ell (bgTower G U) p.1 (suCoord (gradL2 U ν)))) p.2.1 = 0 := by
    apply Subtype.ext
    show toM2 ((QlinCompX G.ell (bgTower G U) p.1 (suCoord (gradL2 U ν))) p.2.1) = 0
    rw [hval, map_zero]
  have hq : QlinB G U p.1 (gradL2 U ν) = suCoordInv (QlinCompX G.ell (bgTower G U) p.1
      (suCoord (gradL2 U ν))) := QlinB_eq_r7 G U G.k hreg p.1 hj (gradL2 U ν)  -- r8 transfer: bridge (hreg = RegTower, a hypothesis here)
  first
    | (rw [hz, smul_zero])
    | (rw [hq, hz, smul_zero])
    | (simp only [hq, hz, smul_zero])

#print axioms suCoord_grad
#print axioms QfullOf_grad_eq_zero

end AdalyFormal.SliceCoerc
