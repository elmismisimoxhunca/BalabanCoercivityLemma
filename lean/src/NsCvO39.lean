import NsCvO38
import NsCvO35

/-!
# CvO39 -- sums over `BIdx`, `QlinB` on sigma_3-valued fields, and the row pairing (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverNested (cartan cartan_coe)
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)

variable {L : PeriodicLatticeExtent}

open Classical in
theorem sum_BIdx (G : TowerGeom L) (F : Fin (G.k + 1) → Bond L → ℝ) :
    ∑ p : BIdx G, F p.1 p.2.1 = ∑ j : Fin (G.k + 1), ∑ b : Bond L, (if b ∈ bondsLam G j then F j b else 0) := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun b : Bond L => b ∈ bondsLam G j)) (by simp) (fun b => F j b)).symm

theorem suCoordInv_thetaOf (A : BondFnL2 L) (hA : SigB (WithLp.ofLp A)) : (suCoordInv (aF (thetaOf (WithLp.ofLp A))) : BondFnL2 L) = A := by
  rw [← suCoord_sig A hA, suCoordInv_suCoord]

/-- **`QlinB` on an arbitrary sigma_3-valued field** along the staggered path (levels `0,1,2`). -/
theorem QlinB_sig (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : StagPar L ell) (hell : 0 < ell)
    (c : ℕ) (t : ℝ) (htπ : |t| < tcap ell) (hc1 : ell ≤ c) (hc2 : c + ell * ell < L 0 + 1)
    (G : TowerGeom L) (hG : G.ell = ell) (j : ℕ) (hj : j ≤ 2) (A : BondFnL2 L) (hA : SigB (WithLp.ofLp A)) :
    QlinB G (stagCfg c t) j A = suCoordInv (aF (thetaSeq ell j (thetaOf (WithLp.ofLp A)))) := by
  have hreg := stag_regTower_u hN hE hell c t htπ hc1 hc2
  have e : bgTower G (stagCfg c t : Cfg L) = UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) := by
    unfold bgTower; rw [hG]
  obtain ⟨q1, q2, -, -⟩ := stag_levels_sigma3 hN hE hell c t htπ hc1 hc2 (thetaOf (WithLp.ofLp A))
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with h0 | h1 | h2
  · subst h0
    rw [QlinB_zero]
    exact (suCoordInv_thetaOf A hA).symm
  · subst h1
    rw [QlinB_apply, e, hG, QlinCompL_eq_QlinCompX2 ell _ 2 hreg 1 (by norm_num), suCoord_sig A hA, q1]
  · subst h2
    rw [QlinB_apply, e, hG, QlinCompL_eq_QlinCompX2 ell _ 2 hreg 2 le_rfl, suCoord_sig A hA, q2]

theorem hsInner_dgS_dgS (a b : ℝ) : hsInner (dgS a) (dgS b) = a * b * hsInner (dgS 1) (dgS 1) := by
  rw [hsInner_dgS_one (dgS a) b, AdalyFormal.Balaban.SuTwoInner.hsInner_symm (dgS a) (dgS 1), hsInner_dgS_one (dgS 1) a]
  ring

#print axioms sum_BIdx
#print axioms QlinB_sig
#print axioms hsInner_dgS_dgS

end AdalyFormal.CoverOmega
