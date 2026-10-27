import NsCvO40

/-!
# CvO41 -- the pairing `<Q w, zrow rho>` for sigma_3-valued `w` (lane omega)
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
/-- the slice weight `[isRow j v] rho j v`. -/
noncomputable def Hrow (isRow : ℕ → ℕ → Prop) (ρ : ℕ → ℕ → ℝ) (j v : ℕ) : ℝ := if isRow j v then ρ j v else 0

open Classical in
theorem pair_levels {ell c : ℕ} {G : TowerGeom L} {isRow : ℕ → ℕ → Prop} (S : StagSetup L ell c G isRow) (t : ℝ) (htπ : |t| < tcap ell)
    (w : BondFnL2 L) (hw : SigB (WithLp.ofLp w)) (ρ : ℕ → ℕ → ℝ) :
    (inner ℝ (QfullOf G (stagCfg c t) w) (zrow G ρ) : ℝ) =
      ∑ j ∈ Finset.range 3, (((ell : ℝ) ^ j)⁻¹) * c0 *
        ∑ y : PeriodicLatticeSite L, (if Crs (ell ^ j) y then Hrow isRow ρ j (y 0).val * thetaSeq ell j (thetaOf (WithLp.ofLp w)) (y, 1) else 0) := by
  rw [PiLp.inner_apply]
  have hterm : ∀ p : BIdx G, (inner ℝ ((QfullOf G (stagCfg c t) w) p) ((zrow G ρ) p) : ℝ) =
      (fun (j : Fin (G.k + 1)) (b : Bond L) => if b.2 = 1 then (((ell : ℝ) ^ (j : ℕ))⁻¹) * (thetaSeq ell j (thetaOf (WithLp.ofLp w)) b * ρ j (b.1 0).val * c0) else 0)
        p.1 p.2.1 := by
    intro p
    have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; have := S.hk; omega
    show hsInner ((((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G (stagCfg c t) p.1 w)) p.2.1)
      (if p.2.1.2 = 1 then dgS (ρ (p.1 : ℕ) (p.2.1.1 0).val) else 0) = _
    rw [QlinB_sig S.hN S.hE S.hell c t htπ S.hc1 S.hc2 G S.hG p.1 hj w hw, S.hG, suCoordInv_aF]
    by_cases hb : p.2.1.2 = 1
    · simp only [if_pos hb]
      rw [AdalyFormal.Balaban.SuTwoInner.hsInner_smul_left, hsInner_dgS_dgS]
      rfl
    · simp only [if_neg hb]
      exact AdalyFormal.Balaban.DeltaKU.hsInner_zero_right _
  have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset (BIdx G)) = Finset.univ) (fun p _ => hterm p)
  rw [hsum, sum_BIdx G (fun (j : Fin (G.k + 1)) (b : Bond L) => if b.2 = 1 then (((ell : ℝ) ^ (j : ℕ))⁻¹) * (thetaSeq ell j (thetaOf (WithLp.ofLp w)) b * ρ j (b.1 0).val * c0) else 0)]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ∑ b : Bond L, (if b ∈ bondsLam G j then (if b.2 = 1 then (((ell : ℝ) ^ j)⁻¹) * (thetaSeq ell j (thetaOf (WithLp.ofLp w)) b * ρ j (b.1 0).val * c0) else 0) else 0)) (G.k + 1)]
  rw [S.hk]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj2 : j ≤ 2 := by have := Finset.mem_range.mp hj; omega
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Fin.sum_univ_three]
  have h0 : (0 : Fin 3) ≠ 1 := by decide
  have h2 : (2 : Fin 3) ≠ 1 := by decide
  simp only [h0, h2, if_false, ite_self, add_zero, zero_add, if_true]
  by_cases hy : Crs (ell ^ j) y
  · by_cases hr : isRow j (y 0).val
    · have hm : (y, (1 : Fin 3)) ∈ bondsLam G j := (S.hrow j hj2 y).mpr ⟨hy, hr⟩
      simp only [if_pos hm, if_pos hy, Hrow, if_pos hr]
      ring
    · have hm : (y, (1 : Fin 3)) ∉ bondsLam G j := fun h => hr ((S.hrow j hj2 y).mp h).2
      simp only [if_neg hm, if_pos hy, Hrow, if_neg hr]
      ring
  · have hm : (y, (1 : Fin 3)) ∉ bondsLam G j := fun h => hy ((S.hrow j hj2 y).mp h).1
    simp only [if_neg hm, if_neg hy]
    ring

#print axioms pair_levels

end AdalyFormal.CoverOmega
