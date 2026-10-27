import NsCvO42

/-!
# CvO43 -- `Q*` of a Z-row field is a Z-field: `<Q w, zrow rho> = <w, zfield (Wt rho)>` for EVERY `w` (lane omega)

By `Ad_h`-equivariance of `Q` (gauge library at the constant Cartan gauge) both sides depend on `w` only through its sigma_3 part `w + Ad_h w`.
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
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.GaugeCov
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

theorem sig_apply_eq (A : BondFnL2 L) (hA : SigB (WithLp.ofLp A)) (b : Bond L) :
    (A b : SuTwo) = dgS (thetaOf (WithLp.ofLp A) b) := by
  have := congrArg (fun z : BondFnL2 L => z b) (suCoordInv_thetaOf A hA)
  simp only at this
  rw [← this, suCoordInv_aF]

theorem inner_sig_zfield (u : BondFnL2 L) (hu : SigB (WithLp.ofLp u)) (g : ℕ → ℝ) :
    (inner ℝ u (zfield g) : ℝ) = c0 * ∑ x : PeriodicLatticeSite L, thetaOf (WithLp.ofLp u) (x, 1) * g (x 0).val := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Fin.sum_univ_three]
  have h0 : (0 : Fin 3) ≠ 1 := by decide
  have h2 : (2 : Fin 3) ≠ 1 := by decide
  show hsInner (u (x, 0)) (zfun g (x, 0)) + hsInner (u (x, 1)) (zfun g (x, 1)) + hsInner (u (x, 2)) (zfun g (x, 2)) = _
  simp only [zfun, h0, h2, if_false, if_true]
  rw [AdalyFormal.Balaban.DeltaKU.hsInner_zero_right, AdalyFormal.Balaban.DeltaKU.hsInner_zero_right, zero_add, add_zero]
  rw [sig_apply_eq u hu (x, 1), hsInner_dgS_dgS]
  unfold c0
  ring

theorem adFL_zrow (G : TowerGeom L) (ρ : ℕ → ℕ → ℝ) : adFL (hGauge L) G (zrow G ρ) = zrow G ρ := by
  refine PiLp.ext (fun p => ?_)
  rw [adFL_apply]
  show RMap (cartan (Real.pi / 2)) (if p.2.1.2 = 1 then dgS (ρ (p.1 : ℕ) (p.2.1.1 0).val) else 0) = (if p.2.1.2 = 1 then dgS (ρ (p.1 : ℕ) (p.2.1.1 0).val) else 0)
  split_ifs
  · exact RMap_dgS (cartan_isCartan _) _
  · exact map_zero _

theorem adBL_zfield (g : ℕ → ℝ) : adBL (hGauge L) (zfield g) = zfield g := by
  refine PiLp.ext (fun b => ?_)
  rw [adBL_hGauge_apply]
  show RMap (cartan (Real.pi / 2)) (zfun g b) = zfun g b
  unfold zfun
  split_ifs
  · exact RMap_dgS (cartan_isCartan _) _
  · exact map_zero _

end AdalyFormal.CoverOmega
