import CvO21
import ZXR2Ops3

/-!
# CvO22 -- Z-fields (sigma_3, direction 1, transverse-constant) and the gauge-fixing pieces on them (lane omega)

`zfield f` : the bond field `(x,1) ↦ i f(x₀) σ₃`, zero in directions `0, 2`.  On a Cartan configuration `U`:
* `gradAdj_zfield`: `D*_U (zfield f) = 0` (the divergence of a transverse-constant direction-1 field vanishes),
* `Wop_zfield`: `W (zfield f) = zfield f`,  `Tfull_zfield`: `T (zfield f) = 0`  (`W = 1 - D G' R D*`, `T = R D*`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (gradCovariantAdjointValue periodicLatticeShiftBack)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2 (toM2 toM2_mem gradAdj gradAdj_apply Wop Tfull Rproj Gp gradL2 SiteL2 TowerGeom Cfg)

variable {L : PeriodicLatticeExtent}

/-- `i x σ₃ ∈ su(2)`. -/
noncomputable def dgS (x : ℝ) : SuTwo := ⟨toM2 ![x, 0, 0], toM2_mem _⟩

theorem dgS_coe (x : ℝ) : ((dgS x : SuTwo) : M2) = dg x := toM2_aF x

theorem diagP_dgS (x : ℝ) : diagP (dgS x) = dgS x := by
  apply Subtype.ext
  rw [diagP_coe, dgS_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [dg, Matrix.diagonal_apply]

theorem dgS_zero : dgS 0 = 0 := by
  apply Subtype.ext; rw [dgS_coe, dg_zero]; rfl

theorem RMap_dgS {V : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hV : IsCartan V) (x : ℝ) : RMap V (dgS x) = dgS x := by
  have := RMap_diagP hV (dgS x)
  rwa [diagP_dgS] at this

/-- the transverse-constant direction-1 sigma_3 field with profile `f`. -/
noncomputable def zfield (f : ℕ → ℝ) : BondFnL2 L :=
  WithLp.toLp 2 (fun b : Bond L => if b.2 = 1 then dgS (f (b.1 0).val) else 0)

theorem zfield_apply (f : ℕ → ℝ) (b : Bond L) : (zfield f : BondFnL2 L) b = if b.2 = 1 then dgS (f (b.1 0).val) else 0 := rfl

theorem shiftBack_coord_ne (y : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) :
    (periodicLatticeShiftBack y μ) ν = y ν := by
  unfold periodicLatticeShiftBack; exact Function.update_of_ne h _ _

/-- **`D*_U` kills Z-fields**. -/
theorem gradAdj_zfield {U : Cfg L} (hU : CartanCfg U) (f : ℕ → ℝ) : gradAdj U (zfield f) = 0 := by
  refine PiLp.ext (fun y => ?_)
  rw [show (gradAdj U (zfield f)) y = gradCovariantAdjointValue U (WithLp.ofLp (zfield f)) y from
    congrFun (gradAdj_apply U (zfield f)) y]
  unfold gradCovariantAdjointValue
  rw [Fin.sum_univ_three]
  have h1 : (periodicLatticeShiftBack y 1) 0 = y 0 := shiftBack_coord_ne y 1 0 (by decide)
  simp only [zfield, WithLp.ofLp_toLp, if_neg (show ¬ ((0 : Fin 3) = 1) by decide), if_neg (show ¬ ((2 : Fin 3) = 1) by decide),
    if_true, h1]
  have hci : IsCartan (U (periodicLatticeShiftBack y 1, 1))⁻¹ := isCartan_inv (hU _)
  rw [show RMap (U (periodicLatticeShiftBack y 1, 1))⁻¹ (dgS (f (y 0).val)) = dgS (f (y 0).val) from RMap_dgS hci _]
  simp

theorem Wop_zfield (G : TowerGeom L) (U : Cfg L) (hU : CartanCfg U) (a : ℝ) (f : ℕ → ℝ) : Wop G U a (zfield f) = zfield f := by
  unfold Wop
  simp [gradAdj_zfield hU]

theorem Tfull_zfield (G : TowerGeom L) (U : Cfg L) (hU : CartanCfg U) (f : ℕ → ℝ) : Tfull G U (zfield f) = 0 := by
  unfold Tfull
  simp [gradAdj_zfield hU]

#print axioms gradAdj_zfield
#print axioms Wop_zfield
#print axioms Tfull_zfield

end AdalyFormal.CoverOmega
