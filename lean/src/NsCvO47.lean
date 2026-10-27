import NsCvO46

/-!
# CvO47 -- `Q`, `Q*`, `Mass` on Z-fields (lane omega)
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
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

/-- `Qfull (zfield f) = zrow` of the (rescaled) slice sums. -/
theorem Qfull_zfield_eq_zrow {ell c : ℕ} {G : TowerGeom L} {isRow : ℕ → ℕ → Prop} (S : StagSetup L ell c G isRow) (t : ℝ) (htπ : |t| < tcap ell)
    (f : ℕ → ℝ) : QfullOf G (stagCfg c t) (zfield f) = zrow G (fun j v => ((ell : ℝ) ^ j)⁻¹ * fSum ell j f v) := by
  refine PiLp.ext (fun p => ?_)
  rw [Qfull_zfield S.hN S.hE S.hell S.hdiv c t htπ S.hc1 S.hc2 f G S.hG S.hk S.hcrs p]
  show _ = (if p.2.1.2 = 1 then dgS (((ell : ℝ) ^ (p.1 : ℕ))⁻¹ * fSum ell (p.1 : ℕ) f (p.2.1.1 0).val) else 0)
  split_ifs
  · rw [dgS_smul]
  · simp

/-- the mass weights on a row field. -/
theorem diagW_massW_zrow (G : TowerGeom L) (ell : ℕ) (hG : G.ell = ell) (a : ℝ) (ρ : ℕ → ℕ → ℝ) :
    diagW G (massW G a) (zrow G ρ) = zrow G (fun j v => a * (ell : ℝ) ^ j * ρ j v) := by
  refine PiLp.ext (fun p => ?_)
  show massW G a p • (if p.2.1.2 = 1 then dgS (ρ (p.1 : ℕ) (p.2.1.1 0).val) else 0) = (if p.2.1.2 = 1 then dgS (a * (ell : ℝ) ^ (p.1 : ℕ) * ρ (p.1 : ℕ) (p.2.1.1 0).val) else 0)
  unfold massW
  rw [hG]
  split_ifs
  · rw [dgS_smul]
  · simp

/-- `Q*` of a Z-row field. -/
theorem Qstar_zrow {ell c : ℕ} {G : TowerGeom L} {isRow : ℕ → ℕ → Prop} (S : StagSetup L ell c G isRow) (t : ℝ) (htπ : |t| < tcap ell)
    (ρ : ℕ → ℕ → ℝ) : ContinuousLinearMap.adjoint (QfullOf G (stagCfg c t)) (zrow G ρ) = zfield (Wt ell isRow ρ) := by
  apply ext_inner_left ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_Q_zrow S t htπ w ρ

/-- **`Mass` on a Z-field**. -/
theorem MassFull_zfield {ell c : ℕ} {G : TowerGeom L} {isRow : ℕ → ℕ → Prop} (S : StagSetup L ell c G isRow) (t : ℝ) (htπ : |t| < tcap ell)
    (a : ℝ) (f : ℕ → ℝ) :
    MassFull G a (bondSectorOf G (stagCfg c t)) (zfield f) =
      zfield (Wt ell isRow (fun j v => a * fSum ell j f v)) := by
  show ContinuousLinearMap.adjoint (QfullOf G (stagCfg c t)) (diagW G (massW G a) (QfullOf G (stagCfg c t) (zfield f))) = _
  rw [Qfull_zfield_eq_zrow S t htπ f, diagW_massW_zrow G ell S.hG, Qstar_zrow S t htπ]
  have hne : ∀ j : ℕ, (ell : ℝ) ^ j ≠ 0 := fun j => pow_ne_zero _ (by exact_mod_cast S.hell.ne')
  have : (fun (j v : ℕ) => a * (ell : ℝ) ^ j * (((ell : ℝ) ^ j)⁻¹ * fSum ell j f v)) = (fun (j v : ℕ) => a * fSum ell j f v) := by
    funext j v
    field_simp [hne j]
  rw [this]

#print axioms Qfull_zfield_eq_zrow
#print axioms Qstar_zrow
#print axioms MassFull_zfield

end AdalyFormal.CoverOmega
