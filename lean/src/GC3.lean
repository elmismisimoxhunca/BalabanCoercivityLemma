import GC2
import ZXG3A

/-!
# GC3 -- shared interface: pointwise `Ad` on every `L²` carrier, as `LinearIsometryEquiv`s.
`adGen φ : (ι → 𝔰𝔲(2)) ≃ₗᵢ same`, `(adGen φ f) i = R(φ i) (f i)`, for any label function `φ : ι → SU(2)`.
* sites `adSL γ = adGen γ`; bonds `adBL γ = adGen (fun b => γ b.1)` (equal to `adB γ`, `adBL_apply : rfl`);
* constraint space `adFL γ G = adGen (fun p : BIdx G => γ p.2.1.1)` (frame = base site of the level-`j` bond);
* `E₀ = bondSupp G`: `adEL γ G` (restriction of `adBL γ`; supports are pointwise-invariant).
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul_apply RMap_one)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply gaugeInv)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

/-- pointwise `Ad` on an `L²` space of `𝔰𝔲(2)`-valued functions with SU(2) labels. -/
def adGenLM {ι : Type*} [Fintype ι] (φ : ι → SU2g) :
    PiLp 2 (fun _ : ι => SuTwo) →ₗ[ℝ] PiLp 2 (fun _ : ι => SuTwo) where
  toFun f := WithLp.toLp 2 (fun i => RMap (φ i) (f i))
  map_add' f g := by ext i; simp
  map_smul' c f := by ext i; simp

theorem adGenLM_apply {ι : Type*} [Fintype ι] (φ : ι → SU2g) (f : PiLp 2 (fun _ : ι => SuTwo)) (i : ι) :
    (adGenLM φ f) i = RMap (φ i) (f i) := rfl

theorem inner_adGenLM {ι : Type*} [Fintype ι] (φ : ι → SU2g) (x y : PiLp 2 (fun _ : ι => SuTwo)) :
    ⟪adGenLM φ x, adGenLM φ y⟫ = ⟪x, y⟫ := by
  simp only [PiLp.inner_apply, adGenLM_apply]
  exact Finset.sum_congr rfl (fun i _ => AdalyFormal.Balaban.SuTwoInner.inner_RMap _ _ _)

theorem adGenLM_inv {ι : Type*} [Fintype ι] (φ : ι → SU2g) (x : PiLp 2 (fun _ : ι => SuTwo)) :
    adGenLM (fun i => (φ i)⁻¹) (adGenLM φ x) = x := by
  ext i
  simp only [adGenLM_apply, RMap_mul_apply, inv_mul_cancel, RMap_one]
  rfl

/-- `Ad_φ` as a linear isometric equivalence. -/
def adGen {ι : Type*} [Fintype ι] (φ : ι → SU2g) :
    PiLp 2 (fun _ : ι => SuTwo) ≃ₗᵢ[ℝ] PiLp 2 (fun _ : ι => SuTwo) :=
  LinearIsometryEquiv.mk
    (LinearEquiv.ofLinear (adGenLM φ) (adGenLM (fun i => (φ i)⁻¹))
      (LinearMap.ext (fun y => by
        have := adGenLM_inv (fun i => (φ i)⁻¹) y
        simpa using this))
      (LinearMap.ext (adGenLM_inv φ)))
    (fun x => by
      have h := inner_adGenLM φ x x
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
      show ‖adGenLM φ x‖ = ‖x‖
      have := norm_nonneg (adGenLM φ x); have := norm_nonneg x
      nlinarith [sq_nonneg (‖adGenLM φ x‖ - ‖x‖), sq_nonneg (‖adGenLM φ x‖ + ‖x‖)])

theorem adGen_apply {ι : Type*} [Fintype ι] (φ : ι → SU2g) (f : PiLp 2 (fun _ : ι => SuTwo)) (i : ι) :
    (adGen φ f) i = RMap (φ i) (f i) := rfl

theorem adGen_symm_apply {ι : Type*} [Fintype ι] (φ : ι → SU2g) (f : PiLp 2 (fun _ : ι => SuTwo)) (i : ι) :
    ((adGen φ).symm f) i = RMap ((φ i)⁻¹) (f i) := rfl

/-- sites -/
abbrev adSL (γ : GaugeFn L) : SiteL2 L ≃ₗᵢ[ℝ] SiteL2 L := adGen γ
/-- bonds -/
abbrev adBL (γ : GaugeFn L) : BondFnL2 L ≃ₗᵢ[ℝ] BondFnL2 L := adGen (fun b : Bond L => γ b.1)

theorem adBL_apply (γ : GaugeFn L) (f : BondFnL2 L) : adBL γ f = adB γ f := rfl

/-- constraint space `FSp G`: frame at the base site of the level-`j` bond. -/
abbrev adFL (γ : GaugeFn L) (G : TowerGeom L) : FSp G ≃ₗᵢ[ℝ] FSp G :=
  adGen (fun p : BIdx G => γ p.2.1.1)

theorem adFL_apply (γ : GaugeFn L) (G : TowerGeom L) (f : FSp G) (p : BIdx G) :
    (adFL γ G f) p = RMap (γ p.2.1.1) (f p) := rfl

/-- `E₀ = bondSupp G` is `Ad`-stable. -/
theorem adBL_mem_bondSupp (γ : GaugeFn L) (G : TowerGeom L) (A : ↥(bondSupp G)) :
    adBL γ (A : BondFnL2 L) ∈ bondSupp G := by
  intro b hb
  show RMap (γ b.1) ((A : BondFnL2 L) b) = 0
  rw [A.2 b hb, map_zero]

/-- `Ad` on `E₀`. -/
def adEL (γ : GaugeFn L) (G : TowerGeom L) : ↥(bondSupp G) ≃ₗᵢ[ℝ] ↥(bondSupp G) :=
  LinearIsometryEquiv.mk
    (LinearEquiv.ofLinear
      ((adBL γ).toLinearEquiv.toLinearMap.restrict (fun A hA => adBL_mem_bondSupp γ G ⟨A, hA⟩))
      ((adBL γ).symm.toLinearEquiv.toLinearMap.restrict (fun A hA => by
        have := adBL_mem_bondSupp (gaugeInv γ) G ⟨A, hA⟩
        exact this))
      (LinearMap.ext (fun y => by
        apply Subtype.ext
        show (adBL γ) ((adBL γ).symm (y : BondFnL2 L)) = y
        exact (adBL γ).apply_symm_apply _))
      (LinearMap.ext (fun y => by
        apply Subtype.ext
        show (adBL γ).symm ((adBL γ) (y : BondFnL2 L)) = y
        exact (adBL γ).symm_apply_apply _)))
    (fun x => (adBL γ).norm_map (x : BondFnL2 L))

theorem adEL_coe (γ : GaugeFn L) (G : TowerGeom L) (A : ↥(bondSupp G)) :
    ((adEL γ G A : ↥(bondSupp G)) : BondFnL2 L) = adBL γ (A : BondFnL2 L) := rfl

#print axioms adBL
#print axioms adFL
#print axioms adEL

end AdalyFormal.GaugeCov
