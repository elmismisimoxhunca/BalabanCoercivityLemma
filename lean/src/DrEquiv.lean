import DrRed1
import GdR5a

/-!
# DrEquiv -- `GuardResidualT selAll selAll` is equivalent to the PENCIL statement

`GuardPencilT`: the same quantifier shape as `GuardResidualT`, with the conclusion `IsUnit G1inv_lit` replaced by
`IsUnit (Ginv_lit - Delta2_loc)`, where `Delta2_loc` is the correction of the LOCALISED data (`dataS selIn selIn`).
So the guard residual is exactly: "in the class regime with a positive-energy test field, `Ginv_lit` invertible implies `Ginv_lit - Delta2_loc` invertible".
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Residual

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.D1Guarded
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)

/-- the shape of `GuardResidualT selAll selAll` with an arbitrary conclusion `C` (after the premise `IsUnit Ginv_lit`). -/
def GShape (C : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell) (_ : Tower (scaleUp ell k Lu))
    (_ : LinkCfg (scaleUp ell k Lu)) (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
        TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
        (∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt) →
        IsUnit (dataS selAll selAll (gparams ell k Lu (by omega) S U a Lam)).Ginv →
        C ell k Lu (by omega) S U a Lam

/-- the residual conclusion -/
def CRes : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell) (_ : Tower (scaleUp ell k Lu))
    (_ : LinkCfg (scaleUp ell k Lu)) (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop :=
  fun ell k Lu h S U a Lam => IsUnit (G1invS selAll selAll (gparams ell k Lu h S U a Lam))

/-- the pencil conclusion: `Ginv_lit - Delta2_loc` is invertible. -/
def CPen : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell) (_ : Tower (scaleUp ell k Lu))
    (_ : LinkCfg (scaleUp ell k Lu)) (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop :=
  fun ell k Lu h S U a Lam =>
    IsUnit ((dataS selAll selAll (gparams ell k Lu h S U a Lam)).Ginv -
      (dataS selIn selIn (gparams ell k Lu h S U a Lam)).Delta2 (dataS_laws selIn selIn (gparams ell k Lu h S U a Lam)))

theorem guardResidualT_eq_shape : GuardResidualT selAll selAll ↔ GShape CRes := Iff.rfl

/-- transfer along a pointwise implication valid under the covariance-layer data at the configuration. -/
theorem GShape_imp (C₁ C₂ : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell) (_ : Tower (scaleUp ell k Lu))
    (_ : LinkCfg (scaleUp ell k Lu)) (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop)
    (hpt : ∀ (ell k : ℕ) (hell0 : 0 < ell) (M R : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)),
      Admissible ell M R k S → 17 * ell ≤ R * M →
      WellDefAt selIn selIn (gparams ell k Lu hell0 S U a Lam) →
      IsUnit (dataS selAll selAll (gparams ell k Lu hell0 S U a Lam)).Ginv →
      C₁ ell k Lu hell0 S U a Lam → C₂ ell k Lu hell0 S U a Lam)
    (h : GShape C₁) : GShape C₂ := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, hres1⟩ := h ell hell a ha
  obtain ⟨m₂, hm₂, hmm⟩ := (pin_target8_iff.mpr AdalyFormal.M2RightInv.p428Target8 : P428Target8S selIn selIn) ell hell a ha
  refine ⟨max m₁ m₂, le_trans hm₁ (le_max_left _ _), fun m hm => ?_⟩
  obtain ⟨R₁, hres2⟩ := hres1 m (le_trans (le_max_left _ _) hm)
  obtain ⟨R₂, hR₂⟩ := hmm m (le_trans (le_max_right _ _) hm)
  refine ⟨max (max R₁ R₂) 18, fun R hR => ?_⟩
  have hRa : R₁ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRb : R₂ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hR18 : 18 ≤ R := le_trans (le_max_right _ _) hR
  obtain ⟨a₁, ha₁, hres3⟩ := hres2 R hRa
  obtain ⟨hside, a₂, ha₂, γ₀, hγ, hcore⟩ := hR₂ R hRb
  refine ⟨min a₁ a₂, lt_min ha₁ ha₂, fun k hk Lu α₀ hα hαle hT S hS Lam hL U hU hex hu => ?_⟩
  have hell0 : 0 < ell := by omega
  have hm1 : 1 ≤ m := le_trans hm₁ (le_trans (le_max_left _ _) hm)
  have hroom : 17 * ell ≤ R * ell ^ m := by
    have h1 : ell ≤ ell ^ m := by
      calc ell = ell ^ 1 := (pow_one ell).symm
        _ ≤ ell ^ m := Nat.pow_le_pow_right hell0 hm1
    calc 17 * ell ≤ 18 * ell ^ m := by omega
      _ ≤ R * ell ^ m := Nat.mul_le_mul_right _ hR18
  have hαa : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₁ := le_trans hαle (min_le_left _ _)
  have hαb : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₂ := le_trans hαle (min_le_right _ _)
  have hloc := hcore k hk Lu α₀ hα hαb hT S hS Lam hL U hU
  obtain ⟨Bt, h1, h2, hE⟩ := hex
  have hWD := WellDefAt_loc_of_inst ell k hell0 a ha.le Lu γ₀ hγ S Lam U Bt h1 h2 hE hloc
  exact hpt ell k hell0 (ell ^ m) R Lu S U a Lam hS hroom hWD hu
    (hres3 k hk Lu α₀ hα hαa hT S hS Lam hL U hU ⟨Bt, h1, h2, hE⟩ hu)

/-- the pencil statement: the shape of the residual with conclusion `IsUnit (Ginv_lit - Delta2_loc)`. -/
def GuardPencilT : Prop := GShape CPen

theorem residualT_iff_pencilT : GuardResidualT selAll selAll ↔ GuardPencilT := by
  have hiff : ∀ (ell k : ℕ) (hell0 : 0 < ell) (M R : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)),
      Admissible ell M R k S → 17 * ell ≤ R * M →
      WellDefAt selIn selIn (gparams ell k Lu hell0 S U a Lam) →
      IsUnit (dataS selAll selAll (gparams ell k Lu hell0 S U a Lam)).Ginv →
      (CRes ell k Lu hell0 S U a Lam ↔ CPen ell k Lu hell0 S U a Lam) := by
    intro ell k hell0 M R Lu S U a Lam hS hroom hWD hu
    exact isUnit_G1inv_lit_iff_pencil (gparams ell k Lu hell0 S U a Lam) hS hell0 hroom hu hWD
  constructor
  · intro h
    exact GShape_imp CRes CPen (fun ell k h0 M R Lu S U a Lam hS hr hW hu c => (hiff ell k h0 M R Lu S U a Lam hS hr hW hu).mp c) h
  · intro h
    exact GShape_imp CPen CRes (fun ell k h0 M R Lu S U a Lam hS hr hW hu c => (hiff ell k h0 M R Lu S U a Lam hS hr hW hu).mpr c) h

theorem P428Target8SG_iff_pencilT :
    P428Target8SG selAll selAll ↔ GuardPencilT :=
  (P428Target8SG_iff_residualT selAll selAll (fun _ _ => Set.subset_univ _) (fun _ _ => Set.subset_univ _)).trans
    residualT_iff_pencilT

#print axioms guardResidualT_eq_shape
#print axioms GShape_imp
#print axioms residualT_iff_pencilT
#print axioms P428Target8SG_iff_pencilT

end AdalyFormal.D1Residual
