import DrPath3
import DrEquiv

/-!
# DrFamily -- what a counterexample to `GuardResidualT selAll selAll` needs, stated at the real quantifiers.

`SepPathFamily` is the statement that, at every threshold (`m₀`, `R₀`, `a₀`) of the headline's shape, there is an exterior-only path `U t`, an in-class start `U 0`,
a positive-energy test field and the three operator conditions of `exterior_path_separation` (coercivity of `Ginv_lit` on `[0,T]`, positive semidefiniteness of
`Ginv_lit(0) - Delta2_loc`, a negative direction of `Ginv_lit(T) - Delta2_loc`).  `not_GuardResidualT_of_sep` proves `SepPathFamily → ¬ GuardResidualT selAll selAll`.
`SepPathFamily` itself is NOT proved here: it is the named residual (see LOG.md).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Residual

open scoped RealInnerProductSpace
open Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.D1Guarded
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)

/-- the named residual: an exterior-only path with the three operator conditions, at every threshold. -/
def SepPathFamily : Prop :=
  ∃ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (_ : 0 < a), ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ 1 ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ ∀ a₀ : ℝ, 0 < a₀ →
    ∃ (k : ℕ) (_ : 1 ≤ k) (Lu : PeriodicLatticeExtent) (α₀ : ℝ) (_ : 0 < α₀) (_ : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀)
      (_ : TorusOK ell (ell ^ m) Lu) (S : Tower (scaleUp ell k Lu)) (_ : Admissible ell (ell ^ m) R k S)
      (Lam : Set (PeriodicLatticeSite Lu)) (_ : LambdaOK2 ell (ell ^ m) R k S Lam)
      (U : ℝ → Cfg (scaleUp ell k Lu)) (_ : ContFam U)
      (_ : ∀ (t : ℝ) (e : Bond (scaleUp ell k Lu)), e ∉ Zb (S.Om 0) → U t e = U 0 e)
      (_ : ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ (U 0))
      (_ : ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt)
      (T : ℝ) (_ : 0 < T),
      (∀ t ∈ Icc (0 : ℝ) T, ∃ c' : ℝ, 0 < c' ∧ ∀ x, c' * ‖x‖ ^ 2 ≤ ⟪x, GinvLit (by omega : 0 < ell) S a Lam U t x⟫) ∧
      AdalyFormal.D1Literal.PSD (GinvLit (by omega : 0 < ell) S a Lam U 0 - DeltaLoc0 (by omega : 0 < ell) S a Lam U) ∧
      ∃ v : E0 S, ⟪v, (GinvLit (by omega : 0 < ell) S a Lam U T - DeltaLoc0 (by omega : 0 < ell) S a Lam U) v⟫ < 0

theorem not_GuardResidualT_of_sep (h : SepPathFamily) : ¬ GuardResidualT selAll selAll := by
  intro hres
  obtain ⟨ell, hell, a, ha, hfam⟩ := h
  obtain ⟨m₁, hm₁, hres1⟩ := hres ell hell a ha
  obtain ⟨m₂, hm₂, hmm⟩ := (pin_target8_iff.mpr AdalyFormal.M2RightInv.p428Target8 : P428Target8S selIn selIn) ell hell a ha
  obtain ⟨m, hm, hm1, hfam1⟩ := hfam (max m₁ m₂)
  obtain ⟨R₁, hres2⟩ := hres1 m (le_trans (le_max_left _ _) hm)
  obtain ⟨R₂, hR₂⟩ := hmm m (le_trans (le_max_right _ _) hm)
  obtain ⟨R, hR, hfam2⟩ := hfam1 (max (max R₁ R₂) 18)
  have hRa : R₁ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRb : R₂ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hR18 : 18 ≤ R := le_trans (le_max_right _ _) hR
  obtain ⟨a₁, ha₁, hres3⟩ := hres2 R hRa
  obtain ⟨hside, a₂, ha₂, γ₀, hγ, hcore⟩ := hR₂ R hRb
  obtain ⟨k, hk, Lu, α₀, hα, hαle, hT, S, hS, Lam, hL, U, hcont, hUU, hcl, hex, T, hT0, hco, h0, v, hv⟩ :=
    hfam2 (min a₁ a₂) (lt_min ha₁ ha₂)
  have hell0 : 0 < ell := by omega
  have hroom : 17 * ell ≤ R * ell ^ m := by
    have h1 : ell ≤ ell ^ m := by
      calc ell = ell ^ 1 := (pow_one ell).symm
        _ ≤ ell ^ m := Nat.pow_le_pow_right hell0 hm1
    calc 17 * ell ≤ 18 * ell ^ m := by omega
      _ ≤ R * ell ^ m := Nat.mul_le_mul_right _ hR18
  have hαa : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₁ := le_trans hαle (min_le_left _ _)
  have hαb : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₂ := le_trans hαle (min_le_right _ _)
  have hloc := hcore k hk Lu α₀ hα hαb hT S hS Lam hL (U 0) hcl
  obtain ⟨Bt, h1, h2, hE⟩ := hex
  have hWD0 := WellDefAt_loc_of_inst ell k hell0 a ha.le Lu γ₀ hγ S Lam (U 0) Bt h1 h2 hE hloc
  obtain ⟨t, ht0, htT, hclt, hu, hnu⟩ := exterior_path_separation hell0 hS hell hroom a Lam U hUU hcont hWD0 12 α₀
    (((ell : ℝ) ^ k)⁻¹) hcl T hT0 hco h0 v hv
  exact hnu (hres3 k hk Lu α₀ hα hαa hT S hS Lam hL (U t) hclt ⟨Bt, h1, h2, hE⟩ hu)

#print axioms not_GuardResidualT_of_sep

/-- the same conclusion at the guarded literal headline. -/
theorem not_P428Target8SG_of_sep (h : SepPathFamily) : ¬ P428Target8SG selAll selAll := fun hs =>
  not_GuardResidualT_of_sep h ((P428Target8SG_iff_residualT selAll selAll (fun _ _ => Set.subset_univ _)
    (fun _ _ => Set.subset_univ _)).mp hs)

#print axioms not_P428Target8SG_of_sep

end AdalyFormal.D1Residual
