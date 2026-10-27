import GdR6a

/-!
# GdR6b -- Round 6: the residual holds on the whole "base-point flat" family.

`Delta2_eq_zero_of_Jperp`: if `C2` takes values in `Z`, `{x | Q x ∈ Z} ⊆ V` and the source `J` is orthogonal to `V`, then `Delta2 = 0`.
`G1invS_eq_Ginv_base`: for ANY configuration `U` with `U e = 1` whenever the base point of `e` lies in `Ω₀` (arbitrary values elsewhere: on the exterior and on the
shell bonds entering `Ω₀`) and collar `3 ≤ R M`, the source `J` vanishes on every bond of `E₀` that is not a level-0 bond, hence is orthogonal to `V`, hence `G1inv = Ginv`.
Consequently `IsUnit Ginv → IsUnit G1inv` holds there, `GapAt` follows from the localised units, and the guarded literal headline holds at every such class configuration
(`SG_on_base_flat_family`).  The boundary-twist family is the one-parameter subfamily `Uth`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.IngredientFamily
open AdalyFormal.D1Literal
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.SourceJ
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

section abstract
variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem Delta2_eq_zero_of_Jperp (D : BaseDataS E S F) (hL : D.Laws) (V : Submodule ℝ E) (Z : Submodule ℝ F)
    (hZV : ∀ x, D.Q x ∈ Z → x ∈ V) (hCZ : ∀ A, D.C2 A ∈ Z) (hJ : ∀ x ∈ V, ⟪x, D.J⟫ = 0) : D.Delta2 hL = 0 := by
  obtain ⟨hs, hf⟩ := D.Delta2_spec hL
  refine symm_unique hs (fun x y => by simp) (fun A => ?_)
  rw [hf A]
  by_cases hN : IsUnit ((D.Q.comp D.G).comp D.Qs)
  · have hV : D.H (D.C2 A) ∈ V := hZV _ (by rw [Q_H_apply D hN]; exact hCZ A)
    rw [hJ _ hV]; simp
  · have : D.H = 0 := by
      unfold BaseDataS.H
      rw [Ring.inverse_non_unit _ hN]
      simp only [ContinuousLinearMap.comp_zero]
    rw [this]; simp

end abstract

#print axioms Delta2_eq_zero_of_Jperp

section conc
variable (sJ : PlaqSel) (P : IngrBParams)

/-- the source vanishes on the non-level-0 bonds of `E₀` when `U` is `1` on all bonds with base point in `Ω₀` (collar `3 ≤ R M`). -/
theorem JfS_vanish_base {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell) (h3 : 3 ≤ R * M)
    (hU' : ∀ e : Bond P.Lf, e.1 ∈ P.S.Om 0 → P.U e = 1) (b : Bond P.Lf) (hb1 : b ∈ bondsOm0 P.G) (hb2 : b ∉ bondsLam P.G 0) :
    (WithLp.ofLp (JfS sJ P)) b = 0 := by
  have hz : JfieldLoc (sJ _ P.G) P.U b.1 b.2 = 0 := by
    apply JfieldLoc_zero_of_flat _ _ (P.S.Om 0) hU'
    intro z hz
    rcases endpoint_om1 hell hS b hb1 hb2 with hw | hw
    · refine near_om1 hS hw ?_ (Nat.zero_le _)
      have := AdalyFormal.StatementLaneR8.pdist_triangle z b.1 b.1
      rw [AdalyFormal.StatementLaneR8.pdist_self] at this
      omega
    · refine near_om1 hS hw ?_ (Nat.zero_le _)
      have h1 := AdalyFormal.StatementLaneR8.pdist_triangle z b.1 (periodicLatticeShift b.1 b.2)
      have h2 := AdalyFormal.StatementLaneR8.pdist_shift_le b.1 b.2
      omega
  unfold JfS
  unfold AdalyFormal.IngredientFamily.JSU2Loc
  apply Subtype.ext
  simp [hz]

theorem G1invS_eq_Ginv_base (sD : PlaqSel) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell) (h3 : 3 ≤ R * M)
    (hU' : ∀ e : Bond P.Lf, e.1 ∈ P.S.Om 0 → P.U e = 1) : G1invS sD sJ P = (dataS sD sJ P).Ginv := by
  have hD2 : (dataS sD sJ P).Delta2 (dataS_laws sD sJ P) = 0 := by
    refine Delta2_eq_zero_of_Jperp (dataS sD sJ P) (dataS_laws sD sJ P) (V0 P.G) (Z0 P.G) ?_ ?_ ?_
    · intro x hx β hβ
      have h1 := Q_level0_coord sD sJ P x β hβ
      have h2 := hx β hβ
      rw [h1] at h2
      exact h2
    · intro A β hβ
      exact C2full_level0_coord P.G P.U _ β hβ
    · intro x hx
      rw [dataS_J_proj, pE_inner_right]
      simp only [PiLp.inner_apply]
      refine Finset.sum_eq_zero (fun b _ => ?_)
      by_cases hb1 : b ∈ bondsOm0 P.G
      · by_cases hb2 : b ∈ bondsLam P.G 0
        · rw [hx b hb2]; simp
        · rw [JfS_vanish_base sJ P hS hell h3 hU' b hb1 hb2]; simp
      · have h0 : (WithLp.ofLp (iE P.G x)) b = 0 := x.2 b hb1
        rw [h0]; simp
  have h := (dataS sD sJ P).G1inv_unique (G1invS_spec sD sJ P) ((dataS sD sJ P).isG1inv_sub (dataS_laws sD sJ P))
  rw [h, hD2]; simp

end conc

#print axioms JfS_vanish_base
#print axioms G1invS_eq_Ginv_base

/-- **the guarded literal headline on the base-point flat family**: for every class configuration `U` that is `1` on every bond whose base point lies in `Ω₀`
(arbitrary on the exterior and on the bonds entering `Ω₀`), at the headline's quantifiers, the guarded literal inequality holds.  No thickness, no `Λ ≠ ∅`,
no injectivity of `Q*` is needed. -/
theorem SG_on_base_flat_family (sD sJ : PlaqSel)
    (hsD : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD L G)
    (hsJ : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ L G) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
        TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
        (∀ e : Bond (scaleUp ell k Lu), e.1 ∈ S.Om 0 → U e = 1) →
        InstIneqSG sD sJ ell k (by omega) a Lu γ₀ S Lam U := by
  have hell0 : 0 < ell := by omega
  obtain ⟨m₀, hm₀, hmm⟩ := (pin_target8_iff.mpr AdalyFormal.M2RightInv.p428Target8 : P428Target8S selIn selIn) ell hell a ha
  refine ⟨m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR₀⟩ := hmm m hm
  refine ⟨max R₀ 18, fun R hR => ?_⟩
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hcore⟩ := hR₀ R (le_trans (le_max_left _ _) hR)
  have hR18 : 18 ≤ R := le_trans (le_max_right _ _) hR
  refine ⟨a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ hα hαle hT S hS Lam hL U hU hbase => ?_⟩
  have hroom : 17 * ell ≤ R * ell ^ m := by
    have h1 : ell ≤ ell ^ m := by
      calc ell = ell ^ 1 := (pow_one ell).symm
        _ ≤ ell ^ m := Nat.pow_le_pow_right hell0 (le_trans hm₀ hm)
    calc 17 * ell ≤ 18 * ell ^ m := by omega
      _ ≤ R * ell ^ m := Nat.mul_le_mul_right _ hR18
  have h3 : 3 ≤ R * ell ^ m := by omega
  have hloc := hcore k hk Lu α₀ hα hαle hT S hS Lam hL U hU
  by_cases hWD2 : WellDefAt selIn selIn (gparams ell k Lu hell0 S U a Lam)
  · exact InstIneqSG_general sD sJ hell0 hS hk hroom ha.le hγ Lam U hsD hsJ hloc hWD2
      (fun hu => by
        rw [G1invS_eq_Ginv_base sJ (gparams ell k Lu hell0 S U a Lam) sD hS hell0 h3 hbase]
        exact hu)
  · intro _
    exact InstIneqS_of_loc_not_wd sD sJ hell0 ha.le hγ Lam U hloc hWD2

#print axioms SG_on_base_flat_family
end AdalyFormal.D1Guarded
