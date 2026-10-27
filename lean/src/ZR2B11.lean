import ZR2B10

/-!
# R2B11 -- MULTI-STRATUM NON-VACUITY: all hypotheses of `CoercAt2` jointly satisfiable on the
two-stratum tower `TT` (k = 1, ell = 2, M = 1, F = 10, R = 12) with a NON-FLAT `U`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

def Lam30 (Lu : PeriodicLatticeExtent) : Set (PeriodicLatticeSite Lu) := {y | (y 0).val = 30}

theorem pcd_far60 (N a b : ℕ) (hN : N = 60) (ha : a = 30) (hb : b < 10 ∨ 50 ≤ b) (hb2 : b < 60) :
    12 < pcd N a b := by
  subst hN; subst ha; unfold pcd; split_ifs <;> omega

theorem Lam30_ok {Lu Lf : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60)
    (hLf : ∀ μ, Lf μ + 1 = 120) :
    LambdaOK (Lu := Lu) (Lf := Lf) 2 1 12 1 (TT Lf) (Lam30 Lu) := by
  have hemb : ∀ (y : PeriodicLatticeSite Lu) (μ : Fin 3), 2 ^ 1 * (y μ).val < Lf μ + 1 := by
    intro y μ
    have h1 := (y μ).isLt; have h2 := hLu μ; have h3 := hLf μ; omega
  refine ⟨?_, fun y μ => ⟨2 ^ 1 * (y μ).val, hemb y μ⟩, ?_, ?_, ?_⟩
  · intro x hx y hy
    have := hy 0
    simp only [Nat.div_one] at this
    simp only [Lam30, Set.mem_setOf_eq] at hx ⊢
    omega
  · intro y μ; rfl
  · intro y hy
    simp only [Lam30, Set.mem_setOf_eq] at hy
    simp only [TT, if_neg (by decide : (1 : ℕ) ≠ 0), if_true, OmB, Set.mem_setOf_eq]
    show 20 ≤ 2 ^ 1 * (y 0).val ∧ 2 ^ 1 * (y 0).val < 100
    omega
  · intro y hy y' hy'
    simp only [Lam30, Set.mem_setOf_eq] at hy
    simp only [TT, if_neg (by decide : (1 : ℕ) ≠ 0), if_true, OmB, Set.mem_setOf_eq, not_and_or,
      not_le, not_lt] at hy'
    have hy'0 : (y' 0).val < 10 ∨ 50 ≤ (y' 0).val := by
      change (2 ^ 1 * (y' 0).val < 20) ∨ (100 ≤ 2 ^ 1 * (y' 0).val) at hy'
      omega
    have hy'1 : (y' 0).val < 60 := by have := (y' 0).isLt; have := hLu 0; omega
    show 12 * 1 < pdist y y'
    have hlt : 12 < pcd (Lu 0 + 1) (y 0).val (y' 0).val :=
      pcd_far60 _ _ _ (hLu 0) hy hy'0 hy'1
    unfold pdist
    exact lt_of_lt_of_le hlt
      (Finset.single_le_sum (f := fun μ : Fin 3 => pcd (Lu μ + 1) (y μ).val (y' μ).val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))

theorem LamPrime_Lam30_empty {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60)
    (y : PeriodicLatticeSite Lu) : y ∉ LamPrime 2 (Lam30 Lu) := by
  rintro ⟨hy, hblk⟩
  have hmod : (y 0).val % 2 = 0 := (AdalyFormal.Balaban.AdmissibleSubspace.mem_CoarseLattice.mp hy) 0
  have hlt : (y 0).val < 60 := by have := (y 0).isLt; have := hLu 0; omega
  have hlt1 : (y 0).val + 1 < Lu 0 + 1 := by have := hLu 0; omega
  have hself : y ∈ blockOf y 2 := by
    rw [AdalyFormal.Balaban.AdmissibleSubspace.mem_blockOf]
    intro μ; omega
  have hx : Function.update y 0 ⟨(y 0).val + 1, hlt1⟩ ∈ blockOf y 2 := by
    rw [AdalyFormal.Balaban.AdmissibleSubspace.mem_blockOf]
    intro μ
    by_cases h : μ = 0
    · subst h; simp
    · rw [Function.update_of_ne h]; omega
  have h1 := hblk y hself
  have h2 := hblk _ hx
  simp only [Lam30, Set.mem_setOf_eq] at h1 h2
  simp at h2
  omega

noncomputable def Bspike30 (Lu : PeriodicLatticeExtent) (hLu : ∀ μ, Lu μ + 1 = 60) : Bond Lu → SuTwo :=
  fun e => if e = ((fun μ => ⟨30, by have := hLu μ; omega⟩ : PeriodicLatticeSite Lu), (1 : Fin 3))
    then suTwoWitness else 0

theorem Bspike30_props {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) :
    OnLambdaTildeIn (Lam30 Lu) 2 (Bspike30 Lu hLu) ∧ OnLambda (Lam30 Lu) (Bspike30 Lu hLu) ∧
      OnLambdaT (Lam30 Lu) (Bspike30 Lu hLu) ∧ 0 < bondEnergy (Bspike30 Lu hLu) := by
  refine ⟨⟨fun y hy => absurd hy (LamPrime_Lam30_empty hLu y), ?_⟩, ?_, ?_, ?_⟩
  · rintro b ⟨c, hc, _⟩
    exact absurd hc (not_or.mpr ⟨LamPrime_Lam30_empty hLu _, LamPrime_Lam30_empty hLu _⟩)
  · intro b hb
    unfold Bspike30
    rw [if_neg]
    rintro rfl
    apply hb
    refine ⟨?_, ?_⟩
    · show (30 : ℕ) = 30; rfl
    · show ((periodicLatticeShift _ 1) 0).val = 30
      rw [shift_apply]; simp
  · intro b hb
    unfold Bspike30
    rw [if_neg]
    rintro rfl
    apply hb
    left; show (30 : ℕ) = 30; rfl
  · unfold bondEnergy
    apply Finset.sum_pos'
    · intro b _; positivity
    · refine ⟨((fun μ => ⟨30, by have := hLu μ; omega⟩ : PeriodicLatticeSite Lu), (1 : Fin 3)),
        Finset.mem_univ _, ?_⟩
      unfold Bspike30
      simp only [if_true]
      have := norm_pos_iff.mpr suTwoWitness_ne_zero
      positivity

/-- **MULTI-STRATUM NON-VACUITY (k = 1).** -/
theorem multistratum_satisfiable {Lu Lf : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60)
    (hLf : ∀ μ, Lf μ + 1 = 120) {α₀ : ℝ} (hα : 0 < α₀) (hα1 : α₀ ≤ 1 / 2) :
    TorusOK 2 1 Lu ∧ Admissible 2 1 12 1 (TT Lf) ∧ CoversOm0 2 1 10 1 (TT Lf) ∧
    (∃ p : PeriodicLatticeSite Lf, p ∈ towerBj (TT Lf) 0) ∧
    (∃ p : PeriodicLatticeSite Lf, p ∈ towerBj (TT Lf) 1) ∧
    (∃ p : PeriodicLatticeSite Lf, p ∉ (TT Lf).Om 0) ∧
    LambdaOK (Lu := Lu) (Lf := Lf) 2 1 12 1 (TT Lf) (Lam30 Lu) ∧
    (∃ U : LinkCfg Lf, PerCubeRegularMix 2 1 10 1 (TT Lf) α₀ (((2 : ℕ) : ℝ) ^ 1)⁻¹ U ∧
       ¬ ∃ g : PeriodicLatticeSite Lf → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
    (∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn (Lam30 Lu) 2 Bt ∧ OnLambdaT (Lam30 Lu) Bt ∧
       OnLambda (Lam30 Lu) Bt ∧ 0 < bondEnergy Bt) := by
  have hLu' : ∀ μ, Lu μ + 1 = 60 := hLu
  have hmk : ∀ (v : ℕ) (μ : Fin 3), v < 120 → v < Lf μ + 1 := fun v μ h => by have := hLf μ; omega
  refine ⟨torusOK_60 hLu, TT_admissible hLf, TT_covers hLf 10 le_rfl, ?_, ?_, ?_,
    Lam30_ok hLu hLf, ?_, ⟨Bspike30 Lu hLu, Bspike30_props hLu |>.1, Bspike30_props hLu |>.2.2.1,
      Bspike30_props hLu |>.2.1, Bspike30_props hLu |>.2.2.2⟩⟩
  · refine ⟨fun μ => ⟨10, hmk 10 μ (by norm_num)⟩, ?_⟩
    simp [towerBj, TT, OmA, OmB]
  · refine ⟨fun μ => ⟨50, hmk 50 μ (by norm_num)⟩, ?_⟩
    simp [towerBj, TT, OmA, OmB]
  · refine ⟨fun μ => ⟨2, hmk 2 μ (by norm_num)⟩, ?_⟩
    simp [TT, OmA]
  · set z0 : PeriodicLatticeSite Lf := fun μ => ⟨0, hmk 0 μ (by norm_num)⟩ with hz0
    have hηv : (((2 : ℕ) : ℝ) ^ 1)⁻¹ = 1 / 2 := by norm_num
    have hpos : 0 < α₀ * ((((2 : ℕ) : ℝ) ^ 1)⁻¹) ^ 2 / 10 := by rw [hηv]; positivity
    refine ⟨Ufield (((2 : ℕ) : ℝ) ^ 1)⁻¹ (spike (periodicLatticeShift z0 0, 1)
        (α₀ * ((((2 : ℕ) : ℝ) ^ 1)⁻¹) ^ 2 / 10)), ?_, ?_⟩
    · intro f hf1 hf2
      have hf : f = 10 := by omega
      subst hf
      apply ufield_perCubeRegular2 (by norm_num) (by norm_num) le_rfl _ hα
      intro e
      unfold spike
      split_ifs
      · rw [abs_of_pos hpos]
      · simp; positivity
    · apply spike_not_pure_gauge (by have := hLf 0; omega)
      · rw [hηv]; norm_num; positivity
      · rw [hηv]; norm_num; linarith

#print axioms multistratum_satisfiable

end AdalyFormal.StatementLane2
