import R7Fork.DM13e

/-!
# DM13f -- THE ADJACENCY INDUCTION: for a potential `phi` and constants `c` whose fine bonds off `Om_1` and whose level-`m` block rows
(`frakB_m`) satisfy the kernel relations, the stratum means of the tilted potential `Theta` agree across every bond, up to the seam defect `-N c`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower Admissible bigSide BlockClosed)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice card_blockOf_of_coarse)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)

section adj
variable {L : PeriodicLatticeExtent}

structure AdjHyp (ell M R k : ℕ) (L : PeriodicLatticeExtent) (S : Tower L) (φ : PeriodicLatticeSite L → SuTwo)
    (c : Fin 3 → SuTwo) : Prop where
  hell : 0 < ell
  hS : Admissible ell M R k S
  hN : ∀ ν, 1 ≤ L ν
  hbig : ∀ j ≤ k, ∀ ν, 2 * ell ^ j ≤ L ν + 1
  r0 : ∀ (u : PeriodicLatticeSite L) (μ : Fin 3), u ∉ S.Om 1 → periodicLatticeShift u μ ∉ S.Om 1 →
    φ (periodicLatticeShift u μ) - φ u + c μ = 0
  rows : ∀ m, 1 ≤ m → m ≤ k → ∀ p ∈ CoarseLattice L (ell ^ m), ∀ μ : Fin 3,
    (p ∈ S.Om m ∨ coarseShift p (ell ^ m) μ ∈ S.Om m) → p ∉ S.Om (m + 1) →
    coarseShift p (ell ^ m) μ ∉ S.Om (m + 1) →
    (1 / ((ell ^ m : ℕ) : ℝ) ^ 4) • (∑ x ∈ blockOf (coarseShift p (ell ^ m) μ) (ell ^ m), φ x
      - ∑ x ∈ blockOf p (ell ^ m), φ x) + c μ = 0

/-- the seam defect of the bond `u -> shift u mu` -/
noncomputable def seam (c : Fin 3 → SuTwo) (u : PeriodicLatticeSite L) (μ : Fin 3) : SuTwo :=
  if (u μ).val + 1 = L μ + 1 then ((L μ + 1 : ℕ) : ℝ) • c μ else 0

/-- L7 witness: the package `AdjHyp` is inhabited (trivial potential, any tower satisfying the torus conditions) -/
theorem adjHyp_zero {ell M R k : ℕ} {S : Tower L} (hell : 0 < ell) (hS : Admissible ell M R k S)
    (hN : ∀ ν, 1 ≤ L ν) (hbig : ∀ j ≤ k, ∀ ν, 2 * ell ^ j ≤ L ν + 1) :
    AdjHyp ell M R k L S (fun _ => (0 : SuTwo)) (fun _ => (0 : SuTwo)) := by
  refine ⟨hell, hS, hN, hbig, ?_, ?_⟩
  · intro u μ _ _; simp
  · intro m _ _ p _ μ _ _ _; simp

#print axioms adjHyp_zero

theorem self_mem_block {n : ℕ} (hn : 0 < n) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L n) :
    y ∈ blockOf y n := by
  rw [mem_blockOf]; intro ρ; constructor <;> omega

theorem adj_base {ell M R k : ℕ} {S : Tower L} {φ : PeriodicLatticeSite L → SuTwo} {c : Fin 3 → SuTwo}
    (H : AdjHyp ell M R k L S φ c) (u : PeriodicLatticeSite L) (μ : Fin 3) (hu : lev S u = 0)
    (hv : lev S (periodicLatticeShift u μ) = 0) :
    meanB ell S (Theta φ c) (periodicLatticeShift u μ) = meanB ell S (Theta φ c) u - seam c u μ := by
  rw [meanB_zero S _ hv, meanB_zero S _ hu]
  have hu1 : u ∉ S.Om 1 := by
    have := (lev_spec H.hS u).2.2; rw [hu] at this; exact this
  have hv1 : periodicLatticeShift u μ ∉ S.Om 1 := by
    have := (lev_spec H.hS (periodicLatticeShift u μ)).2.2; rw [hv] at this; exact this
  have hr := H.r0 u μ hu1 hv1
  have hdiff : ∑ ν : Fin 3, (((periodicLatticeShift u μ) ν).val : ℝ) • c ν - ∑ ν : Fin 3, ((u ν).val : ℝ) • c ν
      = ((((periodicLatticeShift u μ) μ).val : ℝ) - ((u μ).val : ℝ)) • c μ := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single μ]
    · rw [sub_smul]
    · intro ν _ hνμ
      simp [shift_val_ne u hνμ]
    · intro h; exact absurd (Finset.mem_univ μ) h
  unfold Theta seam
  have hv' := shift_val_same H.hN u μ
  have hlt := (u μ).isLt
  by_cases hw : (u μ).val + 1 = L μ + 1
  · have h0 : ((periodicLatticeShift u μ) μ).val = 0 := by rw [hv', hw, Nat.mod_self]
    rw [if_pos hw]
    rw [h0] at hdiff
    have hN' : ((L μ + 1 : ℕ) : ℝ) = ((u μ).val : ℝ) + 1 := by
      have : (u μ).val + 1 = L μ + 1 := hw
      exact_mod_cast this.symm
    rw [hN']
    simp only [Nat.cast_zero] at hdiff
    have := hdiff
    calc φ (periodicLatticeShift u μ) + ∑ ν : Fin 3, (((periodicLatticeShift u μ) ν).val : ℝ) • c ν
        = (φ (periodicLatticeShift u μ) - φ u + c μ) + (φ u + ∑ ν : Fin 3, ((u ν).val : ℝ) • c ν) +
          ((∑ ν : Fin 3, (((periodicLatticeShift u μ) ν).val : ℝ) • c ν - ∑ ν : Fin 3, ((u ν).val : ℝ) • c ν) - c μ) := by abel
      _ = _ := by rw [hr, this]; module
  · rw [if_neg hw]
    have h1 : ((periodicLatticeShift u μ) μ).val = (u μ).val + 1 := by
      rw [hv', Nat.mod_eq_of_lt (by omega)]
    rw [h1] at hdiff
    push_cast at hdiff
    calc φ (periodicLatticeShift u μ) + ∑ ν : Fin 3, (((periodicLatticeShift u μ) ν).val : ℝ) • c ν
        = (φ (periodicLatticeShift u μ) - φ u + c μ) + (φ u + ∑ ν : Fin 3, ((u ν).val : ℝ) • c ν) +
          ((∑ ν : Fin 3, (((periodicLatticeShift u μ) ν).val : ℝ) • c ν - ∑ ν : Fin 3, ((u ν).val : ℝ) • c ν) - c μ) := by abel
      _ = _ := by rw [hr, hdiff]; module

end adj

#print axioms adj_base

end AdalyFormal.DirichletMono
