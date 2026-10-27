import R7Fork.DM13g

/-!
# DM13h -- global consequences of the adjacency induction: the stratum means are constant, and the harmonic constants `c` vanish.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 32000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower Admissible bigSide BlockClosed)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice card_blockOf_of_coarse)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)

section glob
variable {L : PeriodicLatticeExtent}

theorem adj_all {ell M R k : ℕ} {S : Tower L} {φ : PeriodicLatticeSite L → SuTwo} {c : Fin 3 → SuTwo}
    (H : AdjHyp ell M R k L S φ c) :
    ∀ (u : PeriodicLatticeSite L) (μ : Fin 3),
      meanB ell S (Theta φ c) (periodicLatticeShift u μ) = meanB ell S (Theta φ c) u - seam c u μ := by
  have key : ∀ m, m ≤ k → ∀ (u : PeriodicLatticeSite L) (μ : Fin 3), lev S u ≤ m → lev S (periodicLatticeShift u μ) ≤ m →
      meanB ell S (Theta φ c) (periodicLatticeShift u μ) = meanB ell S (Theta φ c) u - seam c u μ := by
    intro m
    induction m with
    | zero =>
      intro _ u μ hu hv
      exact adj_base H u μ (by omega) (by omega)
    | succ m ih =>
      intro hmk u μ hu hv
      exact adj_step H (m + 1) (by omega) hmk (fun u μ h1 h2 => ih (by omega) u μ (by omega) (by omega)) u μ hu hv
  intro u μ
  exact key k le_rfl u μ (lev_spec H.hS u).1 (lev_spec H.hS _).1

/-- the origin -/
def origin (L : PeriodicLatticeExtent) : PeriodicLatticeSite L := fun ρ => ⟨0, Nat.succ_pos _⟩

theorem meanB_const {ell M R k : ℕ} {S : Tower L} {φ : PeriodicLatticeSite L → SuTwo} {c : Fin 3 → SuTwo}
    (H : AdjHyp ell M R k L S φ c) (x : PeriodicLatticeSite L) :
    meanB ell S (Theta φ c) x = meanB ell S (Theta φ c) (origin L) := by
  classical
  set Nmax : ℕ := Finset.univ.sup (fun ρ : Fin 3 => L ρ + 1) with hNmax
  have hNpos : 0 < Nmax := lt_of_lt_of_le (Nat.succ_pos (L 0)) (Finset.le_sup (f := fun ρ : Fin 3 => L ρ + 1) (Finset.mem_univ 0))
  have hbound : ∀ ρ, L ρ + 1 ≤ Nmax := fun ρ => Finset.le_sup (f := fun ρ : Fin 3 => L ρ + 1) (Finset.mem_univ ρ)
  have hz : origin L ∈ CoarseLattice L Nmax := by
    rw [mem_CoarseLattice]; intro ρ; simp [origin]
  have hmem : ∀ w : PeriodicLatticeSite L, w ∈ blockOf (origin L) Nmax := by
    intro w; rw [mem_blockOf]; intro ρ
    have := (w ρ).isLt; have := hbound ρ
    simp [origin]; omega
  refine box_const H.hN (fun w => meanB ell S (Theta φ c) w) hNpos hz ?_ x (hmem x)
  intro w _ ν hlt _
  show meanB ell S (Theta φ c) (periodicLatticeShift w ν) = meanB ell S (Theta φ c) w
  rw [adj_all H w ν]
  unfold seam
  rw [if_neg (by omega), sub_zero]

theorem c_zero {ell M R k : ℕ} {S : Tower L} {φ : PeriodicLatticeSite L → SuTwo} {c : Fin 3 → SuTwo}
    (H : AdjHyp ell M R k L S φ c) (μ : Fin 3) : c μ = 0 := by
  -- the last site of the line through the origin in direction mu
  let u : PeriodicLatticeSite L := fun ρ => if _h : ρ = μ then ⟨L ρ, Nat.lt_succ_self _⟩ else ⟨0, Nat.succ_pos _⟩
  have hu : (u μ).val = L μ := by simp [u]
  have hshift : periodicLatticeShift u μ = origin L := by
    funext ρ
    apply Fin.ext
    by_cases h : ρ = μ
    · subst h
      rw [shift_val_same H.hN, hu, Nat.mod_self]
      rfl
    · rw [shift_val_ne u h]; simp [u, origin, h]
  have h1 := adj_all H u μ
  rw [hshift, meanB_const H u] at h1
  unfold seam at h1
  rw [if_pos (by omega)] at h1
  have h2 : ((L μ + 1 : ℕ) : ℝ) • c μ = 0 := sub_eq_self.mp h1.symm
  have hne : ((L μ + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  exact (smul_eq_zero.mp h2).resolve_left hne

end glob

#print axioms adj_all
#print axioms c_zero

#print axioms meanB_const

end AdalyFormal.DirichletMono
