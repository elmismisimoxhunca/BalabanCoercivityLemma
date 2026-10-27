import FE3c
import ZT4A

/-!
# FE4a -- unit-torus block geometry for the operator `C` at a general `Lambda`:
 (a) a row `c` of `Q_1` reads only bonds with both end-points in `B(c_-) ∪ B(c_+)`;
 (b) a staircase `Gamma_{y,x}` (`x ∈ B(y)`) has both end-points of every bond in `B(y)`;
 (c) if `Lambda` is a union of blocks (`LamBlockSum`), a site of `Lambda` in `B(y')` forces `y' ∈ Lambda'`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.FlatEllGeneral

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice
  staircasePath mem_axisSegment corner1 corner2 coarseLattice_unique)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ReparamCDisjoint (ReadsBond droppedBondLast coarse_coord_add_ell_le)

theorem arith_block (N ell y x t : ℕ) (hell : 0 < ell) (hN : ell ∣ N) (hy : ell ∣ y) (hyN : y + ell ≤ N)
    (hx1 : y ≤ x) (hx2 : x < y + ell) (ht : t ≤ ell) :
    (y ≤ (x + t) % N ∧ (x + t) % N < y + ell) ∨
      ((y + ell) % N ≤ (x + t) % N ∧ (x + t) % N < (y + ell) % N + ell) := by
  by_cases hlt : x + t < N
  · rw [Nat.mod_eq_of_lt hlt]
    by_cases h1 : x + t < y + ell
    · left; omega
    · right
      have h2 : y + ell < N := by omega
      rw [Nat.mod_eq_of_lt h2]; omega
  · have hge : N ≤ x + t := Nat.le_of_not_lt hlt
    obtain ⟨b, hb⟩ := hy
    obtain ⟨a, ha⟩ := hN
    have hell0 : 0 < ell := hell
    have h1 : b + 1 ≤ a := by
      have : ell * (b + 1) ≤ ell * a := by rw [← ha]; nlinarith
      exact Nat.le_of_mul_le_mul_left this hell0
    have h2 : a < b + 2 := by
      have : ell * a < ell * (b + 2) := by rw [← ha]; nlinarith
      exact Nat.lt_of_mul_lt_mul_left this
    have hNy : N = y + ell := by
      have : a = b + 1 := by omega
      rw [ha, hb, this]; ring
    right
    rw [hNy, Nat.mod_self, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- one block step: a coordinate-wise forward shift by `t ≤ ell` of a point of `B(y)` stays in `B(y)` or lands in `B(y_+)` -/
theorem coarseShift_block {L : PeriodicLatticeExtent} {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    {x : PeriodicLatticeSite L} (hx : x ∈ blockOf y ell) (μ : Fin 3) (t : ℕ) (ht : t ≤ ell) :
    coarseShift x t μ ∈ blockOf y ell ∨ coarseShift x t μ ∈ blockOf (coarseShift y ell μ) ell := by
  have hx' := mem_blockOf.mp hx
  have hy' := mem_CoarseLattice.mp hy
  have hyN := coarse_coord_add_ell_le hdvd μ (y μ).val (hy' μ) (y μ).isLt
  have hA := arith_block (L μ + 1) ell (y μ).val (x μ).val t hell (hdvd μ)
    (Nat.dvd_of_mod_eq_zero (hy' μ)) hyN (hx' μ).1 (hx' μ).2 ht
  have hxv := coarseShift_val_eq x t μ
  have hyv := coarseShift_val_eq y ell μ
  rcases hA with h | h
  · left
    rw [mem_blockOf]
    intro ρ
    by_cases hρ : ρ = μ
    · subst hρ; rw [hxv]; exact h
    · rw [coarseShift_apply_ne x t μ ρ hρ]; exact hx' ρ
  · right
    rw [mem_blockOf]
    intro ρ
    by_cases hρ : ρ = μ
    · subst hρ; rw [hxv, hyv]; exact h
    · rw [coarseShift_apply_ne x t μ ρ hρ, coarseShift_apply_ne y ell μ ρ hρ]; exact hx' ρ

/-- a row of `Q_1` reads only bonds with both end-points in `B(c_-) ∪ B(c_+)` -/
theorem reads_in_blocks {L : PeriodicLatticeExtent} {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (c : CoarseBond L ell) (b : Bond L) (hb : ReadsBond ell c b) :
    (b.1 ∈ blockOf c.1.1 ell ∨ b.1 ∈ blockOf (coarseShift c.1.1 ell c.2) ell) ∧
    (periodicLatticeShift b.1 b.2 ∈ blockOf c.1.1 ell ∨
      periodicLatticeShift b.1 b.2 ∈ blockOf (coarseShift c.1.1 ell c.2) ell) := by
  obtain ⟨x, hx, i, hi, rfl⟩ := hb
  rw [Finset.mem_range] at hi
  have h1 := coarseShift_block hell hdvd c.1.2 hx c.2 i (by omega)
  have h2 := coarseShift_block hell hdvd c.1.2 hx c.2 (i + 1) (by omega)
  have hs : periodicLatticeShift (AdalyFormal.Balaban.QOne.pathSite x c.2 i) c.2 = coarseShift x (i + 1) c.2 := by
    unfold AdalyFormal.Balaban.QOne.pathSite coarseShift
    rw [Function.iterate_succ_apply']
  exact ⟨h1, by rw [hs]; exact h2⟩

/-- `Λ` a union of blocks: a point of `Λ` in `B(y')` (`y'` coarse) forces `y' ∈ Λ'` -/
theorem lamPrime_of_mem {Lu : PeriodicLatticeExtent} {ell : ℕ} {Lam : Set (PeriodicLatticeSite Lu)}
    (hLB : LamBlockSum ell Lam) {y' s : PeriodicLatticeSite Lu} (hy' : y' ∈ CoarseLattice Lu ell)
    (hs : s ∈ blockOf y' ell) (hsL : s ∈ Lam) : y' ∈ LamPrime ell Lam := by
  obtain ⟨y'', hy'', hs''⟩ := hLB s hsL
  have : y'' = y' := coarseLattice_unique ell hy''.1 hy' hs'' hs
  rw [← this]; exact hy''

#print axioms arith_block
#print axioms coarseShift_block
#print axioms reads_in_blocks
#print axioms lamPrime_of_mem

end AdalyFormal.FlatEllGeneral
