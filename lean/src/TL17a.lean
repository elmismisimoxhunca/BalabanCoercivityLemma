import TL16b

/-!
# TL17a -- the constraint sets `Λ'`, dropped bonds, staircases and `Λ̃` are compatible with pull-back
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice blockOf mem_blockOf inBlock staircasePath)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast)
open AdalyFormal.Balaban.QOne (pathSite pathSite_succ)
open AdalyFormal.IngredientFamilyR2

section lamsec
variable {Lut Lu : PeriodicLatticeExtent} {hu : Covers Lut Lu} {o : Fin 3 → ℕ} {ell : ℕ}

theorem phiS_mem_blockOf (hp : PhiOK hu o ell) (hell : 0 < ell) {y x : PeriodicLatticeSite Lut} (hy : Aligned ell y)
    (hx : x ∈ blockOf y ell) : phiS hu o x ∈ blockOf (phiS hu o y) ell := by
  rw [mem_blockOf] at hx ⊢
  intro μ
  obtain ⟨h1, h2⟩ := hx μ
  have := phiS_val_in_block hp hell hy μ h1 h2
  exact ⟨by omega, by omega⟩

theorem exists_lift_blockOf (hp : PhiOK hu o ell) (hell : 0 < ell) {y : PeriodicLatticeSite Lut} (hy : Aligned ell y)
    {x : PeriodicLatticeSite Lu} (hx : x ∈ blockOf (phiS hu o y) ell) : ∃ x' ∈ blockOf y ell, phiS hu o x' = x := by
  rw [mem_blockOf] at hx
  have key : ∀ μ : Fin 3, ∃ c : Fin (Lut μ + 1), (y μ).val ≤ c.val ∧ c.val < (y μ).val + ell ∧
      (phiS hu o y μ).val + (c.val - (y μ).val) = (x μ).val := by
    intro μ
    obtain ⟨h1, h2⟩ := hx μ
    have hlt : (y μ).val + ((x μ).val - (phiS hu o y μ).val) < Lut μ + 1 := by
      have := aligned_add_le ell (Lut μ + 1) (y μ).val ((hp.side μ).trans (hu μ)) (hy μ) (y μ).isLt
      omega
    refine ⟨⟨(y μ).val + ((x μ).val - (phiS hu o y μ).val), hlt⟩, by simp, by simp; omega, ?_⟩
    simp only [Nat.add_sub_cancel_left]; omega
  choose c hc1 hc2 hc3 using key
  refine ⟨c, ?_, ?_⟩
  · rw [mem_blockOf]; exact fun μ => ⟨hc1 μ, hc2 μ⟩
  · funext μ
    apply Fin.ext
    have e1 := phiS_val_in_block hp hell hy μ (hc1 μ) (hc2 μ)
    have := hc3 μ
    omega

theorem LamPrime_pull (hp : PhiOK hu o ell) (hell : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu)) (y : PeriodicLatticeSite Lut) :
    y ∈ LamPrime ell (phiS hu o ⁻¹' Lam) ↔ phiS hu o y ∈ LamPrime ell Lam := by
  constructor
  · rintro ⟨hy, hb⟩
    have hal : Aligned ell y := fun μ => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hy μ)
    refine ⟨mem_CoarseLattice.mpr (fun μ => Nat.mod_eq_zero_of_dvd (((aligned_phiS hp y).mpr hal) μ)), fun x hx => ?_⟩
    obtain ⟨x', hx', rfl⟩ := exists_lift_blockOf hp hell hal hx
    exact hb x' hx'
  · rintro ⟨hy, hb⟩
    have hal : Aligned ell (phiS hu o y) := fun μ => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hy μ)
    have hal' : Aligned ell y := (aligned_phiS hp y).mp hal
    refine ⟨mem_CoarseLattice.mpr (fun μ => Nat.mod_eq_zero_of_dvd (hal' μ)), fun x hx => ?_⟩
    exact hb _ (phiS_mem_blockOf hp hell hal' hx)

theorem pathSite_nat (y : PeriodicLatticeSite Lut) (μ : Fin 3) (i : ℕ) :
    phiS hu o (pathSite y μ i) = pathSite (phiS hu o y) μ i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pathSite_succ, pathSite_succ, phiS_shift, ih]

theorem dropped_nat (hp : PhiOK hu o ell) (c : CoarseBond Lut ell) :
    phiE hu o (droppedBondLast ell c) = droppedBondLast ell (cbMap hp c) := by
  simp only [droppedBondLast, phiE, cbMap, pathSite_nat]

end lamsec

end AdalyFormal.Thin
