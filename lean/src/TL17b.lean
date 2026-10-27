import TL17a

/-!
# TL17b -- `CRowIn`, `IsDroppedIn`, staircases, `Λ̃` and `Λ`-supports under pull-back
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
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShiftBack_shift periodicLatticeShift_shiftBack)
open AdalyFormal.IngredientFamilyR2

section drop
variable {Lut Lu : PeriodicLatticeExtent} {hu : Covers Lut Lu} {o : Fin 3 → ℕ} {ell : ℕ}

theorem CRowIn_pull (hp : PhiOK hu o ell) (hell : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu)) (c : CoarseBond Lut ell) :
    CRowIn ell (phiS hu o ⁻¹' Lam) c ↔ CRowIn ell Lam (cbMap hp c) := by
  unfold CRowIn
  rw [LamPrime_pull hp hell, LamPrime_pull hp hell, coarseShift_nat]
  rfl

theorem pathSite_sbIter {L' : PeriodicLatticeExtent} (y : PeriodicLatticeSite L') (μ : Fin 3) (n : ℕ) :
    pathSite ((fun z => periodicLatticeShiftBack z μ)^[n] y) μ n = y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, pathSite_succ, ih, periodicLatticeShift_shiftBack]

theorem sbIter_pathSite {L' : PeriodicLatticeExtent} (y : PeriodicLatticeSite L') (μ : Fin 3) (n : ℕ) :
    (fun z => periodicLatticeShiftBack z μ)^[n] (pathSite y μ n) = y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, pathSite_succ, periodicLatticeShiftBack_shift]
    exact ih y

theorem sbIter_nat (y : PeriodicLatticeSite Lut) (μ : Fin 3) (n : ℕ) :
    phiS hu o ((fun z => periodicLatticeShiftBack z μ)^[n] y) = (fun z => periodicLatticeShiftBack z μ)^[n] (phiS hu o y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, phiS_shiftBack]

theorem isDropped_pull (hp : PhiOK hu o ell) (hell : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu)) (b : Bond Lut) :
    IsDroppedIn (phiS hu o ⁻¹' Lam) ell b ↔ IsDroppedIn Lam ell (phiE hu o b) := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨cbMap hp c, (CRowIn_pull hp hell Lam c).mp hc, dropped_nat hp c⟩
  · rintro ⟨c, hc, hb⟩
    obtain ⟨x, μ⟩ := b
    -- φ b = (pathSite c.1.1 c.2 (ell-1), c.2)
    have hb' : (phiS hu o x, μ) = (pathSite c.1.1 c.2 (ell - 1), c.2) := hb
    have hμ : μ = c.2 := congrArg Prod.snd hb'
    have hx0 : phiS hu o x = pathSite c.1.1 c.2 (ell - 1) := congrArg Prod.fst hb'
    have hx : phiS hu o x = pathSite c.1.1 μ (ell - 1) := by rw [hμ]; exact hx0
    let y : PeriodicLatticeSite Lut := (fun z => periodicLatticeShiftBack z μ)^[ell - 1] x
    have hφy : phiS hu o y = c.1.1 := by
      show phiS hu o ((fun z => periodicLatticeShiftBack z μ)^[ell - 1] x) = _
      rw [sbIter_nat, hx, sbIter_pathSite]
    have hal : Aligned ell y := (aligned_phiS hp y).mp (by rw [hφy]; exact coarse_aligned _ c.1.2)
    have hyc : y ∈ CoarseLattice Lut ell := mem_CoarseLattice.mpr (fun ν => Nat.mod_eq_zero_of_dvd (hal ν))
    refine ⟨(⟨y, hyc⟩, μ), ?_, ?_⟩
    · rw [CRowIn_pull hp hell]
      have : cbMap hp ((⟨y, hyc⟩ : { y : PeriodicLatticeSite Lut // y ∈ CoarseLattice Lut ell }), μ) = c := by
        unfold cbMap
        apply Prod.ext
        · exact Subtype.ext hφy
        · exact hμ
      rw [this]; exact hc
    · show (x, μ) = (pathSite y μ (ell - 1), μ)
      rw [pathSite_sbIter]

open AdalyFormal.Balaban.AdmissibleSubspace (axisSegment mem_axisSegment corner1 corner2) in
theorem seg_pull (hp : PhiOK hu o ell) (hell : 0 < ell) {y x : PeriodicLatticeSite Lut} (hy : Aligned ell y)
    (hxb : ∀ ν, (y ν).val ≤ (x ν).val ∧ (x ν).val < (y ν).val + ell)
    (base : PeriodicLatticeSite Lut) (base' : PeriodicLatticeSite Lu) (μ : Fin 3)
    (hbase : ∀ ν, ν ≠ μ → phiS hu o base ν = base' ν) (e : PeriodicLatticeEdge Lut)
    (he : e ∈ axisSegment base μ (y μ).val (x μ).val) :
    phiE hu o e ∈ axisSegment base' μ (phiS hu o y μ).val (phiS hu o x μ).val := by
  rw [mem_axisSegment] at he ⊢
  obtain ⟨h1, h2, h3, h4⟩ := he
  have hyx := hxb μ
  have hvx := phiS_val_in_block hp hell hy μ hyx.1 hyx.2
  have hve := phiS_val_in_block hp hell hy (x := e.1) μ h3 (by omega)
  refine ⟨h1, fun ν hν => ?_, by show _ ≤ (phiS hu o e.1 μ).val; omega, by show (phiS hu o e.1 μ).val < _; omega⟩
  · show phiS hu o e.1 ν = base' ν
    rw [← hbase ν hν]
    apply Fin.ext
    simp only [phiS_val, h2 ν hν]

open AdalyFormal.Balaban.AdmissibleSubspace (axisSegment mem_axisSegment corner1 corner2) in
theorem staircase_pull (hp : PhiOK hu o ell) (hell : 0 < ell) {y x : PeriodicLatticeSite Lut} (hy : Aligned ell y)
    (hx : x ∈ blockOf y ell) {b : PeriodicLatticeEdge Lut} (hb : b ∈ staircasePath y x) :
    phiE hu o b ∈ staircasePath (phiS hu o y) (phiS hu o x) := by
  rw [mem_blockOf] at hx
  have hmin : ∀ ν, min (y ν).val (x ν).val = (y ν).val := fun ν => min_eq_left (hx ν).1
  have hmax : ∀ ν, max (y ν).val (x ν).val = (x ν).val := fun ν => max_eq_right (hx ν).1
  have hmin' : ∀ ν, min (phiS hu o y ν).val (phiS hu o x ν).val = (phiS hu o y ν).val := fun ν => by
    have := phiS_val_in_block hp hell hy ν (hx ν).1 (hx ν).2; exact min_eq_left (by omega)
  have hmax' : ∀ ν, max (phiS hu o y ν).val (phiS hu o x ν).val = (phiS hu o x ν).val := fun ν => by
    have := phiS_val_in_block hp hell hy ν (hx ν).1 (hx ν).2; exact max_eq_right (by omega)
  have hc1 : phiS hu o (corner1 y x) = corner1 (phiS hu o y) (phiS hu o x) := phiS_update hu o y x 2
  have hc2 : phiS hu o (corner2 y x) = corner2 (phiS hu o y) (phiS hu o x) := by
    unfold corner2; rw [phiS_update, hc1]
  unfold staircasePath at hb ⊢
  rw [hmin, hmax, hmin, hmax, hmin, hmax] at hb
  rw [hmin', hmax', hmin', hmax', hmin', hmax']
  simp only [Finset.mem_union] at hb ⊢
  rcases hb with (hb | hb) | hb
  · exact Or.inl (Or.inl (seg_pull hp hell hy hx y (phiS hu o y) 2 (fun ν _ => rfl) b hb))
  · exact Or.inl (Or.inr (seg_pull hp hell hy hx (corner1 y x) (corner1 (phiS hu o y) (phiS hu o x)) 1
      (fun ν _ => by rw [← hc1]) b hb))
  · exact Or.inr (seg_pull hp hell hy hx (corner2 y x) (corner2 (phiS hu o y) (phiS hu o x)) 0
      (fun ν _ => by rw [← hc2]) b hb)

end drop


end AdalyFormal.Thin
