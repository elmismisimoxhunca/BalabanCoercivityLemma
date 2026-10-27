import R7Fork.DM4a

/-!
# DM4b -- properties of `C B~` for `B~ in Lambda~` at a GENERAL `Lambda` (a union of 2-blocks), `ell = 2`, flat `Q_1`:
 (i) `C B~` vanishes on every staircase `Gamma_{y,x}` (all coarse `y`), (ii) `Q_1 (C B~) = 0` on ALL rows (touching rows by `Cop_ker`;
 non-touching rows because they read no bond touching `Lambda` and no dropped bond: `droppedBondLast_not_reads`),
 (iii) `||B~||^2 <= ||C B~||^2`, (iv) `C B~` is supported on bonds touching `Lambda`.
Generalises `StatementLaneG.Cop_props_univ` (which is `Lambda = univ` only).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.DirichletMono

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice
  staircasePath mem_axisSegment corner1 corner2 coarseLattice_unique axisSegment)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ReparamCDisjoint (ReadsBond droppedBondLast droppedBondLast_not_mem_staircase
  droppedBondLast_not_reads coarse_coord_add_ell_le)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.IngredientFamily (q1SU2)

theorem seg_in_block {L : PeriodicLatticeExtent} {ell : ℕ} (hL : ∀ ρ, 1 ≤ L ρ)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    {base : PeriodicLatticeSite L} {μ : Fin 3} {a b : ℕ}
    (hbase : ∀ ρ, ρ ≠ μ → (y ρ).val ≤ (base ρ).val ∧ (base ρ).val < (y ρ).val + ell)
    (ha : (y μ).val ≤ a) (hb : b < (y μ).val + ell)
    {e : PeriodicLatticeEdge L} (he : e ∈ axisSegment base μ a b) :
    e.1 ∈ blockOf y ell ∧ periodicLatticeShift e.1 e.2 ∈ blockOf y ell := by
  obtain ⟨h2, h3, h4, h5⟩ := mem_axisSegment.mp he
  have hyN := coarse_coord_add_ell_le hdvd μ (y μ).val (mem_CoarseLattice.mp hy μ) (y μ).isLt
  refine ⟨?_, ?_⟩
  · rw [mem_blockOf]
    intro ρ
    by_cases hρ : ρ = μ
    · subst hρ; constructor <;> omega
    · rw [h3 ρ hρ]; exact hbase ρ hρ
  · rw [mem_blockOf]
    intro ρ
    rw [h2, AdalyFormal.StatementLane2.shift_apply]
    by_cases hρ : ρ = μ
    · subst hρ
      simp only [if_true]
      rw [AdalyFormal.StatementLane2.fin_succ_val ρ (hL ρ), Nat.mod_eq_of_lt (by omega)]
      constructor <;> omega
    · simp only [hρ, if_false]
      rw [h3 ρ hρ]; exact hbase ρ hρ

theorem stair_in_block {L : PeriodicLatticeExtent} {ell : ℕ} (hell : 0 < ell) (hL : ∀ ρ, 1 ≤ L ρ)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    {x : PeriodicLatticeSite L} (hx : x ∈ blockOf y ell) {b : Bond L} (hb : b ∈ staircasePath y x) :
    b.1 ∈ blockOf y ell ∧ periodicLatticeShift b.1 b.2 ∈ blockOf y ell := by
  have hx' := mem_blockOf.mp hx
  unfold staircasePath at hb
  simp only [Finset.mem_union] at hb
  have hmin : ∀ μ : Fin 3, (y μ).val ≤ min (y μ).val (x μ).val := fun μ => le_min le_rfl (hx' μ).1
  have hmax : ∀ μ : Fin 3, max (y μ).val (x μ).val < (y μ).val + ell := fun μ =>
    max_lt (by have := (hx' μ).2; omega) (hx' μ).2
  have hyl : ∀ ρ, (y ρ).val ≤ (y ρ).val ∧ (y ρ).val < (y ρ).val + ell := fun ρ => by
    constructor <;> omega
  have hxl : ∀ ρ, (y ρ).val ≤ (x ρ).val ∧ (x ρ).val < (y ρ).val + ell := hx'
  rcases hb with (hb | hb) | hb
  · exact seg_in_block hL hdvd hy (fun ρ _ => hyl ρ) (hmin 2) (hmax 2) hb
  · refine seg_in_block hL hdvd hy ?_ (hmin 1) (hmax 1) hb
    intro ρ hρ
    unfold corner1
    by_cases h2 : ρ = 2
    · subst h2; simpa using hxl 2
    · rw [Function.update_of_ne h2]; exact hyl ρ
  · refine seg_in_block hL hdvd hy ?_ (hmin 0) (hmax 0) hb
    intro ρ hρ
    unfold corner2 corner1
    by_cases h1 : ρ = 1
    · subst h1; simpa using hxl 1
    · rw [Function.update_of_ne h1]
      by_cases h2 : ρ = 2
      · subst h2; simpa using hxl 2
      · rw [Function.update_of_ne h2]; exact hyl ρ

theorem Cop_props_gen {Lu : PeriodicLatticeExtent} (hd : ∀ μ, 2 ∣ Lu μ + 1) (hu : ∀ μ, 1 ≤ Lu μ)
    {Lam : Set (PeriodicLatticeSite Lu)} (hLB : LamBlockSum 2 Lam)
    (hb : Function.Bijective (H0 Lam (q1SU2 2))) (Bt : Bond Lu → SuTwo)
    (hBt : OnLambdaTildeIn Lam 2 Bt) (hBT : OnLambdaT Lam Bt) :
    (∀ y ∈ CoarseLattice Lu 2, ∀ x ∈ blockOf y 2, ∀ b ∈ staircasePath y x,
        Cop Lam (q1SU2 2) Bt b = 0) ∧
    (∀ c, lineCoarseRestrictSuTwo 2 (Cop Lam (q1SU2 2) Bt) c = 0) ∧
    bondEnergy Bt ≤ ∑ b : Bond Lu, ‖Cop Lam (q1SU2 2) Bt b‖ ^ 2 ∧
    (∀ e : Bond Lu, Cop Lam (q1SU2 2) Bt e ≠ 0 → e.1 ∈ Lam ∨ periodicLatticeShift e.1 e.2 ∈ Lam) := by
  have hell : 0 < 2 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy x hx b hbst
    have hnd : ¬ IsDroppedIn Lam 2 b := by
      rintro ⟨c, -, rfl⟩
      exact droppedBondLast_not_mem_staircase hell hd c y hy x hx hbst
    rw [Cop_id _ _ Bt b hnd]
    by_cases hLP : y ∈ LamPrime 2 Lam
    · exact hBt.1 y hLP x hx b hbst
    · apply hBT b
      rintro (h | h)
      · exact hLP (lamPrime_of_mem hLB hy (stair_in_block hell hu hd hy hx hbst).1 h)
      · exact hLP (lamPrime_of_mem hLB hy (stair_in_block hell hu hd hy hx hbst).2 h)
  · intro c
    by_cases hc : CRowIn 2 Lam c
    · exact Cop_ker Lam (q1SU2 2) hb Bt c hc
    · have hread : ∀ b : Bond Lu, ReadsBond 2 c b → Cop Lam (q1SU2 2) Bt b = 0 := by
        intro b hbr
        have hnd : ¬ IsDroppedIn Lam 2 b := by
          rintro ⟨c', hc', rfl⟩
          by_cases hcc : c = c'
          · subst hcc; exact hc hc'
          · exact droppedBondLast_not_reads hell hd c c' hcc hbr
        rw [Cop_id _ _ Bt b hnd]
        apply hBT b
        have hrb := reads_in_blocks hell hd c b hbr
        have hcm : c.1.1 ∈ CoarseLattice Lu 2 := c.1.2
        have hcp : coarseShift c.1.1 2 c.2 ∈ CoarseLattice Lu 2 := coarseShift_mem_coarseLattice hd c.1.2 c.2
        rintro (h | h)
        · rcases hrb.1 with h1 | h1
          · exact hc (Or.inl (lamPrime_of_mem hLB hcm h1 h))
          · exact hc (Or.inr (lamPrime_of_mem hLB hcp h1 h))
        · rcases hrb.2 with h1 | h1
          · exact hc (Or.inl (lamPrime_of_mem hLB hcm h1 h))
          · exact hc (Or.inr (lamPrime_of_mem hLB hcp h1 h))
      show (1 / (2 : ℝ) ^ 4) • ∑ x ∈ blockOf c.1.1 2, ∑ i ∈ Finset.range 2,
        Cop Lam (q1SU2 2) Bt (AdalyFormal.Balaban.QOne.pathSite x c.2 i, c.2) = 0
      rw [Finset.sum_eq_zero, smul_zero]
      intro x hx
      refine Finset.sum_eq_zero (fun i hi => hread _ ⟨x, hx, i, hi, rfl⟩)
  · unfold bondEnergy
    refine Finset.sum_le_sum (fun b _ => ?_)
    by_cases hd' : IsDroppedIn Lam 2 b
    · rw [hBt.2 b hd']; simp
    · rw [Cop_id _ _ Bt b hd']
  · intro e he
    by_cases hdr : IsDroppedIn Lam 2 e
    · exact dropped_touches_lam hell hd hdr
    · rw [Cop_id Lam (q1SU2 2) Bt e hdr] at he
      by_contra hnt
      exact he (hBT e hnt)

#print axioms seg_in_block
#print axioms stair_in_block
#print axioms Cop_props_gen

end AdalyFormal.DirichletMono
