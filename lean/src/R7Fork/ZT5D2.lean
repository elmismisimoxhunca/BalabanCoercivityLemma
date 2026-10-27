import R7Fork.ZT5D
import R7Fork.ZR6A

/-!
# ZT5D2 -- r6 (R2) on the PROPER tower `TT` (k = 1, ell = 2, M = 2, R = 6, c = 12): every PLAQUETTE of `Ω₀` lies in ONE class cube.
`TT2_coversp : CoversOm0p 2 2 12 1 (TT L)`; `proper_tower_hyps_p` = `proper_tower_hyps` with `CoversOm0p`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- the index-1 cube data: box of side 48, corner `z` with `z₀ ∈ [20,52]`, all corner coordinates `≡ 0 (mod 4)`. -/
theorem TT2_cube1 {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = 120) (z : PeriodicLatticeSite L)
    (hz0 : 20 ≤ (z 0).val ∧ (z 0).val ≤ 52) (hz : GridCorner (bigSide 2 2 1) z) :
    IsClassCube 2 2 12 1 (TT L) (siteBox z (12 * bigSide 2 2 1)) 1 := by
  have hbox : ∀ y : PeriodicLatticeSite L, y ∈ siteBox z (12 * bigSide 2 2 1) ↔
      ((y 0).val + 120 - (z 0).val) % 120 < 48 ∧ ((y 1).val + 120 - (z 1).val) % 120 < 48 ∧
      ((y 2).val + 120 - (z 2).val) % 120 < 48 := by
    intro y
    have := mem_box_iff hN z y (12 * bigSide 2 2 1)
    simpa [bigSide] using this
  have hz0' : (z 0).val < 120 := by have := (z 0).isLt; have := hN 0; omega
  have hzmem : z ∈ siteBox z (12 * bigSide 2 2 1) := by
    rw [hbox]; have := (z 1).isLt; have := (z 2).isLt; have := hN 1; have := hN 2; refine ⟨?_, ?_, ?_⟩ <;> omega
  have hsub : ∀ y ∈ siteBox z (12 * bigSide 2 2 1), 20 ≤ (y 0).val ∧ (y 0).val < 100 := by
    intro y hy
    rw [hbox] at hy
    have h0 := hy.1; have := (y 0).isLt; have := hN 0; omega
  refine ⟨⟨le_rfl, ⟨z, hz, rfl⟩, ?_, ?_⟩, ?_⟩
  · intro y hy
    left
    simp only [towerBj, TT, if_neg (by decide : (1 : ℕ) ≠ 0), if_true,
      if_neg (by decide : (1 + 1 : ℕ) ≠ 0), if_neg (by decide : (1 + 1 : ℕ) ≠ 1), OmB,
      Set.mem_diff, Set.mem_setOf_eq, Set.mem_empty_iff_false, not_false_eq_true, and_true]
    exact hsub y hy
  · refine ⟨z, hzmem, ?_⟩
    simp only [towerBj, TT, if_neg (by decide : (1 : ℕ) ≠ 0), if_true,
      if_neg (by decide : (1 + 1 : ℕ) ≠ 0), if_neg (by decide : (1 + 1 : ℕ) ≠ 1), OmB,
      Set.mem_diff, Set.mem_setOf_eq, Set.mem_empty_iff_false, not_false_eq_true, and_true]
    omega
  · intro i hi
    by_contra hne
    have hi0 : i = 0 := by have := hi.1; omega
    subst hi0
    obtain ⟨_, ⟨z', _, hz'⟩, _⟩ := hi
    have : siteBox z (12 * bigSide 2 2 1) = siteBox z' (12 * bigSide 2 2 0) := hz'.symm ▸ rfl
    have h48 : siteBox z 48 ⊆ siteBox z' 24 := by
      have h := this.subset
      simpa [bigSide] using h
    exact box48_not_sub_box24 hN z z' h48

/-- the index-0 cube data: box of side 24, corner `z` with `z₀ ∈ {8, 88}`, corner coordinates `≡ 0 (mod 2)`, and a witness
`w` in the box lying in the shell `Ω₀ \ Ω₁`. -/
theorem TT2_cube0 {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = 120) (z : PeriodicLatticeSite L)
    (hz0 : (z 0).val = 8 ∨ (z 0).val = 88) (hz : GridCorner (bigSide 2 2 0) z)
    (w : PeriodicLatticeSite L) (hw : w ∈ siteBox z (12 * bigSide 2 2 0))
    (hw0 : 8 ≤ (w 0).val ∧ (w 0).val < 112 ∧ ¬ (20 ≤ (w 0).val ∧ (w 0).val < 100)) :
    IsClassCube 2 2 12 1 (TT L) (siteBox z (12 * bigSide 2 2 0)) 0 := by
  have hbox : ∀ y : PeriodicLatticeSite L, y ∈ siteBox z (12 * bigSide 2 2 0) ↔
      ((y 0).val + 120 - (z 0).val) % 120 < 24 ∧ ((y 1).val + 120 - (z 1).val) % 120 < 24 ∧
      ((y 2).val + 120 - (z 2).val) % 120 < 24 := by
    intro y
    have := mem_box_iff hN z y (12 * bigSide 2 2 0)
    simpa [bigSide] using this
  have hsub : ∀ y ∈ siteBox z (12 * bigSide 2 2 0), 8 ≤ (y 0).val ∧ (y 0).val < 112 := by
    intro y hy
    rw [hbox] at hy
    have h0 := hy.1; have := (y 0).isLt; have := hN 0; omega
  refine ⟨⟨by omega, ⟨z, hz, rfl⟩, ?_, ?_⟩, ?_⟩
  · intro y hy
    have h8 := hsub y hy
    by_cases hy20 : 20 ≤ (y 0).val ∧ (y 0).val < 100
    · right
      simp only [towerBj, TT, if_neg (by decide : (1 : ℕ) ≠ 0), if_true,
        if_neg (by decide : (0 + 1 : ℕ) ≠ 0), OmB, Set.mem_diff, Set.mem_setOf_eq, if_pos rfl]
      simp only [towerBj, TT, if_pos rfl, if_neg (by decide : (1 + 1 : ℕ) ≠ 0),
        if_neg (by decide : (1 + 1 : ℕ) ≠ 1)]
      exact ⟨hy20, by simp⟩
    · left
      simp only [towerBj, TT, if_true, if_neg (by decide : (0 + 1 : ℕ) ≠ 0), OmA, OmB,
        Set.mem_diff, Set.mem_setOf_eq]
      exact ⟨h8, by omega⟩
  · refine ⟨w, hw, ?_⟩
    simp only [towerBj, TT, if_true, if_neg (by decide : (0 + 1 : ℕ) ≠ 0), if_pos rfl, OmA, OmB,
      Set.mem_diff, Set.mem_setOf_eq]
    exact ⟨⟨hw0.1, hw0.2.1⟩, by omega⟩
  · intro i hi
    by_contra hne
    have hi1 : i = 1 := by have := hi.1; omega
    subst hi1
    obtain ⟨_, ⟨z', _, hz'⟩, _⟩ := hi
    have : siteBox z' (12 * bigSide 2 2 1) = siteBox z (12 * bigSide 2 2 0) := hz'.symm ▸ rfl
    have h48 : siteBox z' 48 ⊆ siteBox z 24 := by
      have h := this.subset
      simpa [bigSide] using h
    exact box48_not_sub_box24 hN z' z h48

/-! ### coordinates of the periodic shift, adjacency -/

theorem shift_val {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = 120) (s : PeriodicLatticeSite L) (μ ρ : Fin 3) :
    ((periodicLatticeShift s μ) ρ).val = if ρ = μ then ((s ρ).val + 1) % 120 else (s ρ).val := by
  unfold periodicLatticeShift
  by_cases h : ρ = μ
  · subst h
    simp only [Function.update_self, if_true]
    rw [Fin.val_add, Fin.val_one']
    have h1 := hN ρ
    have h2 : 1 % (L ρ + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h2]
    generalize ((s ρ).val) = v
    rw [h1]
  · simp [Function.update_of_ne h, h]

/-- `w` is adjacent to `x`: each coordinate equal or one step up (periodic, 120). -/
def Adj {L : PeriodicLatticeExtent} (x w : PeriodicLatticeSite L) : Prop :=
  ∀ ρ : Fin 3, (w ρ).val = (x ρ).val ∨ (w ρ).val = ((x ρ).val + 1) % 120

theorem adj_refl {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) : Adj x x := fun _ => Or.inl rfl

theorem adj_shift {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = 120) {x s : PeriodicLatticeSite L}
    (h : Adj x s) (μ : Fin 3) (hμ : (s μ).val = (x μ).val) : Adj x (periodicLatticeShift s μ) := by
  intro ρ
  rw [shift_val hN]
  by_cases hρ : ρ = μ
  · subst hρ; simp only [if_true]; right; rw [hμ]
  · simp only [if_neg hρ]; exact h ρ

theorem adj_shift_coord {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = 120) (s : PeriodicLatticeSite L)
    {μ ν : Fin 3} (hne : ν ≠ μ) : ((periodicLatticeShift s μ) ν).val = (s ν).val := by
  rw [shift_val hN, if_neg hne]

/-- the cube for a base site `x ∈ Ω₀`: a class cube containing every site adjacent to `x` that lies in `Ω₀`. -/
theorem TT2_cube_nbhd {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = 120) (x : PeriodicLatticeSite L)
    (hx : 8 ≤ (x 0).val ∧ (x 0).val < 112) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube 2 2 12 1 (TT L) sites j ∧
      ∀ w : PeriodicLatticeSite L, Adj x w → 8 ≤ (w 0).val → (w 0).val < 112 → w ∈ sites := by
  have hx120 : ∀ μ, (x μ).val < 120 := fun μ => by have := (x μ).isLt; have := hN μ; omega
  by_cases hA : 20 ≤ (x 0).val ∧ (x 0).val < 99
  · let c : Fin 3 → ℕ := fun μ => if μ = 0 then min (4 * ((x 0).val / 4)) 52 else 4 * ((x μ).val / 4)
    have hc : ∀ μ, c μ < L μ + 1 := fun μ => by
      have := hN μ; have := hx120 μ; simp only [c]; split_ifs <;> omega
    let z : PeriodicLatticeSite L := fun μ => ⟨c μ, hc μ⟩
    have hz0 : (z 0).val = min (4 * ((x 0).val / 4)) 52 := by simp [z, c]
    have hz1 : (z 1).val = 4 * ((x 1).val / 4) := by simp [z, c]
    have hz2 : (z 2).val = 4 * ((x 2).val / 4) := by simp [z, c]
    have hgrid : GridCorner (bigSide 2 2 1) z := by
      intro μ; fin_cases μ <;> simp [bigSide, hz0, hz1, hz2] <;> omega
    refine ⟨siteBox z (12 * bigSide 2 2 1), 1, TT2_cube1 hN z ⟨by rw [hz0]; omega, by rw [hz0]; omega⟩ hgrid, ?_⟩
    intro w hw _ _
    have hbox : w ∈ siteBox z (12 * bigSide 2 2 1) ↔
        ((w 0).val + 120 - (z 0).val) % 120 < 48 ∧ ((w 1).val + 120 - (z 1).val) % 120 < 48 ∧
        ((w 2).val + 120 - (z 2).val) % 120 < 48 := by
      have := mem_box_iff hN z w (12 * bigSide 2 2 1)
      simpa [bigSide] using this
    rw [hbox]
    have w0 := hw 0; have w1 := hw 1; have w2 := hw 2
    have := hx120 1; have := hx120 2
    rw [hz0, hz1, hz2]
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · by_cases hB : (x 0).val < 20
    · let c : Fin 3 → ℕ := fun μ => if μ = 0 then 8 else 2 * ((x μ).val / 2)
      have hc : ∀ μ, c μ < L μ + 1 := fun μ => by
        have := hN μ; have := hx120 μ; simp only [c]; split_ifs <;> omega
      let z : PeriodicLatticeSite L := fun μ => ⟨c μ, hc μ⟩
      have hz0 : (z 0).val = 8 := by simp [z, c]
      have hz1 : (z 1).val = 2 * ((x 1).val / 2) := by simp [z, c]
      have hz2 : (z 2).val = 2 * ((x 2).val / 2) := by simp [z, c]
      have hgrid : GridCorner (bigSide 2 2 0) z := by
        intro μ; fin_cases μ <;> simp [bigSide, hz0, hz1, hz2] <;> omega
      have hbox : ∀ w : PeriodicLatticeSite L, w ∈ siteBox z (12 * bigSide 2 2 0) ↔
          ((w 0).val + 120 - (z 0).val) % 120 < 24 ∧ ((w 1).val + 120 - (z 1).val) % 120 < 24 ∧
          ((w 2).val + 120 - (z 2).val) % 120 < 24 := by
        intro w
        have := mem_box_iff hN z w (12 * bigSide 2 2 0)
        simpa [bigSide] using this
      have hxb : x ∈ siteBox z (12 * bigSide 2 2 0) := by
        rw [hbox]; have := hx120 1; have := hx120 2; rw [hz0, hz1, hz2]; refine ⟨?_, ?_, ?_⟩ <;> omega
      refine ⟨siteBox z (12 * bigSide 2 2 0), 0, TT2_cube0 hN z (Or.inl hz0) hgrid x hxb ⟨hx.1, hx.2, by omega⟩, ?_⟩
      intro w hw _ _
      rw [hbox]
      have w0 := hw 0; have w1 := hw 1; have w2 := hw 2
      have := hx120 1; have := hx120 2
      rw [hz0, hz1, hz2]
      refine ⟨?_, ?_, ?_⟩ <;> omega
    · let c : Fin 3 → ℕ := fun μ => if μ = 0 then 88 else 2 * ((x μ).val / 2)
      have hc : ∀ μ, c μ < L μ + 1 := fun μ => by
        have := hN μ; have := hx120 μ; simp only [c]; split_ifs <;> omega
      let z : PeriodicLatticeSite L := fun μ => ⟨c μ, hc μ⟩
      have hz0 : (z 0).val = 88 := by simp [z, c]
      have hz1 : (z 1).val = 2 * ((x 1).val / 2) := by simp [z, c]
      have hz2 : (z 2).val = 2 * ((x 2).val / 2) := by simp [z, c]
      have hgrid : GridCorner (bigSide 2 2 0) z := by
        intro μ; fin_cases μ <;> simp [bigSide, hz0, hz1, hz2] <;> omega
      have hbox : ∀ w : PeriodicLatticeSite L, w ∈ siteBox z (12 * bigSide 2 2 0) ↔
          ((w 0).val + 120 - (z 0).val) % 120 < 24 ∧ ((w 1).val + 120 - (z 1).val) % 120 < 24 ∧
          ((w 2).val + 120 - (z 2).val) % 120 < 24 := by
        intro w
        have := mem_box_iff hN z w (12 * bigSide 2 2 0)
        simpa [bigSide] using this
      let w0 : PeriodicLatticeSite L := Function.update z 0 ⟨111, by have := hN 0; omega⟩
      have hw0v : (w0 0).val = 111 := by simp [w0]
      have hw0b : w0 ∈ siteBox z (12 * bigSide 2 2 0) := by
        rw [hbox]
        have h1 : (w0 1).val = (z 1).val := by simp [w0, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]
        have h2 : (w0 2).val = (z 2).val := by simp [w0, Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
        rw [hw0v, h1, h2, hz0]
        have := (z 1).isLt; have := (z 2).isLt; have := hN 1; have := hN 2
        refine ⟨?_, ?_, ?_⟩ <;> omega
      refine ⟨siteBox z (12 * bigSide 2 2 0), 0,
        TT2_cube0 hN z (Or.inr hz0) hgrid w0 hw0b ⟨by omega, by omega, by omega⟩, ?_⟩
      intro w hw hw8 hw112
      rw [hbox]
      have w0' := hw 0; have w1 := hw 1; have w2 := hw 2
      have := hx120 1; have := hx120 2
      rw [hz0, hz1, hz2]
      refine ⟨?_, ?_, ?_⟩ <;> omega

#print axioms shift_val
#print axioms TT2_cube_nbhd

/-- **R2 on the proper tower**: every plaquette of `Ω₀` (all four boundary bonds with both endpoints in `Ω₀`) lies in one class cube. -/
theorem TT2_coversp_plaq {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = 120) :
    CoversPlaqOm0c 2 2 12 1 (TT L) := by
  intro p hp
  have hmu : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  have hnu : p.2.1.2 ≠ p.2.1.1 := fun h => hmu h.symm
  have hmem : ∀ e : PeriodicLatticeEdge L, e ∈ periodicPlaquetteBoundaryEdges p ↔
      (e = (p.1, p.2.1.1) ∨ e = (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∨
        e = (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∨ e = (p.1, p.2.1.2)) := by
    intro e
    simp [periodicPlaquetteBoundaryEdges]
  have hx : 8 ≤ (p.1 0).val ∧ (p.1 0).val < 112 := by
    have := (hp (p.1, p.2.1.1) ((hmem _).mpr (Or.inl rfl))).1
    simpa [TT, OmA] using this
  obtain ⟨sites, j, hc, hall⟩ := TT2_cube_nbhd hN p.1 hx
  refine ⟨sites, j, hc, fun e he => ?_⟩
  have hcb := hp e he
  simp only [TT, if_true, OmA, Set.mem_setOf_eq] at hcb
  have a0 : Adj p.1 p.1 := adj_refl _
  have aμ : Adj p.1 (periodicLatticeShift p.1 p.2.1.1) := adj_shift hN a0 _ rfl
  have aν : Adj p.1 (periodicLatticeShift p.1 p.2.1.2) := adj_shift hN a0 _ rfl
  have aμν : Adj p.1 (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2) :=
    adj_shift hN aμ _ (adj_shift_coord hN _ hnu)
  have aνμ : Adj p.1 (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.2) p.2.1.1) :=
    adj_shift hN aν _ (adj_shift_coord hN _ hmu)
  refine ⟨?_, ?_⟩
  · rcases (hmem e).mp he with rfl | rfl | rfl | rfl
    · exact hall _ a0 hcb.1.1 hcb.1.2
    · exact hall _ aμ hcb.1.1 hcb.1.2
    · exact hall _ aν hcb.1.1 hcb.1.2
    · exact hall _ a0 hcb.1.1 hcb.1.2
  · rcases (hmem e).mp he with rfl | rfl | rfl | rfl
    · exact hall _ aμ hcb.2.1 hcb.2.2
    · exact hall _ aμν hcb.2.1 hcb.2.2
    · exact hall _ aνμ hcb.2.1 hcb.2.2
    · exact hall _ aν hcb.2.1 hcb.2.2

theorem TT2_coversp {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = 120) : CoversOm0p 2 2 12 1 (TT L) :=
  ⟨TT2_covers hN, TT2_coversp_plaq hN⟩

/-- `proper_tower_hyps` with the r6 coverage `CoversOm0p` (sites AND plaquettes). -/
theorem proper_tower_hyps_p {Lu Lf : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60)
    (hLf : ∀ μ, Lf μ + 1 = 120) {α₀ : ℝ} (hα : 0 < α₀) (hα1 : α₀ ≤ 1 / 2) :
    TorusOK 2 2 Lu ∧ Admissible 2 2 6 1 (TT Lf) ∧ CoversOm0p 2 2 12 1 (TT Lf) ∧
    (∃ p : PeriodicLatticeSite Lf, p ∈ towerBj (TT Lf) 0) ∧
    (∃ p : PeriodicLatticeSite Lf, p ∈ towerBj (TT Lf) 1) ∧
    (∃ p : PeriodicLatticeSite Lf, p ∉ (TT Lf).Om 0) ∧
    LambdaOK2 (Lu := Lu) (Lf := Lf) 2 2 6 1 (TT Lf) (LamT Lu) ∧
    (LamPrime 2 (LamT Lu)).Nonempty ∧
    (∃ U : LinkCfg Lf, PerCubeRegular2 2 2 12 1 (TT Lf) α₀ (((2 : ℕ) : ℝ) ^ 1)⁻¹ U ∧
       ¬ ∃ g : PeriodicLatticeSite Lf → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
    (∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn (LamT Lu) 2 Bt ∧ OnLambdaT (LamT Lu) Bt ∧
       0 < bondEnergy Bt) := by
  obtain ⟨h1, h2, _, rest⟩ := proper_tower_hyps hLu hLf hα hα1
  exact ⟨h1, h2, TT2_coversp hLf, rest⟩

#print axioms TT2_coversp_plaq
#print axioms TT2_coversp
#print axioms proper_tower_hyps_p

#print axioms TT2_cube1
#print axioms TT2_cube0

end AdalyFormal.StatementLaneG
