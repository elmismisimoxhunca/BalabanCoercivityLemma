import ZT5C

/-!
# ZT5D -- NON-VACUITY of the r5 statement on a PROPER multistratum tower at `k = 1` (the `TT` tower of `ZR2B9`, ported to `M = 2 = ell^1`, `R = 6`, `c = 12`).

Geometry (fine torus `Lf`, 120 sites per direction; unit torus `Lu`, 60 sites): `Ω₁ = {20 ≤ x₀ < 100}`, `Ω₀ = {8 ≤ x₀ < 112}` (= `Ω₁` widened by `R M = 12`, ℓ¹ distance,
2-block closed), `Ω₂ = ∅`; `Λ = {30 ≤ y₀ < 34}` (a genuine sum of 2-blocks, `Λ' ≠ ∅`), non-flat `U` (a spike), and a NONZERO `B̃ ∈ Λ̃`.
What is proved: every HYPOTHESIS of `CoercG8At 2 2 6 1 .. 12 ..` is satisfiable here and `Λ̃` carries a nonzero `B̃`.
What is NOT proved: the conclusion `InstIneq` at this point (`WellDef` / coercivity of `G⁻¹` at a two-stratum tower is open in the tree).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice staircasePath)
open AdalyFormal.Balaban.FullReparamC (freeBond freeBond_not_mem_staircase freeBond_not_dropped freeBond_coord_zero)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

theorem TT2_admissible {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = 120) :
    Admissible 2 2 6 1 (TT L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases h0 : j = 0
    · subst h0; simp only [TT, if_true, if_neg (by decide : (0 + 1 : ℕ) ≠ 0), if_true, OmA, OmB,
        Set.mem_setOf_eq] at hx ⊢
      omega
    · by_cases h1 : j = 1
      · subst h1; simp [TT] at hx
      · have : j + 1 ≠ 0 := by omega
        have : j + 1 ≠ 1 := by omega
        simp [TT, *] at hx
  · intro j hj
    have h0 : j ≠ 0 := by omega
    have h1 : j ≠ 1 := by omega
    simp [TT, h0, h1]
  · intro j hj μ
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp [bigSide, hN μ] <;> omega
  · intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · intro x hx y hy
      simp only [TT, if_true, OmA, Set.mem_setOf_eq] at hx ⊢
      have := hy 0
      simp [bigSide] at this
      omega
    · intro x hx y hy
      simp only [TT, if_neg (by decide : (1 : ℕ) ≠ 0), if_true, OmB, Set.mem_setOf_eq] at hx ⊢
      have := hy 0
      simp [bigSide] at this
      omega
  · intro j hj x hx y hy
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · simp only [TT, if_true, if_neg (by decide : (0 + 1 : ℕ) ≠ 0), OmA, OmB, Set.mem_setOf_eq,
        not_and_or, not_le, not_lt] at hx hy
      have hxl : (x 0).val < 120 := by have := (x 0).isLt; have := hN 0; omega
      have hlt : 12 < pcd (L 0 + 1) (x 0).val (y 0).val :=
        pcd_far120 _ _ _ (hN 0) hx hxl hy
      unfold pdist
      show 6 * bigSide 2 2 0 < _
      simp only [bigSide, pow_zero, mul_one]
      exact lt_of_lt_of_le hlt
        (Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
    · simp [TT] at hy
  · intro x
    simp only [TT, if_true, if_neg (by decide : (1 : ℕ) ≠ 0), OmA, OmB, Set.mem_setOf_eq]
    constructor
    · intro hx
      have hx120 : (x 0).val < 120 := by have := (x 0).isLt; have := hN 0; omega
      let v : ℕ := if (x 0).val < 20 then 20 else if (x 0).val < 100 then (x 0).val else 99
      have hv : v < L 0 + 1 := by have := hN 0; simp only [v]; split_ifs <;> omega
      refine ⟨Function.update x 0 ⟨v, hv⟩, ?_, x, fun μ => rfl, ?_⟩
      · simp only [Function.update_self]; simp only [v]; split_ifs <;> omega
      · unfold pdist
        rw [Finset.sum_eq_single (0 : Fin 3)]
        · simp only [Function.update_self]
          have := pcd_clamp120 (L 0 + 1) (x 0).val (hN 0) hx
          simpa [v, bigSide] using this
        · intro μ _ h
          rw [Function.update_of_ne h, pcd_self]
        · intro h; exact absurd (Finset.mem_univ _) h
    · rintro ⟨y, hy, z, hz, hd⟩
      have hz0 : (z 0).val / 2 = (x 0).val / 2 := by simpa using hz 0
      have hlt := Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (z μ).val (y μ).val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      have h12 : pcd (L 0 + 1) (z 0).val (y 0).val ≤ 12 := by
        have := le_trans hlt hd
        simpa [bigSide] using this
      have hz120 : (z 0).val < 120 := by have := (z 0).isLt; have := hN 0; omega
      have hzr := pcd_near120 _ _ _ (hN 0) hz120 hy h12
      omega

/-- a box of side 48 is never contained in a box of side 24 (120-torus) -/
theorem box48_not_sub_box24 {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = 120)
    (z z' : PeriodicLatticeSite L) : ¬ (siteBox z 48 ⊆ siteBox z' 24) := by
  intro h
  have hz0 : (z 0).val < 120 := by have := (z 0).isLt; have := hN 0; omega
  have hv : ((z 0).val + 47) % 120 < L 0 + 1 := by have := hN 0; omega
  let w : PeriodicLatticeSite L := Function.update z 0 ⟨((z 0).val + 47) % 120, hv⟩
  have hw : w ∈ siteBox z 48 := by
    rw [mem_box_iff hN]
    refine ⟨?_, ?_, ?_⟩
    · simp only [w, Function.update_self]; omega
    · simp only [w, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]; omega
    · simp only [w, Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]; omega
  have hzz : z ∈ siteBox z 48 := by
    rw [mem_box_iff hN]; refine ⟨?_, ?_, ?_⟩ <;> omega
  have h1 := (mem_box_iff hN _ _ _).mp (h hzz)
  have h2 := (mem_box_iff hN _ _ _).mp (h hw)
  simp only [w, Function.update_self] at h2
  have hz'0 : (z' 0).val < 120 := by have := (z' 0).isLt; have := hN 0; omega
  omega

theorem TT2_covers {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = 120) :
    CoversOm0c 2 2 12 1 (TT L) := by
  intro x hx
  simp only [TT, if_true, OmA, Set.mem_setOf_eq] at hx
  have hx120 : ∀ μ, (x μ).val < 120 := fun μ => by have := (x μ).isLt; have := hN μ; omega
  by_cases hB : 20 ≤ (x 0).val ∧ (x 0).val < 100
  · -- index-1 cube: side 48, corners multiples of 4
    let c : Fin 3 → ℕ := fun μ => if μ = 0 then min (4 * ((x 0).val / 4)) 52 else 4 * ((x μ).val / 4)
    have hc : ∀ μ, c μ < L μ + 1 := fun μ => by
      have := hN μ; have := hx120 μ; simp only [c]; split_ifs <;> omega
    let z : PeriodicLatticeSite L := fun μ => ⟨c μ, hc μ⟩
    have hz0 : (z 0).val = min (4 * ((x 0).val / 4)) 52 := by simp [z, c]
    have hz1 : (z 1).val = 4 * ((x 1).val / 4) := by simp [z, c]
    have hz2 : (z 2).val = 4 * ((x 2).val / 4) := by simp [z, c]
    have hbox : ∀ y : PeriodicLatticeSite L, y ∈ siteBox z (12 * bigSide 2 2 1) ↔
        ((y 0).val + 120 - (z 0).val) % 120 < 48 ∧ ((y 1).val + 120 - (z 1).val) % 120 < 48 ∧
        ((y 2).val + 120 - (z 2).val) % 120 < 48 := by
      intro y
      have := mem_box_iff hN z y (12 * bigSide 2 2 1)
      simpa [bigSide] using this
    have hxmem : x ∈ siteBox z (12 * bigSide 2 2 1) := by
      rw [hbox]; have := hx120 1; have := hx120 2; rw [hz0, hz1, hz2]; refine ⟨?_, ?_, ?_⟩ <;> omega
    have hsub : ∀ y ∈ siteBox z (12 * bigSide 2 2 1), 20 ≤ (y 0).val ∧ (y 0).val < 100 := by
      intro y hy
      rw [hbox] at hy
      have h0 := hy.1; have := hx120 0; have := (y 0).isLt; have := hN 0; rw [hz0] at h0; omega
    refine ⟨siteBox z (12 * bigSide 2 2 1), 1, ⟨⟨le_rfl, ⟨z, ?_, rfl⟩, ?_, ?_⟩, ?_⟩, hxmem⟩
    · intro μ; fin_cases μ <;> simp [bigSide, hz0, hz1, hz2] <;> omega
    · intro y hy
      left
      simp only [towerBj, TT, if_neg (by decide : (1 : ℕ) ≠ 0), if_true,
        if_neg (by decide : (1 + 1 : ℕ) ≠ 0), if_neg (by decide : (1 + 1 : ℕ) ≠ 1), OmB,
        Set.mem_diff, Set.mem_setOf_eq, Set.mem_empty_iff_false, not_false_eq_true, and_true]
      exact hsub y hy
    · refine ⟨x, hxmem, ?_⟩
      simp only [towerBj, TT, if_neg (by decide : (1 : ℕ) ≠ 0), if_true,
        if_neg (by decide : (1 + 1 : ℕ) ≠ 0), if_neg (by decide : (1 + 1 : ℕ) ≠ 1), OmB,
        Set.mem_diff, Set.mem_setOf_eq, Set.mem_empty_iff_false, not_false_eq_true, and_true]
      exact hB
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
  · -- index-0 cube: side 24, corners multiples of 2; shell `[8,20)` uses `z₀ = 8`, shell `[100,112)` uses `z₀ = 88`
    let c : Fin 3 → ℕ := fun μ => if μ = 0 then (if (x 0).val < 60 then 8 else 88) else 2 * ((x μ).val / 2)
    have hc : ∀ μ, c μ < L μ + 1 := fun μ => by
      have := hN μ; have := hx120 μ; simp only [c]; split_ifs <;> omega
    let z : PeriodicLatticeSite L := fun μ => ⟨c μ, hc μ⟩
    have hz0 : (z 0).val = (if (x 0).val < 60 then 8 else 88) := by simp [z, c]
    have hz1 : (z 1).val = 2 * ((x 1).val / 2) := by simp [z, c]
    have hz2 : (z 2).val = 2 * ((x 2).val / 2) := by simp [z, c]
    have hbox : ∀ y : PeriodicLatticeSite L, y ∈ siteBox z (12 * bigSide 2 2 0) ↔
        ((y 0).val + 120 - (z 0).val) % 120 < 24 ∧ ((y 1).val + 120 - (z 1).val) % 120 < 24 ∧
        ((y 2).val + 120 - (z 2).val) % 120 < 24 := by
      intro y
      have := mem_box_iff hN z y (12 * bigSide 2 2 0)
      simpa [bigSide] using this
    have hxmem : x ∈ siteBox z (12 * bigSide 2 2 0) := by
      rw [hbox]; have := hx120 1; have := hx120 2; rw [hz0, hz1, hz2]
      have hx0 : 8 ≤ (x 0).val ∧ (x 0).val < 112 := hx
      refine ⟨?_, ?_, ?_⟩ <;> (try split_ifs) <;> omega
    have hsub : ∀ y ∈ siteBox z (12 * bigSide 2 2 0), 8 ≤ (y 0).val ∧ (y 0).val < 112 := by
      intro y hy
      rw [hbox] at hy
      have h0 := hy.1; have := hx120 0; have := (y 0).isLt; have := hN 0; rw [hz0] at h0
      split_ifs at h0 <;> omega
    refine ⟨siteBox z (12 * bigSide 2 2 0), 0, ⟨⟨by omega, ⟨z, ?_, rfl⟩, ?_, ?_⟩, ?_⟩, hxmem⟩
    · intro μ; fin_cases μ <;> simp [bigSide, hz0, hz1, hz2] <;> (try split_ifs) <;> omega
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
    · refine ⟨x, hxmem, ?_⟩
      simp only [towerBj, TT, if_true, if_neg (by decide : (0 + 1 : ℕ) ≠ 0), if_pos rfl, OmA, OmB,
        Set.mem_diff, Set.mem_setOf_eq]
      exact ⟨hx, by omega⟩
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

/-! ### `Λ` = a slab of 2-blocks in the unit torus -/

def LamT (Lu : PeriodicLatticeExtent) : Set (PeriodicLatticeSite Lu) := {y | 30 ≤ (y 0).val ∧ (y 0).val < 34}

theorem pcd_far60' (N a b : ℕ) (hN : N = 60) (ha : 30 ≤ a ∧ a < 34) (hb : b < 10 ∨ 50 ≤ b) (hb2 : b < 60) :
    12 < pcd N a b := by
  subst hN; unfold pcd; split_ifs <;> omega

theorem LamT_ok {Lu Lf : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60)
    (hLf : ∀ μ, Lf μ + 1 = 120) :
    LambdaOK (Lu := Lu) (Lf := Lf) 2 2 6 1 (TT Lf) (LamT Lu) := by
  have hemb : ∀ (y : PeriodicLatticeSite Lu) (μ : Fin 3), 2 ^ 1 * (y μ).val < Lf μ + 1 := by
    intro y μ
    have h1 := (y μ).isLt; have h2 := hLu μ; have h3 := hLf μ; omega
  refine ⟨?_, fun y μ => ⟨2 ^ 1 * (y μ).val, hemb y μ⟩, ?_, ?_, ?_⟩
  · intro x hx y hy
    have := hy 0
    simp only [LamT, Set.mem_setOf_eq] at hx ⊢
    omega
  · intro y μ; rfl
  · intro y hy
    simp only [LamT, Set.mem_setOf_eq] at hy
    simp only [TT, if_neg (by decide : (1 : ℕ) ≠ 0), if_true, OmB, Set.mem_setOf_eq]
    show 20 ≤ 2 ^ 1 * (y 0).val ∧ 2 ^ 1 * (y 0).val < 100
    omega
  · intro y hy y' hy'
    simp only [LamT, Set.mem_setOf_eq] at hy
    simp only [TT, if_neg (by decide : (1 : ℕ) ≠ 0), if_true, OmB, Set.mem_setOf_eq, not_and_or,
      not_le, not_lt] at hy'
    have hy'0 : (y' 0).val < 10 ∨ 50 ≤ (y' 0).val := by
      change (2 ^ 1 * (y' 0).val < 20) ∨ (100 ≤ 2 ^ 1 * (y' 0).val) at hy'
      omega
    have hy'1 : (y' 0).val < 60 := by have := (y' 0).isLt; have := hLu 0; omega
    show 6 * 2 < pdist y y'
    have hlt : 12 < pcd (Lu 0 + 1) (y 0).val (y' 0).val :=
      pcd_far60' _ _ _ (hLu 0) hy hy'0 hy'1
    unfold pdist
    exact lt_of_lt_of_le hlt
      (Finset.single_le_sum (f := fun μ : Fin 3 => pcd (Lu μ + 1) (y μ).val (y' μ).val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))

theorem LamT_blockSum {Lu : PeriodicLatticeExtent} : LamBlockSum 2 (LamT Lu) := by
  intro x hx
  simp only [LamT, Set.mem_setOf_eq] at hx
  let y : PeriodicLatticeSite Lu := fun μ => ⟨(x μ).val - (x μ).val % 2, by
    have := (x μ).isLt; omega⟩
  refine ⟨y, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_CoarseLattice]
    intro μ
    show ((x μ).val - (x μ).val % 2) % 2 = 0
    omega
  · intro x' hx'
    rw [mem_blockOf] at hx'
    have := hx' 0
    simp only [LamT, Set.mem_setOf_eq]
    show 30 ≤ (x' 0).val ∧ (x' 0).val < 34
    have h0 : (y 0).val = (x 0).val - (x 0).val % 2 := rfl
    omega
  · rw [mem_blockOf]
    intro μ
    show (x μ).val - (x μ).val % 2 ≤ (x μ).val ∧ (x μ).val < (x μ).val - (x μ).val % 2 + 2
    omega

theorem LamT_lamPrime_nonempty {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) :
    (LamPrime 2 (LamT Lu)).Nonempty :=
  LamT_blockSum.lamPrime_nonempty ⟨fun μ => ⟨if μ = 0 then 30 else 0, by have := hLu μ; split_ifs <;> omega⟩,
    by simp [LamT]⟩

/-! ### a nonzero `B̃ ∈ Λ̃` -/

def y30 (Lu : PeriodicLatticeExtent) (hLu : ∀ μ, Lu μ + 1 = 60) : PeriodicLatticeSite Lu :=
  fun μ => ⟨if μ = 0 then 30 else 0, by have := hLu μ; split_ifs <;> omega⟩

theorem y30_coarse {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) :
    y30 Lu hLu ∈ CoarseLattice Lu 2 := by
  rw [mem_CoarseLattice]
  intro μ
  show (if μ = 0 then 30 else 0) % 2 = 0
  split_ifs <;> norm_num

noncomputable def Bseed30 (Lu : PeriodicLatticeExtent) (hLu : ∀ μ, Lu μ + 1 = 60) : Bond Lu → SuTwo :=
  Pi.single (freeBond 2 (y30 Lu hLu)) suTwoWitness

theorem Bseed30_props {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) :
    OnLambdaTildeIn (LamT Lu) 2 (Bseed30 Lu hLu) ∧ OnLambdaT (LamT Lu) (Bseed30 Lu hLu) ∧
      0 < bondEnergy (Bseed30 Lu hLu) := by
  have hdvd : ∀ μ : Fin 3, 2 ∣ Lu μ + 1 := fun μ => by rw [hLu μ]; norm_num
  have hoff : ∀ b : Bond Lu, b ≠ freeBond 2 (y30 Lu hLu) → Bseed30 Lu hLu b = 0 := fun b hb =>
    Pi.single_eq_of_ne hb _
  have hOn : OnLambdaT (LamT Lu) (Bseed30 Lu hLu) := by
    intro b hb
    by_cases hbe : b = freeBond 2 (y30 Lu hLu)
    · exfalso
      apply hb
      have hfit : ((y30 Lu hLu) 0).val + 2 ≤ Lu 0 + 1 := by
        have : ((y30 Lu hLu) 0).val = 30 := by simp [y30]
        have := hLu 0; omega
      have h0 := freeBond_coord_zero (y30 Lu hLu) hfit (le_refl 2)
      have hy0 : ((y30 Lu hLu) 0).val = 30 := by simp [y30]
      subst hbe
      left
      show 30 ≤ ((freeBond 2 (y30 Lu hLu)).1 0).val ∧ ((freeBond 2 (y30 Lu hLu)).1 0).val < 34
      omega
    · exact hoff b hbe
  refine ⟨⟨?_, ?_⟩, hOn, ?_⟩
  · intro y hy x hx b hb
    refine hoff b ?_
    rintro rfl
    exact freeBond_not_mem_staircase (by norm_num) hdvd (y30 Lu hLu) (y30_coarse hLu) y hy.1 x hx hb
  · intro b hb
    refine hoff b ?_
    rintro rfl
    obtain ⟨c, hc1, hc2⟩ := hb
    exact freeBond_not_dropped (by norm_num) hdvd (y30 Lu hLu) (y30_coarse hLu) ⟨c, hc2⟩
  · have hpos : 0 < ‖Bseed30 Lu hLu (freeBond 2 (y30 Lu hLu))‖ ^ 2 := by
      have : Bseed30 Lu hLu (freeBond 2 (y30 Lu hLu)) = suTwoWitness := Pi.single_eq_same _ _
      rw [this]
      have : suTwoWitness ≠ 0 := suTwoWitness_ne_zero
      positivity
    have hle : ‖Bseed30 Lu hLu (freeBond 2 (y30 Lu hLu))‖ ^ 2
        ≤ ∑ b : Bond Lu, ‖Bseed30 Lu hLu b‖ ^ 2 :=
      Finset.single_le_sum (f := fun b : Bond Lu => ‖Bseed30 Lu hLu b‖ ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ _)
    unfold bondEnergy
    linarith

theorem torusOK_60_M2 {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) : TorusOK 2 2 Lu := by
  refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩ <;> rw [hLu μ] <;> norm_num

/-- **[r5 form: site coverage `CoversOm0c`; the r6 form with `CoversOm0p` is `ZT5D2.proper_tower_hyps_p`]** **PROPER-TOWER NON-VACUITY OF THE HYPOTHESES (k = 1, `ell = 2`, `M = 2 = ell^1`, `R = 6`, cube factor 12).**
`Ω₀ ≠ torus`, both strata nonempty, `Λ' ≠ ∅`, `Λ = B(Λ')`, a NON-FLAT `U` in the class, a nonzero `B̃ ∈ Λ̃` in the touching class. -/
theorem proper_tower_hyps {Lu Lf : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60)
    (hLf : ∀ μ, Lf μ + 1 = 120) {α₀ : ℝ} (hα : 0 < α₀) (hα1 : α₀ ≤ 1 / 2) :
    TorusOK 2 2 Lu ∧ Admissible 2 2 6 1 (TT Lf) ∧ CoversOm0c 2 2 12 1 (TT Lf) ∧
    (∃ p : PeriodicLatticeSite Lf, p ∈ towerBj (TT Lf) 0) ∧
    (∃ p : PeriodicLatticeSite Lf, p ∈ towerBj (TT Lf) 1) ∧
    (∃ p : PeriodicLatticeSite Lf, p ∉ (TT Lf).Om 0) ∧
    LambdaOK2 (Lu := Lu) (Lf := Lf) 2 2 6 1 (TT Lf) (LamT Lu) ∧
    (LamPrime 2 (LamT Lu)).Nonempty ∧
    (∃ U : LinkCfg Lf, PerCubeRegular2 2 2 12 1 (TT Lf) α₀ (((2 : ℕ) : ℝ) ^ 1)⁻¹ U ∧
       ¬ ∃ g : PeriodicLatticeSite Lf → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
    (∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn (LamT Lu) 2 Bt ∧ OnLambdaT (LamT Lu) Bt ∧
       0 < bondEnergy Bt) := by
  have hmk : ∀ (v : ℕ) (μ : Fin 3), v < 120 → v < Lf μ + 1 := fun v μ h => by have := hLf μ; omega
  refine ⟨torusOK_60_M2 hLu, TT2_admissible hLf, TT2_covers hLf, ?_, ?_, ?_,
    ⟨LamT_ok hLu hLf, LamT_blockSum⟩, LamT_lamPrime_nonempty hLu, ?_,
    ⟨Bseed30 Lu hLu, (Bseed30_props hLu).1, (Bseed30_props hLu).2.1, (Bseed30_props hLu).2.2⟩⟩
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
    · apply ufield_perCubeRegular2 (by norm_num) (by norm_num) (by norm_num) _ hα
      intro e
      unfold spike
      split_ifs
      · rw [abs_of_pos hpos]
      · simp; positivity
    · apply spike_not_pure_gauge (by have := hLf 0; omega)
      · rw [hηv]; norm_num; positivity
      · rw [hηv]; norm_num; linarith

/-- the fixed-factor class is restrictive on the proper tower -/
theorem proper_tower_class_excludes_some_U {Lf : PeriodicLatticeExtent} (hLf : ∀ μ, Lf μ + 1 = 120)
    {α₀ : ℝ} (hα : 0 < α₀) (hsmall : α₀ ≤ 1 / 48) :
    ∃ U : LinkCfg Lf, ¬ PerCubeRegular2 2 2 12 1 (TT Lf) α₀ (((2 : ℕ) : ℝ) ^ 1)⁻¹ U := by
  obtain ⟨p, hp⟩ : ∃ p : PeriodicLatticeSite Lf, p ∈ (TT Lf).Om 0 :=
    ⟨fun μ => ⟨10, by have := hLf μ; omega⟩, by simp [TT, OmA]⟩
  refine coveredc_class_excludes_some_U (fun μ => by have := hLf μ; omega) (by norm_num) (by norm_num)
    (by norm_num) _ (TT2_covers hLf) ⟨p, hp⟩ (by norm_num) hα ?_
  push_cast; nlinarith

#print axioms TT2_admissible
#print axioms box48_not_sub_box24
#print axioms TT2_covers
#print axioms LamT_ok
#print axioms LamT_blockSum
#print axioms Bseed30_props
#print axioms proper_tower_hyps
#print axioms proper_tower_class_excludes_some_U

end AdalyFormal.StatementLaneG
