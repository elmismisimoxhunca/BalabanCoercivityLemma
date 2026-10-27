import R8UR3
import ZT5A
import ZT5C
import ZT6B

/-!
# UR4 -- a family of proper slab towers satisfying EVERY hypothesis of the frozen inner claim, for all large `M` and `R`.

Parameters: `M ≥ 2` even, `h ≥ 6`; `R = 2h`; write `H = h·M` (so `R·M = 2H`).  Fine torus: `N = 12H + 16M` sites per direction
(`= 2·Nu`, unit torus `Nu = 6H + 8M`).  Tower (`k = 1`, slab in direction 0):
`Ω₀ = {4M ≤ x₀ < 12H + 12M}`, `Ω₁ = {2H + 4M ≤ x₀ < 10H + 12M}`, `Ω₂ = ∅`;  `Λ = {3H + 3M ≤ y₀ < 3H + 5M}` (unit lattice).
Proved here: `TorusOK 2 M Lu` (`slab_torusOK`), `Admissible 2 M R 1 S` (`slab_admissible`), `CoversOm0p 2 M 12 1 S`
(`slab_coversp`), `LambdaOK2 2 M R 1 S Λ` (`slab_lambdaOK2`), a nonzero `B̃ ∈ Λ̃` (`slab_seed`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.URLocalityR8

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice staircasePath)
open AdalyFormal.Balaban.FullReparamC (freeBond freeBond_not_mem_staircase freeBond_not_dropped freeBond_coord_zero)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-! ## 0. arithmetic helpers -/

theorem off_eq (N y z : ℕ) (hy : y < N) (hz : z ≤ y) : (y + N - z) % N = y - z := by
  rw [show y + N - z = (y - z) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem off_lt_iff (N y z s : ℕ) (hy : y < N) (hzs : z + s ≤ N) :
    (y + N - z) % N < s ↔ z ≤ y ∧ y < z + s := by
  by_cases hz : z ≤ y
  · rw [off_eq N y z hy hz]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- transverse membership: anchor `x − x % B`, side `s > B`, the point `x` or `x+1 (mod N)` -/
theorem trans_mem (N B s x w : ℕ) (hx : x < N) (hB : 0 < B) (hBs : B < s) (hsN : s ≤ N)
    (hw : w = x ∨ w = (x + 1) % N) : (w + N - (x - x % B)) % N < s := by
  have hr : x % B < B := Nat.mod_lt _ hB
  have hle : x % B ≤ x := Nat.mod_le _ _
  rcases hw with rfl | rfl
  · rw [off_eq N w _ hx (by omega)]; omega
  · by_cases h1 : x + 1 < N
    · rw [Nat.mod_eq_of_lt h1, off_eq N _ _ h1 (by omega)]; omega
    · have hN : x + 1 = N := by omega
      rw [hN, Nat.mod_self, zero_add]
      by_cases hz : x - x % B = 0
      · rw [hz, Nat.sub_zero, Nat.mod_self]; omega
      · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem mem_siteBox {L : PeriodicLatticeExtent} (z y : PeriodicLatticeSite L) (s : ℕ) :
    y ∈ siteBox z s ↔ ∀ μ : Fin 3, ((y μ).val + (L μ + 1) - (z μ).val) % (L μ + 1) < s := Iff.rfl

/-- `c·M ≤ y ↔ c ≤ y / M` packaged for block-closedness -/
theorem mulle_iff_div (M c y : ℕ) (hM : 0 < M) : c * M ≤ y ↔ c ≤ y / M := (Nat.le_div_iff_mul_le hM).symm

theorem lt_mul_iff_div (M c y : ℕ) (hM : 0 < M) : y < c * M ↔ y / M < c := (Nat.div_lt_iff_lt_mul hM).symm

/-! ## 1. the slab tower -/

section slab
variable {L : PeriodicLatticeExtent}

def slabOm (L : PeriodicLatticeExtent) (lo hi : ℕ) : Set (PeriodicLatticeSite L) := {x | lo ≤ (x 0).val ∧ (x 0).val < hi}

/-- the tower: `Ω₀ = [4M, 12H+12M)`, `Ω₁ = [2H+4M, 10H+12M)` in direction 0 -/
def SlabT (L : PeriodicLatticeExtent) (M H : ℕ) : Tower L :=
  ⟨fun j => if j = 0 then slabOm L (4 * M) (12 * H + 12 * M)
    else if j = 1 then slabOm L (2 * H + 4 * M) (10 * H + 12 * M) else ∅⟩

theorem slab_om0 (M H : ℕ) : (SlabT L M H).Om 0 = slabOm L (4 * M) (12 * H + 12 * M) := rfl
theorem slab_om1 (M H : ℕ) : (SlabT L M H).Om 1 = slabOm L (2 * H + 4 * M) (10 * H + 12 * M) := rfl
theorem slab_omj (M H j : ℕ) (hj : 2 ≤ j) : (SlabT L M H).Om j = ∅ := by
  show (if j = 0 then _ else if j = 1 then _ else ∅) = ∅
  rw [if_neg (by omega), if_neg (by omega)]

theorem towerBj0 (M H : ℕ) (x : PeriodicLatticeSite L) :
    x ∈ towerBj (SlabT L M H) 0 ↔ (4 * M ≤ (x 0).val ∧ (x 0).val < 12 * H + 12 * M) ∧
      ¬ (2 * H + 4 * M ≤ (x 0).val ∧ (x 0).val < 10 * H + 12 * M) := by
  show x ∈ (SlabT L M H).Om 0 \ (SlabT L M H).Om 1 ↔ _
  simp only [slab_om0, slab_om1, Set.mem_diff, slabOm, Set.mem_setOf_eq]

theorem towerBj1 (M H : ℕ) (x : PeriodicLatticeSite L) :
    x ∈ towerBj (SlabT L M H) 1 ↔ (2 * H + 4 * M ≤ (x 0).val ∧ (x 0).val < 10 * H + 12 * M) := by
  simp only [towerBj, slab_om1, slab_omj M H (1 + 1) le_rfl, Set.mem_diff, slabOm, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, not_false_eq_true, and_true]

theorem towerBj2 (M H : ℕ) (x : PeriodicLatticeSite L) : x ∉ towerBj (SlabT L M H) 2 := by
  simp only [towerBj, slab_omj M H 2 le_rfl, Set.mem_diff, Set.mem_empty_iff_false, false_and, not_false_eq_true]

/-! ### standing hypotheses -/

/-- the parameter facts used everywhere (`H = h·M`, `M` even, `h ≥ 6`, torus `N = 12H + 16M`) -/
structure SlabP (M h N : ℕ) : Prop where
  hM : 2 ≤ M
  hMe : 2 ∣ M
  hh : 6 ≤ h
  hN : N = 12 * (h * M) + 16 * M

theorem SlabP.H_ge {M h N : ℕ} (P : SlabP M h N) : 6 * M ≤ h * M := Nat.mul_le_mul_right _ P.hh

theorem SlabP.Mpos {M h N : ℕ} (P : SlabP M h N) : 0 < M := by have := P.hM; omega

/-- `x₀ / M`-blocks respect the boundaries `c·M` -/
theorem blk_le {M c x y : ℕ} (hM : 0 < M) (hxy : x / M = y / M) : c * M ≤ x ↔ c * M ≤ y := by
  rw [mulle_iff_div M c x hM, mulle_iff_div M c y hM, hxy]

theorem blk_lt {M c x y : ℕ} (hM : 0 < M) (hxy : x / M = y / M) : x < c * M ↔ y < c * M := by
  rw [lt_mul_iff_div M c x hM, lt_mul_iff_div M c y hM, hxy]

/-- `pcd` lower bound from one-sided distances on the circle -/
theorem pcd_gt (N a b d : ℕ) (ha : a < N) (hb : b < N) (h1 : d < (if a ≤ b then b - a else a - b))
    (h2 : d < N - (if a ≤ b then b - a else a - b)) : d < pcd N a b := by
  unfold pcd; omega

end slab

/-! ## 2. Admissible -/

section adm
variable {L : PeriodicLatticeExtent}

theorem pdist_ge_coord0 (x y : PeriodicLatticeSite L) : pcd (L 0 + 1) (x 0).val (y 0).val ≤ pdist x y :=
  Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)

/-- the collar inequality in coordinate 0 -/
theorem slab_collar {M h N : ℕ} (P : SlabP M h N) (a b : ℕ) (ha : a < N) (hb : b < N)
    (hout : ¬ (4 * M ≤ a ∧ a < 12 * (h * M) + 12 * M)) (hin : 2 * (h * M) + 4 * M ≤ b ∧ b < 10 * (h * M) + 12 * M) :
    2 * (h * M) < pcd N a b := by
  have := P.hN; have := P.H_ge
  unfold pcd; split_ifs <;> omega

theorem slab_admissible {M h N : ℕ} (P : SlabP M h N) (hL : ∀ μ, L μ + 1 = N) :
    Admissible 2 M (2 * h) 1 (SlabT L M (h * M)) := by
  have hM0 := P.Mpos
  have hR : 2 * h * bigSide M 2 0 = 2 * (h * M) := by unfold bigSide; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    rcases Nat.lt_or_ge j 1 with hj | hj
    · have : j = 0 := by omega
      subst this
      change x ∈ (SlabT L M (h * M)).Om 1 at hx
      rw [slab_om1] at hx; rw [slab_om0]
      simp only [slabOm, Set.mem_setOf_eq] at hx ⊢
      omega
    · rw [slab_omj M (h * M) (j + 1) (by omega)] at hx; exact hx.elim
  · intro j hj; exact slab_omj M (h * M) j (by omega)
  · intro j hj μ
    rw [hL μ, P.hN]
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · exact ⟨12 * h + 16, by unfold bigSide; ring⟩
    · exact ⟨6 * h + 8, by unfold bigSide; ring⟩
  · intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · intro x hx y hy
      have h0 := hy 0
      simp only [bigSide, pow_zero, mul_one] at h0
      rw [slab_om0] at hx ⊢
      simp only [slabOm, Set.mem_setOf_eq] at hx ⊢
      have e1 : 4 * M = 4 * M := rfl
      have e2 : 12 * (h * M) + 12 * M = (12 * h + 12) * M := by ring
      rw [e2] at hx ⊢
      exact ⟨(blk_le hM0 h0.symm).mp hx.1, (blk_lt hM0 h0.symm).mp hx.2⟩
    · intro x hx y hy
      have h0 := hy 0
      simp only [bigSide, pow_one] at h0
      rw [slab_om1] at hx ⊢
      simp only [slabOm, Set.mem_setOf_eq] at hx ⊢
      have e1 : 2 * (h * M) + 4 * M = (h + 2) * (M * 2) := by ring
      have e2 : 10 * (h * M) + 12 * M = (5 * h + 6) * (M * 2) := by ring
      rw [e1, e2] at hx ⊢
      have hM2 : 0 < M * 2 := by omega
      exact ⟨(blk_le hM2 h0.symm).mp hx.1, (blk_lt hM2 h0.symm).mp hx.2⟩
  · intro j hj x hx y hy
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · change y ∈ (SlabT L M (h * M)).Om 1 at hy
      rw [slab_om0] at hx; rw [slab_om1] at hy
      simp only [slabOm, Set.mem_setOf_eq] at hx hy
      rw [hR]
      have hxl : (x 0).val < N := by have := (x 0).isLt; have := hL 0; omega
      have hyl : (y 0).val < N := by have := (y 0).isLt; have := hL 0; omega
      have := slab_collar P _ _ hxl hyl hx hy
      have h2 := pdist_ge_coord0 x y
      rw [← hL 0] at this
      omega
    · rw [slab_omj M (h * M) (1 + 1) le_rfl] at hy; exact hy.elim
  · intro x
    rw [slab_om0]
    simp only [slabOm, Set.mem_setOf_eq]
    have hR' : 2 * h * M = 2 * (h * M) := by ring
    rw [hR']
    have hH := P.H_ge
    have hNv := P.hN
    constructor
    · intro hx
      have hxl : (x 0).val < N := by have := (x 0).isLt; have := hL 0; omega
      let v : ℕ := if (x 0).val < 2 * (h * M) + 4 * M then 2 * (h * M) + 4 * M
        else if (x 0).val < 10 * (h * M) + 12 * M then (x 0).val else 10 * (h * M) + 12 * M - 1
      have hv : v < L 0 + 1 := by rw [hL 0]; simp only [v]; split_ifs <;> omega
      refine ⟨Function.update x 0 ⟨v, hv⟩, ?_, x, fun μ => rfl, ?_⟩
      · rw [slab_om1]; simp only [slabOm, Set.mem_setOf_eq, Function.update_self]; simp only [v]; split_ifs <;> omega
      · unfold pdist
        rw [Finset.sum_eq_single (0 : Fin 3)]
        · simp only [Function.update_self]
          have hL0 := hL 0
          unfold pcd; simp only [v]; split_ifs <;> omega
        · intro μ _ hμ
          rw [Function.update_of_ne hμ, pcd_self]
        · intro h; exact absurd (Finset.mem_univ _) h
    · rintro ⟨y, hy, z, hz, hd⟩
      rw [slab_om1] at hy
      simp only [slabOm, Set.mem_setOf_eq] at hy
      have hzl : (z 0).val < N := by have := (z 0).isLt; have := hL 0; omega
      have hyl : (y 0).val < N := by have := (y 0).isLt; have := hL 0; omega
      have hc := pdist_ge_coord0 z y
      have hz0 : 4 * M ≤ (z 0).val ∧ (z 0).val < 12 * (h * M) + 12 * M := by
        by_contra hout
        have := slab_collar P _ _ hzl hyl hout hy
        rw [← hL 0] at this
        omega
      have hzx : (z 0).val / M = (x 0).val / M := hz 0
      have e2 : 12 * (h * M) + 12 * M = (12 * h + 12) * M := by ring
      rw [e2] at hz0 ⊢
      exact ⟨(blk_le hM0 hzx).mp hz0.1, (blk_lt hM0 hzx).mp hz0.2⟩

end adm

/-! ## 3. class cubes and coverage -/

section cover
variable {L : PeriodicLatticeExtent}

theorem fshift_val (hL2 : ∀ μ, 2 ≤ L μ + 1) (s : PeriodicLatticeSite L) (μ ρ : Fin 3) :
    ((periodicLatticeShift s μ) ρ).val = if ρ = μ then ((s ρ).val + 1) % (L ρ + 1) else (s ρ).val := by
  unfold periodicLatticeShift
  by_cases h : ρ = μ
  · subst h
    simp only [Function.update_self, if_true]
    rw [Fin.val_add, Fin.val_one']
    have h2 : 1 % (L ρ + 1) = 1 := Nat.mod_eq_of_lt (by have := hL2 ρ; omega)
    rw [h2]
  · simp [Function.update_of_ne h, h]

def AdjG (x w : PeriodicLatticeSite L) : Prop :=
  ∀ ρ : Fin 3, (w ρ).val = (x ρ).val ∨ (w ρ).val = ((x ρ).val + 1) % (L ρ + 1)

theorem adjG_refl (x : PeriodicLatticeSite L) : AdjG x x := fun _ => Or.inl rfl

theorem adjG_shift (hL2 : ∀ μ, 2 ≤ L μ + 1) {x s : PeriodicLatticeSite L}
    (h : AdjG x s) (μ : Fin 3) (hμ : (s μ).val = (x μ).val) : AdjG x (periodicLatticeShift s μ) := by
  intro ρ
  rw [fshift_val hL2]
  by_cases hρ : ρ = μ
  · subst hρ; simp only [if_true]; right; rw [hμ]
  · simp only [if_neg hρ]; exact h ρ

theorem shift_coord_ne (hL2 : ∀ μ, 2 ≤ L μ + 1) (s : PeriodicLatticeSite L) {μ ν : Fin 3} (hne : ν ≠ μ) :
    ((periodicLatticeShift s μ) ν).val = (s ν).val := by
  rw [fshift_val hL2, if_neg hne]

/-- index-0 class cube: grid corner (mod `M`), `x₀`-range inside `Ω₀`, containing a shell site -/
theorem slab_cube0 {M h N : ℕ} (P : SlabP M h N) (hL : ∀ μ, L μ + 1 = N) (z : PeriodicLatticeSite L)
    (hz : GridCorner (bigSide M 2 0) z) (hz0 : 4 * M ≤ (z 0).val ∧ (z 0).val + 12 * M ≤ 12 * (h * M) + 12 * M)
    (w : PeriodicLatticeSite L) (hw : w ∈ siteBox z (12 * bigSide M 2 0)) (hws : w ∈ towerBj (SlabT L M (h * M)) 0) :
    IsClassCube 2 M 12 1 (SlabT L M (h * M)) (siteBox z (12 * bigSide M 2 0)) 0 := by
  have hNv := P.hN; have hH := P.H_ge
  have hs : 12 * bigSide M 2 0 = 12 * M := by unfold bigSide; ring
  have hsub : ∀ y ∈ siteBox z (12 * bigSide M 2 0), 4 * M ≤ (y 0).val ∧ (y 0).val < 12 * (h * M) + 12 * M := by
    intro y hy
    have h0 := (mem_siteBox z y _).mp hy 0
    rw [hs] at h0
    rw [off_lt_iff (L 0 + 1) _ _ _ (y 0).isLt (by have := hL 0; omega)] at h0
    omega
  refine ⟨⟨by omega, ⟨z, hz, rfl⟩, ?_, ⟨w, hw, hws⟩⟩, ?_⟩
  · intro y hy
    have h8 := hsub y hy
    by_cases hy1 : 2 * (h * M) + 4 * M ≤ (y 0).val ∧ (y 0).val < 10 * (h * M) + 12 * M
    · right; exact (towerBj1 M (h * M) y).mpr hy1
    · left; exact (towerBj0 M (h * M) y).mpr ⟨h8, hy1⟩
  · intro i hi
    by_contra hne
    have hi1 : i = 1 := by have := hi.1; omega
    subst hi1
    obtain ⟨_, _, hsub1, _⟩ := hi
    rcases hsub1 hw with h1 | h1
    · exact ((towerBj0 M (h * M) w).mp hws).2 ((towerBj1 M (h * M) w).mp h1)
    · exact towerBj2 M (h * M) w h1

/-- index-1 class cube: grid corner (mod `2M`), `x₀`-range inside `Ω₁` -/
theorem slab_cube1 {M h N : ℕ} (P : SlabP M h N) (hL : ∀ μ, L μ + 1 = N) (z : PeriodicLatticeSite L)
    (hz : GridCorner (bigSide M 2 1) z)
    (hz0 : 2 * (h * M) + 4 * M ≤ (z 0).val ∧ (z 0).val + 24 * M ≤ 10 * (h * M) + 12 * M) :
    IsClassCube 2 M 12 1 (SlabT L M (h * M)) (siteBox z (12 * bigSide M 2 1)) 1 := by
  have hNv := P.hN; have hH := P.H_ge; have hM0 := P.Mpos
  have hs : 12 * bigSide M 2 1 = 24 * M := by unfold bigSide; ring
  have hsub : ∀ y ∈ siteBox z (12 * bigSide M 2 1), 2 * (h * M) + 4 * M ≤ (y 0).val ∧ (y 0).val < 10 * (h * M) + 12 * M := by
    intro y hy
    have h0 := (mem_siteBox z y _).mp hy 0
    rw [hs] at h0
    rw [off_lt_iff (L 0 + 1) _ _ _ (y 0).isLt (by have := hL 0; omega)] at h0
    omega
  have hzmem : z ∈ siteBox z (12 * bigSide M 2 1) := by
    refine (mem_siteBox z z _).mpr (fun μ => ?_)
    have hzl : (z μ).val < L μ + 1 := (z μ).isLt
    rw [off_eq _ _ _ hzl le_rfl, Nat.sub_self, hs]; omega
  refine ⟨⟨le_rfl, ⟨z, hz, rfl⟩, ?_, ⟨z, hzmem, (towerBj1 M (h * M) z).mpr (hsub z hzmem)⟩⟩, ?_⟩
  · intro y hy; left; exact (towerBj1 M (h * M) y).mpr (hsub y hy)
  · intro i hi
    by_contra hne
    have hi0 : i = 0 := by have := hi.1; omega
    subst hi0
    obtain ⟨_, _, _, ⟨w, hw, hw0⟩⟩ := hi
    exact ((towerBj0 M (h * M) w).mp hw0).2 (hsub w hw)

/-- a class cube containing every `Ω₀`-site adjacent to `x` -/
theorem slab_cube_nbhd {M h N : ℕ} (P : SlabP M h N) (hL : ∀ μ, L μ + 1 = N) (x : PeriodicLatticeSite L)
    (hx : 4 * M ≤ (x 0).val ∧ (x 0).val < 12 * (h * M) + 12 * M) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube 2 M 12 1 (SlabT L M (h * M)) sites j ∧
      ∀ w : PeriodicLatticeSite L, AdjG x w → 4 * M ≤ (w 0).val → (w 0).val < 12 * (h * M) + 12 * M → w ∈ sites := by
  have hNv := P.hN; have hH := P.H_ge; have hM0 := P.Mpos; have hM2 := P.hM
  have hxl : ∀ μ, (x μ).val < N := fun μ => by have := (x μ).isLt; have := hL μ; omega
  have hw0 : ∀ w : PeriodicLatticeSite L, AdjG x w → (w 0).val < 12 * (h * M) + 12 * M →
      (w 0).val = (x 0).val ∨ (w 0).val = (x 0).val + 1 := by
    intro w hw _
    rcases hw 0 with h1 | h1
    · left; exact h1
    · right; rw [h1, Nat.mod_eq_of_lt (by have := hxl 0; have := hL 0; omega)]
  have hmodM : ∀ v : ℕ, v % M < M := fun v => Nat.mod_lt _ hM0
  have hmod2M : ∀ v : ℕ, v % (2 * M) < 2 * M := fun v => Nat.mod_lt _ (by omega)
  -- the three cases
  by_cases hA : 2 * (h * M) + 4 * M ≤ (x 0).val ∧ (x 0).val + 1 < 10 * (h * M) + 12 * M
  · -- interior: index 1
    let r0 := (x 0).val % (2 * M)
    let c : Fin 3 → ℕ := fun μ => if μ = 0 then min (max ((x 0).val - r0) (2 * (h * M) + 4 * M)) (10 * (h * M) - 12 * M)
      else (x μ).val - (x μ).val % (2 * M)
    have hc : ∀ μ, c μ < L μ + 1 := fun μ => by
      have := hxl μ; have := hL μ; simp only [c]; split_ifs <;> omega
    let z : PeriodicLatticeSite L := fun μ => ⟨c μ, hc μ⟩
    have hz0 : (z 0).val = min (max ((x 0).val - r0) (2 * (h * M) + 4 * M)) (10 * (h * M) - 12 * M) := by simp [z, c]
    have hzt : ∀ μ, μ ≠ 0 → (z μ).val = (x μ).val - (x μ).val % (2 * M) := fun μ hμ => by simp [z, c, hμ]
    have hr0 : r0 < 2 * M := hmod2M _
    have hr0le : r0 ≤ (x 0).val := Nat.mod_le _ _
    have hgrid : GridCorner (bigSide M 2 1) z := by
      intro μ
      have hb : bigSide M 2 1 = 2 * M := by unfold bigSide; ring
      rw [hb]
      by_cases hμ : μ = 0
      · subst hμ; rw [hz0]
        have d1 : ((x 0).val - r0) % (2 * M) = 0 := Nat.sub_mod_eq_zero_of_mod_eq (by simp [r0])
        have d2 : (2 * (h * M) + 4 * M) % (2 * M) = 0 := Nat.mod_eq_zero_of_dvd ⟨h + 2, by ring⟩
        have d3 : (10 * (h * M) - 12 * M) % (2 * M) = 0 := Nat.mod_eq_zero_of_dvd ⟨5 * h - 6, by
          rw [mul_tsub, show 2 * M * (5 * h) = 10 * (h * M) by ring, show 2 * M * 6 = 12 * M by ring]⟩
        rcases min_choice (max ((x 0).val - r0) (2 * (h * M) + 4 * M)) (10 * (h * M) - 12 * M) with e | e <;> rw [e]
        · rcases max_choice ((x 0).val - r0) (2 * (h * M) + 4 * M) with e' | e' <;> rw [e'] <;> assumption
        · exact d3
      · rw [hzt μ hμ]; exact Nat.sub_mod_eq_zero_of_mod_eq (by simp)
    have hzr : 2 * (h * M) + 4 * M ≤ (z 0).val ∧ (z 0).val + 24 * M ≤ 10 * (h * M) + 12 * M := by
      rw [hz0]; constructor <;> omega
    refine ⟨_, 1, slab_cube1 P hL z hgrid hzr, ?_⟩
    intro w hw hlo hhi
    have hs : 12 * bigSide M 2 1 = 24 * M := by unfold bigSide; ring
    refine (mem_siteBox z w _).mpr (fun μ => ?_)
    rw [hs]
    by_cases hμ : μ = 0
    · subst hμ
      have hwl : (w 0).val < N := by have := (w 0).isLt; have := hL 0; omega
      rw [off_lt_iff (L 0 + 1) _ _ _ (Fin.isLt _) (by have := hL 0; omega), hz0]
      rcases hw0 w hw hhi with e | e <;> rw [e] <;> constructor <;> omega
    · rw [hzt μ hμ]
      have := hL μ; exact trans_mem (L μ + 1) (2 * M) (24 * M) _ _ (x μ).isLt (by omega) (by omega) (by omega) (hw μ)
  · by_cases hB : (x 0).val < 2 * (h * M) + 4 * M
    · -- left shell: index 0 at x₀ − x₀ % M
      let c : Fin 3 → ℕ := fun μ => (x μ).val - (x μ).val % M
      have hc : ∀ μ, c μ < L μ + 1 := fun μ => by have := hxl μ; have := hL μ; simp only [c]; omega
      let z : PeriodicLatticeSite L := fun μ => ⟨c μ, hc μ⟩
      have hzv : ∀ μ, (z μ).val = (x μ).val - (x μ).val % M := fun μ => rfl
      have hgrid : GridCorner (bigSide M 2 0) z := by
        intro μ; rw [hzv]; simp only [bigSide, pow_zero, mul_one]; exact Nat.sub_mod_eq_zero_of_mod_eq (by simp)
      have hq : 4 * M ≤ (x 0).val - (x 0).val % M := by
        have h1 : 4 ≤ (x 0).val / M := (Nat.le_div_iff_mul_le hM0).mpr (by omega)
        have h2 : (x 0).val - (x 0).val % M = M * ((x 0).val / M) := by
          have := Nat.div_add_mod (x 0).val M; omega
        rw [h2]
        calc 4 * M = M * 4 := by ring
          _ ≤ M * ((x 0).val / M) := Nat.mul_le_mul_left _ h1
      have hr := hmodM (x 0).val
      have hrle := Nat.mod_le (x 0).val M
      have hzr : 4 * M ≤ (z 0).val ∧ (z 0).val + 12 * M ≤ 12 * (h * M) + 12 * M := by
        rw [hzv]; constructor <;> omega
      have hs : 12 * bigSide M 2 0 = 12 * M := by unfold bigSide; ring
      have hxin : x ∈ siteBox z (12 * bigSide M 2 0) := by
        refine (mem_siteBox z x _).mpr (fun μ => ?_)
        rw [hs, hzv]
        have := hL μ; exact trans_mem (L μ + 1) M (12 * M) _ _ (x μ).isLt hM0 (by omega) (by omega) (Or.inl rfl)
      refine ⟨_, 0, slab_cube0 P hL z hgrid hzr x hxin ((towerBj0 M (h * M) x).mpr ⟨hx, by omega⟩), ?_⟩
      intro w hw hlo hhi
      refine (mem_siteBox z w _).mpr (fun μ => ?_)
      rw [hs, hzv]
      by_cases hμ : μ = 0
      · subst hμ
        have hwl : (w 0).val < N := by have := (w 0).isLt; have := hL 0; omega
        rw [off_lt_iff (L 0 + 1) _ _ _ (Fin.isLt _) (by have := hL 0; omega)]
        rcases hw0 w hw hhi with e | e <;> rw [e] <;> constructor <;> omega
      · have := hL μ; exact trans_mem (L μ + 1) M (12 * M) _ _ (x μ).isLt hM0 (by omega) (by omega) (hw μ)
    · -- right part: index 0 at min (x₀ − x₀ % M) 12H
      have hr := hmodM (x 0).val
      have hrle := Nat.mod_le (x 0).val M
      let c : Fin 3 → ℕ := fun μ => if μ = 0 then min ((x 0).val - (x 0).val % M) (12 * (h * M))
        else (x μ).val - (x μ).val % M
      have hc : ∀ μ, c μ < L μ + 1 := fun μ => by
        have := hxl μ; have := hL μ; simp only [c]; split_ifs <;> omega
      let z : PeriodicLatticeSite L := fun μ => ⟨c μ, hc μ⟩
      have hz0 : (z 0).val = min ((x 0).val - (x 0).val % M) (12 * (h * M)) := by simp [z, c]
      have hzt : ∀ μ, μ ≠ 0 → (z μ).val = (x μ).val - (x μ).val % M := fun μ hμ => by simp [z, c, hμ]
      have hgrid : GridCorner (bigSide M 2 0) z := by
        intro μ
        simp only [bigSide, pow_zero, mul_one]
        by_cases hμ : μ = 0
        · subst hμ; rw [hz0]
          rcases min_choice ((x 0).val - (x 0).val % M) (12 * (h * M)) with e | e <;> rw [e]
          · exact Nat.sub_mod_eq_zero_of_mod_eq (by simp)
          · exact Nat.mod_eq_zero_of_dvd ⟨12 * h, by ring⟩
        · rw [hzt μ hμ]; exact Nat.sub_mod_eq_zero_of_mod_eq (by simp)
      have hzr : 4 * M ≤ (z 0).val ∧ (z 0).val + 12 * M ≤ 12 * (h * M) + 12 * M := by
        rw [hz0]; constructor <;> omega
      have hs : 12 * bigSide M 2 0 = 12 * M := by unfold bigSide; ring
      -- shell witness: x with x₀ ↦ max x₀ (10H+12M)
      let v : ℕ := max (x 0).val (10 * (h * M) + 12 * M)
      have hv : v < L 0 + 1 := by rw [hL 0]; simp only [v]; omega
      let ws : PeriodicLatticeSite L := Function.update x 0 ⟨v, hv⟩
      have hws0 : (ws 0).val = v := by simp [ws]
      have hwst : ∀ μ, μ ≠ 0 → ws μ = x μ := fun μ hμ => by simp [ws, Function.update_of_ne hμ]
      have hwsin : ws ∈ siteBox z (12 * bigSide M 2 0) := by
        refine (mem_siteBox z ws _).mpr (fun μ => ?_)
        rw [hs]
        by_cases hμ : μ = 0
        · subst hμ
          have hwl : (ws 0).val < N := by rw [hws0]; simp only [v]; omega
          rw [off_lt_iff (L 0 + 1) _ _ _ (Fin.isLt _) (by have := hL 0; omega), hws0, hz0]
          simp only [v]; constructor <;> omega
        · rw [hwst μ hμ, hzt μ hμ]
          have := hL μ; exact trans_mem (L μ + 1) M (12 * M) _ _ (x μ).isLt hM0 (by omega) (by omega) (Or.inl rfl)
      have hwsS : ws ∈ towerBj (SlabT L M (h * M)) 0 := by
        rw [towerBj0, hws0]; simp only [v]; constructor <;> omega
      refine ⟨_, 0, slab_cube0 P hL z hgrid hzr ws hwsin hwsS, ?_⟩
      intro w hw hlo hhi
      refine (mem_siteBox z w _).mpr (fun μ => ?_)
      rw [hs]
      by_cases hμ : μ = 0
      · subst hμ
        have hwl : (w 0).val < N := by have := (w 0).isLt; have := hL 0; omega
        rw [off_lt_iff (L 0 + 1) _ _ _ (Fin.isLt _) (by have := hL 0; omega), hz0]
        rcases hw0 w hw hhi with e | e <;> rw [e] <;> constructor <;> omega
      · rw [hzt μ hμ]
        have := hL μ; exact trans_mem (L μ + 1) M (12 * M) _ _ (x μ).isLt hM0 (by omega) (by omega) (hw μ)

theorem slab_coversp {M h N : ℕ} (P : SlabP M h N) (hL : ∀ μ, L μ + 1 = N) :
    CoversOm0p 2 M 12 1 (SlabT L M (h * M)) := by
  have hL2 : ∀ μ, 2 ≤ L μ + 1 := fun μ => by rw [hL μ, P.hN]; have := P.hM; omega
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [slab_om0] at hx
    have hx' : 4 * M ≤ (x 0).val ∧ (x 0).val < 12 * (h * M) + 12 * M := hx
    obtain ⟨sites, j, hc, hall⟩ := slab_cube_nbhd P hL x hx'
    exact ⟨sites, j, hc, hall x (adjG_refl x) hx'.1 hx'.2⟩
  · intro p hp
    have hmu : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
    have hnu : p.2.1.2 ≠ p.2.1.1 := fun h => hmu h.symm
    have hmem : ∀ e : PeriodicLatticeEdge L, e ∈ periodicPlaquetteBoundaryEdges p ↔
        (e = (p.1, p.2.1.1) ∨ e = (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∨
          e = (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∨ e = (p.1, p.2.1.2)) := by
      intro e
      simp [periodicPlaquetteBoundaryEdges]
    have hx : 4 * M ≤ (p.1 0).val ∧ (p.1 0).val < 12 * (h * M) + 12 * M := by
      have := (hp (p.1, p.2.1.1) ((hmem _).mpr (Or.inl rfl))).1
      rw [slab_om0] at this; exact this
    obtain ⟨sites, j, hc, hall⟩ := slab_cube_nbhd P hL p.1 hx
    refine ⟨sites, j, hc, fun e he => ?_⟩
    have hcb := hp e he
    rw [slab_om0] at hcb
    simp only [slabOm, Set.mem_setOf_eq] at hcb
    have a0 : AdjG p.1 p.1 := adjG_refl _
    have aμ : AdjG p.1 (periodicLatticeShift p.1 p.2.1.1) := adjG_shift hL2 a0 _ rfl
    have aν : AdjG p.1 (periodicLatticeShift p.1 p.2.1.2) := adjG_shift hL2 a0 _ rfl
    have aμν : AdjG p.1 (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2) :=
      adjG_shift hL2 aμ _ (shift_coord_ne hL2 _ hnu)
    have aνμ : AdjG p.1 (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.2) p.2.1.1) :=
      adjG_shift hL2 aν _ (shift_coord_ne hL2 _ hmu)
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

end cover

#print axioms slab_admissible
#print axioms slab_cube_nbhd
#print axioms slab_coversp

end AdalyFormal.URLocalityR8
