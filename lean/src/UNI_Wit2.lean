import UNI_Base

/-!
# UNI_Wit2 -- a union that is not a box, on an ADMISSIBLE tower (lane union_cubes_20261018)

Prosecutor's example (finding 5 of union_cubes_prosecution_20261018): `ell = M = 2`, `k = 1`, torus side 8 (`L = fun _ => 7`), `R ≥ 12`,
`Ω₀ = univ`, `Ω₁ = [0,4)³`, `Ω_j = ∅` for `j ≥ 2`.  `T8` is `Admissible 2 2 R 1` (all six clauses, `admissible_T8`).
`sitesW8 = [4,6)³ ∪ [6,8)³` (16 sites, two diagonal level-0 blocks of side 2) is an `IsClassUnion` of index 0 and is not an `IsClassCube` for any factor `f`.
-/
set_option autoImplicit false

namespace UNI.Wit2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open UNI.AllC

def L8 : PeriodicLatticeExtent := fun _ => 7

def T8 : Tower L8 := ⟨fun j => if j = 0 then Set.univ else if j = 1 then {x | ∀ μ, (x μ).val < 4} else ∅⟩

theorem pcd8 (a : ℕ) (ha : a < 8) : pcd 8 a 0 ≤ 4 := by
  unfold pcd
  split_ifs <;> omega

theorem admissible_T8 (R : ℕ) (hR : 12 ≤ R) : Admissible 2 2 R 1 T8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    simp only [T8] at hx ⊢
    by_cases h0 : j = 0
    · subst h0; simp at hx ⊢
    · by_cases h1 : j + 1 = 1
      · omega
      · simp [h1] at hx
        exact absurd hx.1 h0
  · intro j hj
    simp only [T8]
    have h0 : j ≠ 0 := by omega
    have h1 : j ≠ 1 := by omega
    simp [h0, h1]
  · intro j hj μ
    interval_cases j <;> simp [bigSide, L8]
  · intro j hj
    interval_cases j
    · intro x _ y _; simp [T8]
    · intro x hx y hxy
      simp only [T8, bigSide] at hx ⊢
      simp only [if_neg (by omega : (1:ℕ) ≠ 0), if_pos rfl, Set.mem_setOf_eq] at hx ⊢
      intro μ
      have h2 := hxy μ
      have h3 := hx μ
      simp only [bigSide] at h2
      norm_num at h2
      omega
  · intro j hj x hx y hy
    interval_cases j
    · simp [T8] at hx
    · simp [T8] at hy
  · intro x
    simp only [T8]
    constructor
    · intro _
      refine ⟨fun _ => ⟨0, by simp [L8]⟩, ?_, x, fun μ => rfl, ?_⟩
      · simp
      · unfold pdist
        have h1 := pcd8 (x 0).val (x 0).isLt
        have h2 := pcd8 (x 1).val (x 1).isLt
        have h3 := pcd8 (x 2).val (x 2).isLt
        simp [Fin.sum_univ_three, L8]
        omega
    · intro _; simp

theorem mem_B0 (x : PeriodicLatticeSite L8) : x ∈ towerBj T8 0 ↔ ¬ ∀ μ, (x μ).val < 4 := by
  show x ∈ T8.Om 0 ∧ x ∉ T8.Om (0 + 1) ↔ _
  simp [T8]

def sitesW8 : Set (PeriodicLatticeSite L8) := {x | (∀ μ, 4 ≤ (x μ).val ∧ (x μ).val < 6) ∨ (∀ μ, 6 ≤ (x μ).val)}

theorem unionAt_W8 : UnionAt 2 2 1 T8 sitesW8 0 := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro x hx y hxy
    simp only [bigSide, pow_zero, mul_one] at hxy
    rcases hx with hx | hx
    · left; intro μ; have := hxy μ; have := hx μ; omega
    · right; intro μ; have := hxy μ; have := hx μ; omega
  · intro x hx
    left
    rw [mem_B0]
    intro hall
    rcases hx with hx | hx
    · have := (hx 0).1; have := hall 0; omega
    · have := hx 0; have := hall 0; omega
  · refine ⟨fun _ => ⟨4, by simp [L8]⟩, Or.inl (fun μ => by simp), ?_⟩
    rw [mem_B0]
    intro hall
    have := hall 0
    simp at this

theorem isClassUnion_W8 (R : ℕ) (hR : 12 ≤ R) : IsClassUnion 2 2 1 T8 sitesW8 0 :=
  isClassUnion_of_unionAt (admissible_T8 R hR).1 unionAt_W8

theorem not_box_W8 (f : ℕ) : ¬ IsClassCube 2 2 f 1 T8 sitesW8 0 := by
  intro hc
  obtain ⟨⟨-, ⟨z, -, hz⟩, -, -⟩, -⟩ := hc
  let a : PeriodicLatticeSite L8 := fun _ => ⟨4, by simp [L8]⟩
  let b : PeriodicLatticeSite L8 := fun _ => ⟨6, by simp [L8]⟩
  let c : PeriodicLatticeSite L8 := fun μ => if μ = 2 then ⟨6, by simp [L8]⟩ else ⟨4, by simp [L8]⟩
  have ha : a ∈ sitesW8 := Or.inl (fun μ => by simp [a])
  have hb : b ∈ sitesW8 := Or.inr (fun μ => by simp [b])
  rw [hz] at ha hb
  have hc : c ∈ siteBox z (f * bigSide 2 2 0) := by
    intro μ
    by_cases h : μ = 2
    · have := hb μ; simpa [c, h, b] using this
    · have := ha μ; simpa [c, h, a] using this
  rw [← hz] at hc
  rcases hc with hc | hc
  · have := hc 2; simp [c] at this
  · have := hc 0; simp [c] at this

end UNI.Wit2

#print axioms UNI.Wit2.admissible_T8
#print axioms UNI.Wit2.isClassUnion_W8
#print axioms UNI.Wit2.not_box_W8
