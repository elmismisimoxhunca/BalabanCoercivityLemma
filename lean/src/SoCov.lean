import SoGeo
import CaT2d

/-!
# SoCov -- site coverage of the decoupled tower `neS ell M R` (lane sites_only_20261019)

For every `ell >= 2`, `M > 0`, `c <= R`, `c >= 10` and `SoRel ell c` (thin width `cfv - 1` top blocks, `ell (cfv - 1) = 2 (c - 1)`), EVERY site of `Omega_0` of `neS ell M R`
lies in a class cube of factor `c`: `CovSitesF ell M (constFam c _) 2 (neS ell M R)`.  The cases by the `x_0` coordinate:
* `P0 <= x_0 < P1`      : level-0 shell, window of width `c M` inside `[P0, A')`, index 0.
* `Q1 <= x_0 < Q0`      : level-0 shell, window inside `[B, Q0)`, index 0.
* `A' <= x_0 < A' + (c-1) Y_1` : thin component, left part: window `[A' - Y_1, A' + (c-1) Y_1)` of width `c Y_1`, index 1, sticks out at `A' - 1`.
* `A' + (c-1) Y_1 <= x_0 < B'` : thin component, right part: window `[B' - (c-1) Y_1, B' + Y_1)`, index 1, sticks out at `B'` (here `B' - A' = 2 (c-1) Y_1`).
* `A <= x_0 < B`        : fat component, window of width `c Y_2` inside `[A, B)`, index 2.
* `P1 <= x_0 < Q1` outside both components : window inside `[P1, Q1)`, index 1.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.SitesOnly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.NonVac (mem_box_N)
open MXQ.AllC
open NcwdhFam
open AdalyFormal.CoverOmega.Struct (box_coord)

section
variable [CfData]
local notation "cfv" => CfData.cf

/-- the layer `Ω_i \ Ω_{i+1}` (with `Ω₃ = ∅`) of `neS ell M R` as a condition on the `x₀` coordinate. -/
def Bc (ell M R i w : ℕ) : Prop :=
  (i = 0 ∧ neP0 ell M R ≤ w ∧ w < neQ0 ell M R ∧ ¬ (neP1 ell M R ≤ w ∧ w < neQ1 ell M R)) ∨
  (i = 1 ∧ (neP1 ell M R ≤ w ∧ w < neQ1 ell M R) ∧
    ¬ ((neA' ell M R ≤ w ∧ w < neB' ell M R) ∨ (neA ell M R ≤ w ∧ w < neB ell M R))) ∨
  (i = 2 ∧ ((neA' ell M R ≤ w ∧ w < neB' ell M R) ∨ (neA ell M R ≤ w ∧ w < neB ell M R)))

theorem mem_bj {ell M R : ℕ} (i : ℕ) (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) :
    y ∈ towerBj (neS ell M R) i ↔ Bc ell M R i (y 0).val := by
  unfold towerBj
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | rfl | h
  · simp only [Set.mem_sdiff, Nat.reduceAdd, neS_om0, neS_om1]
    unfold Bc
    constructor <;> intro h <;> omega
  · simp only [Set.mem_sdiff, Nat.reduceAdd, neS_om1, neS_om2]
    unfold Bc
    constructor <;> intro h <;> omega
  · simp only [Set.mem_sdiff, Nat.reduceAdd, neS_om2]
    unfold Bc
    constructor
    · rintro ⟨h1, -⟩; omega
    · intro h1
      exact ⟨by omega, tw3_omHi 3 le_rfl y⟩
  · constructor
    · rintro ⟨h1, -⟩; exact absurd h1 (tw3_omHi i h y)
    · intro h1; unfold Bc at h1; omega

/-- the atoms and their linear relations (everything the case analysis needs). -/
theorem so_vals {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) :
    neA' ell M R = ell * (ell * (R * M)) + ell * (ell * M) ∧
    neB' ell M R = ell * (ell * (R * M)) + ell * (ell * M) + 2 * ((c - 1) * (ell * M)) ∧
    neA ell M R = ell * (ell * (R * M)) + 2 * (ell * (ell * M)) + 2 * ((c - 1) * (ell * M)) ∧
    neB ell M R = 3 * (ell * (ell * (R * M))) + 5 * (ell * (ell * M)) + 2 * ((c - 1) * (ell * M)) ∧
    neP1 ell M R + ell * (R * M) = ell * (ell * (R * M)) + ell * (ell * M) ∧
    neP0 ell M R + R * M = neP1 ell M R ∧
    neQ1 ell M R = neB ell M R + ell * (R * M) ∧ neQ0 ell M R = neQ1 ell M R + R * M ∧
    neN ell M R = 4 * (ell * (ell * (R * M))) + 8 * (ell * (ell * M)) + 4 * ((c - 1) * (ell * M)) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  have hthin := so_thin_atoms (M := M) hrel (by omega : 1 ≤ c)
  have e1 : neA' ell M R = ell * (ell * (R * M)) + ell * (ell * M) := rfl
  refine ⟨e1, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · simp only [neB']; omega
  · simp only [neA]; omega
  · simp only [neB]; omega
  · simp only [neP1, neA']; omega
  · simp only [neP0, neP1, neA']; omega
  · simp only [neN]; omega

/-- the ordering `P0 < P1 < A' < B' < A < B < Q1 < Q0` and `Q0 < N`. -/
theorem so_order {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) :
    neP0 ell M R < neP1 ell M R ∧ neP1 ell M R < neA' ell M R ∧ neA' ell M R < neB' ell M R ∧ neB' ell M R < neA ell M R ∧
      neA ell M R < neB ell M R ∧ neB ell M R < neQ1 ell M R ∧ neQ1 ell M R < neQ0 ell M R ∧ neQ0 ell M R < neN ell M R := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := so_vals hell hM hR hrel hc
  have hY1 : 0 < ell * M := Nat.mul_pos (by omega) hM
  have hcm1 : 1 * (ell * M) ≤ (c - 1) * (ell * M) := Nat.mul_le_mul_right _ (by omega)
  have hRM : 1 ≤ R * M := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem bc_disj {ell M R c i i' w : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c)
    (h : Bc ell M R i w) (h' : Bc ell M R i' w) : i = i' := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := so_order hell hM hR hrel hc
  unfold Bc at h h'
  omega

theorem bc0 {ell M R w : ℕ} : Bc ell M R 0 w ↔ (neP0 ell M R ≤ w ∧ w < neQ0 ell M R ∧ ¬ (neP1 ell M R ≤ w ∧ w < neQ1 ell M R)) := by
  unfold Bc; constructor <;> intro h <;> omega

theorem bc1 {ell M R w : ℕ} : Bc ell M R 1 w ↔ ((neP1 ell M R ≤ w ∧ w < neQ1 ell M R) ∧
    ¬ ((neA' ell M R ≤ w ∧ w < neB' ell M R) ∨ (neA ell M R ≤ w ∧ w < neB ell M R))) := by
  unfold Bc; constructor <;> intro h <;> omega

theorem bc2 {ell M R w : ℕ} : Bc ell M R 2 w ↔ ((neA' ell M R ≤ w ∧ w < neB' ell M R) ∨ (neA ell M R ≤ w ∧ w < neB ell M R)) := by
  unfold Bc; constructor <;> intro h <;> omega

theorem bc3 {ell M R w : ℕ} : Bc ell M R 3 w ↔ False := by
  unfold Bc
  constructor
  · intro h; omega
  · intro h; exact h.elim

/-- an `x₀`-window with the right layer conditions is a class cube containing a given site. -/
theorem mkCube {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) {j : ℕ} (hj : j ≤ 2)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (s : ℕ)
    (hs : bigSide M ell j ∣ s) (hsx : s ≤ (x 0).val ∧ (x 0).val < s + c * bigSide M ell j)
    (hsN : s + c * bigSide M ell j ≤ neN ell M R)
    (hsub : ∀ w, s ≤ w → w < s + c * bigSide M ell j → Bc ell M R j w ∨ Bc ell M R (j + 1) w)
    (hmeet : ∃ w, s ≤ w ∧ w < s + c * bigSide M ell j ∧ Bc ell M R j w) :
    ∃ sites : Set (PeriodicLatticeSite (scaleUp ell 2 (neLu M R))),
      IsClassCube ell M c 2 (neS ell M R) sites j ∧ x ∈ sites := by
  have hell0 : 0 < ell := by omega
  have hN := ne_scaleUp (ell := ell) (R := R) hell0 hM
  have hu : 0 < bigSide M ell j := by simp only [bigSide]; exact Nat.mul_pos hM (pow_pos hell0 j)
  obtain ⟨side, hside⟩ : ∃ side, side = c * bigSide M ell j := ⟨_, rfl⟩
  rw [← hside] at hsx hsN hsub hmeet
  have hpos : 0 < side := by rw [hside]; exact Nat.mul_pos (by omega) hu
  have hlt : ∀ (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (μ : Fin 3), (y μ).val < neN ell M R :=
    fun y μ => by have := (y μ).isLt; have := hN μ; omega
  have hsd : bigSide M ell j ∣ side := by rw [hside]; exact Dvd.intro_left _ rfl
  let z : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)) := fun μ =>
    if h : μ = 0 then ⟨s, by have := hN μ; omega⟩
    else ⟨side * ((x μ).val / side), by have := Nat.mul_div_le (x μ).val side; have := hlt x μ; have := hN μ; omega⟩
  have hz0 : (z 0).val = s := by simp [z]
  have hzμ : ∀ μ : Fin 3, μ ≠ 0 → (z μ).val = side * ((x μ).val / side) := by
    intro μ hμ; simp [z, hμ]
  have hxμ : ∀ μ : Fin 3, μ ≠ 0 → (z μ).val ≤ (x μ).val ∧ (x μ).val < (z μ).val + side := by
    intro μ hμ
    rw [hzμ μ hμ]
    have h1 := Nat.mul_div_le (x μ).val side
    have h2 := Nat.lt_mul_div_succ (x μ).val hpos
    rw [Nat.mul_add, Nat.mul_one] at h2
    exact ⟨h1, h2⟩
  have hbox : ∀ y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)),
      s ≤ (y 0).val → (y 0).val < s + side → (y 1 = x 1) → (y 2 = x 2) → y ∈ siteBox z side := by
    intro y h0 h0' h1 h2
    rw [mem_box_N hN z y side]
    refine ⟨CovAssume.box_off (hlt y 0) (by rw [hz0]; exact h0) (by rw [hz0]; exact h0'), ?_, ?_⟩
    · rw [h1]
      have := hxμ 1 (by decide)
      exact CovAssume.box_off (hlt x 1) this.1 this.2
    · rw [h2]
      have := hxμ 2 (by decide)
      exact CovAssume.box_off (hlt x 2) this.1 this.2
  have hxbox : x ∈ siteBox z side := hbox x hsx.1 hsx.2 rfl rfl
  have hsub' : ∀ y ∈ siteBox z side, y ∈ towerBj (neS ell M R) j ∪ towerBj (neS ell M R) (j + 1) := by
    intro y hy
    have h0 := ((mem_box_N hN z y side).1 hy).1
    rw [hz0] at h0
    obtain ⟨hlo, hhi⟩ := box_coord (hlt y 0) (by omega) h0
    rcases hsub (y 0).val hlo hhi with h | h
    · exact Or.inl ((mem_bj j y).2 h)
    · exact Or.inr ((mem_bj (j + 1) y).2 h)
  obtain ⟨w, hw1, hw2, hwB⟩ := hmeet
  have hwN : w < neN ell M R := by omega
  let q : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)) := Function.update x 0 ⟨w, by have := hN 0; omega⟩
  have hq0 : (q 0).val = w := by simp [q]
  have hq1 : q 1 = x 1 := by simp [q]
  have hq2 : q 2 = x 2 := by simp [q]
  have hqbox : q ∈ siteBox z side := hbox q (by rw [hq0]; exact hw1) (by rw [hq0]; exact hw2) hq1 hq2
  have hqB : q ∈ towerBj (neS ell M R) j := (mem_bj j q).2 (by rw [hq0]; exact hwB)
  refine ⟨siteBox z side, ⟨⟨hj, ⟨z, ?_, by rw [hside]⟩, hsub', ⟨q, hqbox, hqB⟩⟩, ?_⟩, hxbox⟩
  · intro μ
    by_cases hμ : μ = 0
    · subst hμ; rw [hz0]; exact Nat.mod_eq_zero_of_dvd hs
    · rw [hzμ μ hμ]; exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right hsd _)
  · rintro i ⟨hi, -, hsub2, ⟨p, hp, hpB⟩⟩
    have a1 : i = j ∨ i = j + 1 := by
      rcases hsub' p hp with h | h
      · exact Or.inl (bc_disj hell hM hR hrel hc ((mem_bj i p).1 hpB) ((mem_bj j p).1 h))
      · exact Or.inr (bc_disj hell hM hR hrel hc ((mem_bj i p).1 hpB) ((mem_bj (j + 1) p).1 h))
    have a2 : j = i ∨ j = i + 1 := by
      rcases hsub2 hqbox with h | h
      · exact Or.inl (bc_disj hell hM hR hrel hc ((mem_bj j q).1 hqB) ((mem_bj i q).1 h))
      · exact Or.inr (bc_disj hell hM hR hrel hc ((mem_bj j q).1 hqB) ((mem_bj (i + 1) q).1 h))
    omega

#print axioms mkCube

end

end AdalyFormal.SitesOnly
