import NuA3

/-!
# CaT2a -- site coverage at `ell = 2` on the witness tower `neS 2 M R` (lane cov_assume_20261019), part A: the covering construction

Source tower: `neS 2 M R = tw3 _ P0 Q0 P1 Q1 A' B' A B` (NsCvNe2), `Ω₀ = [P0,Q0)`, `Ω₁ = [P1,Q1)`, `Ω₂ = [A',B') ∪ [A,B)` in the `x₀` coordinate, transverse coordinates free.
In units of `M` (with `r = R M`, `cm = cf M`): `P0 = r+4M`, `P1 = 2r+4M`, `A' = 4r+4M`, `B' = 4r+4cm`, `A = 4r+4cm+4M`, `B = 12r+4cm+16M`, `Q1 = 14r+4cm+16M`, `Q0 = 15r+4cm+16M`, `N = 16r+8cm+24M`.
* `ne2_vals`   : these values (proved from the definitions).
* `Bc`, `mem_bj`, `bc_disj` : the layers `Ω_i \ Ω_{i+1}` as conditions on `x₀`, and their disjointness.
* `tile`       : one aligned window of width `side` inside `[lo,hi)` containing `x`.
* `mkCube`     : a window in `x₀` with the right layer conditions gives an `IsClassCube` containing `x` (transverse corners chosen by tiling).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace CovAssume

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.NonVac (mem_box_N)
open MXQ.AllC
open NcwdhFam

theorem tile {u side lo hi x : ℕ} (hu : u ∣ lo) (hh : u ∣ hi) (hs : u ∣ side) (hpos : 0 < side)
    (hlen : side ≤ hi - lo) (hlo : lo ≤ x) (hx : x < hi) :
    ∃ s, u ∣ s ∧ lo ≤ s ∧ s + side ≤ hi ∧ s ≤ x ∧ x < s + side := by
  by_cases h : x + side ≤ hi
  · have h1 := Nat.mul_div_le (x - lo) side
    have h2 := Nat.lt_mul_div_succ (x - lo) hpos
    rw [Nat.mul_add, Nat.mul_one] at h2
    refine ⟨lo + side * ((x - lo) / side), Nat.dvd_add hu (Dvd.dvd.mul_right hs _), ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
  · refine ⟨hi - side, Nat.dvd_sub hh hs, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega

theorem box_off {N a z side : ℕ} (haN : a < N) (h1 : z ≤ a) (h2 : a < z + side) : (a + N - z) % N < side := by
  have : a + N - z = (a - z) + N := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega

section
variable [CfData]

theorem ne2_vals {M R : ℕ} :
    neP0 2 M R = R * M + 4 * M ∧ neP1 2 M R = 2 * (R * M) + 4 * M ∧ neA' 2 M R = 4 * (R * M) + 4 * M ∧
    neB' 2 M R = 4 * (R * M) + 4 * (CfData.cf * M) ∧ neA 2 M R = 4 * (R * M) + 4 * (CfData.cf * M) + 4 * M ∧
    neB 2 M R = 12 * (R * M) + 4 * (CfData.cf * M) + 16 * M ∧ neQ1 2 M R = 14 * (R * M) + 4 * (CfData.cf * M) + 16 * M ∧
    neQ0 2 M R = 15 * (R * M) + 4 * (CfData.cf * M) + 16 * M ∧ neN 2 M R = 16 * (R * M) + 8 * (CfData.cf * M) + 24 * M := by
  have e1 : CfData.cf * (2 * (2 * M)) = 4 * (CfData.cf * M) := by ring
  simp only [neP0, neP1, neQ0, neQ1, neA', neB', neA, neB, neN, e1]
  omega

/-- the layer `Ω_i \ Ω_{i+1}` (with `Ω₃ = ∅`) of `neS 2 M R` as a condition on the `x₀` coordinate. -/
def Bc (M R i w : ℕ) : Prop :=
  (i = 0 ∧ neP0 2 M R ≤ w ∧ w < neQ0 2 M R ∧ ¬ (neP1 2 M R ≤ w ∧ w < neQ1 2 M R)) ∨
  (i = 1 ∧ (neP1 2 M R ≤ w ∧ w < neQ1 2 M R) ∧
    ¬ ((neA' 2 M R ≤ w ∧ w < neB' 2 M R) ∨ (neA 2 M R ≤ w ∧ w < neB 2 M R))) ∨
  (i = 2 ∧ ((neA' 2 M R ≤ w ∧ w < neB' 2 M R) ∨ (neA 2 M R ≤ w ∧ w < neB 2 M R)))

theorem mem_bj {M R : ℕ} (i : ℕ) (y : PeriodicLatticeSite (scaleUp 2 2 (neLu M R))) :
    y ∈ towerBj (neS 2 M R) i ↔ Bc M R i (y 0).val := by
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

theorem bc_disj {M R i i' w : ℕ} (hM : 0 < M) (hR : CfData.cf ≤ R) (h : Bc M R i w) (h' : Bc M R i' w) : i = i' := by
  obtain ⟨eP0, eP1, eA', eB', eA, eB, eQ1, eQ0, eN⟩ := ne2_vals (M := M) (R := R)
  have hcf := CfData.hcf
  have hcR : CfData.cf * M ≤ R * M := Nat.mul_le_mul_right M hR
  have hc10 : 10 * M ≤ CfData.cf * M := Nat.mul_le_mul_right M hcf
  unfold Bc at h h'
  omega

theorem bc0 {M R w : ℕ} : Bc M R 0 w ↔ (neP0 2 M R ≤ w ∧ w < neQ0 2 M R ∧ ¬ (neP1 2 M R ≤ w ∧ w < neQ1 2 M R)) := by
  unfold Bc; constructor <;> intro h <;> omega

theorem bc1 {M R w : ℕ} : Bc M R 1 w ↔ ((neP1 2 M R ≤ w ∧ w < neQ1 2 M R) ∧
    ¬ ((neA' 2 M R ≤ w ∧ w < neB' 2 M R) ∨ (neA 2 M R ≤ w ∧ w < neB 2 M R))) := by
  unfold Bc; constructor <;> intro h <;> omega

theorem bc2 {M R w : ℕ} : Bc M R 2 w ↔ ((neA' 2 M R ≤ w ∧ w < neB' 2 M R) ∨ (neA 2 M R ≤ w ∧ w < neB 2 M R)) := by
  unfold Bc; constructor <;> intro h <;> omega

theorem bc3 {M R w : ℕ} : Bc M R 3 w ↔ False := by
  unfold Bc
  constructor
  · intro h; omega
  · intro h; exact h.elim

end

end CovAssume
