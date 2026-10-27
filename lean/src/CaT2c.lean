import CaT2b

/-!
# CaT2c -- the six cases of site coverage at `ell = 2` on the witness tower (lane cov_assume_20261019)

For a site `x` of `Ω₀` of `neS 2 M R` (`M > 0`, `R ≥ cf`), by the `x₀` coordinate (units: `r = R M`, `cm = cf M`):
* `cov_L0left`  : `x₀ ∈ [P0, P1)`      -- level-0 shell: a window of width `cm` inside `[P0, A')`, index 0.
* `cov_L0right` : `x₀ ∈ [Q1, Q0)`      -- level-0 shell: a window of width `cm` inside `[B, Q0)`, index 0.
* `cov_thinL`   : `x₀ ∈ [A', C)`, `C = A' + 2cm - 2M`  -- thin component, left half: window `[A'-2M, C)` of width `2cm`, index 1, sticks out at `A'-1`.
* `cov_thinR`   : `x₀ ∈ [C, B')`       -- thin component, right half: window `[C, C+2cm)`, index 1, sticks out at `B'`.
* `cov_fat`     : `x₀ ∈ [A, B)`        -- fat component: a window of width `4cm` inside `[A, B)`, index 2.
* `cov_lev1`    : `x₀ ∈ [P1, Q1)` outside both components -- a window of width `2cm` inside `[P1, Q1)`, index 1.
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
open MXQ.AllC
open NcwdhFam

section
variable [CfData]

/-- the goal of every case: `x` lies in some class cube of factor `cf` (index `j`). -/
def CovEx (M R : ℕ) (x : PeriodicLatticeSite (scaleUp 2 2 (neLu M R))) : Prop :=
  ∃ (sites : Set (PeriodicLatticeSite (scaleUp 2 2 (neLu M R)))) (j : ℕ),
    IsClassCube 2 M CfData.cf 2 (neS 2 M R) sites j ∧ x ∈ sites

theorem cov_L0left {M R : ℕ} (hM : 0 < M) (hR : CfData.cf ≤ R) (x : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)))
    (h1 : neP0 2 M R ≤ (x 0).val) (h2 : (x 0).val < neP1 2 M R) : CovEx M R x := by
  obtain ⟨eP0, eP1, eA', eB', eA, eB, eQ1, eQ0, eN⟩ := ne2_vals (M := M) (R := R)
  have hcf := CfData.hcf
  have hcR : CfData.cf * M ≤ R * M := Nat.mul_le_mul_right M hR
  have hc10 : 10 * M ≤ CfData.cf * M := Nat.mul_le_mul_right M hcf
  have hb0 : bigSide M 2 0 = M := by simp [bigSide]
  have s0 : CfData.cf * bigSide M 2 0 = CfData.cf * M := by rw [hb0]
  have dP0 : M ∣ neP0 2 M R := ⟨R + 4, by rw [eP0]; ring⟩
  have dA' : M ∣ neA' 2 M R := ⟨4 * R + 4, by rw [eA']; ring⟩
  have dcM : M ∣ CfData.cf * M := ⟨CfData.cf, by ring⟩
  obtain ⟨s, hds, hlo, hhi, hsx1, hsx2⟩ :=
    tile (x := (x 0).val) dP0 dA' dcM (by omega) (by omega) (by omega) (by omega)
  obtain ⟨sites, hq⟩ := mkCube hM hR (j := 0) (by norm_num) x s (by rw [hb0]; exact hds)
    ⟨hsx1, by rw [s0]; exact hsx2⟩ (by rw [s0]; omega)
    (fun w hw1 hw2 => by rw [s0] at hw2; show Bc M R 0 w ∨ Bc M R 1 w; rw [bc0, bc1]; omega)
    ⟨(x 0).val, hsx1, by rw [s0]; exact hsx2, by rw [bc0]; omega⟩
  exact ⟨sites, 0, hq⟩

theorem cov_L0right {M R : ℕ} (hM : 0 < M) (hR : CfData.cf ≤ R) (x : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)))
    (h1 : neQ1 2 M R ≤ (x 0).val) (h2 : (x 0).val < neQ0 2 M R) : CovEx M R x := by
  obtain ⟨eP0, eP1, eA', eB', eA, eB, eQ1, eQ0, eN⟩ := ne2_vals (M := M) (R := R)
  have hcf := CfData.hcf
  have hcR : CfData.cf * M ≤ R * M := Nat.mul_le_mul_right M hR
  have hc10 : 10 * M ≤ CfData.cf * M := Nat.mul_le_mul_right M hcf
  have hb0 : bigSide M 2 0 = M := by simp [bigSide]
  have s0 : CfData.cf * bigSide M 2 0 = CfData.cf * M := by rw [hb0]
  have dB : M ∣ neB 2 M R := ⟨12 * R + 4 * CfData.cf + 16, by rw [eB]; ring⟩
  have dQ0 : M ∣ neQ0 2 M R := ⟨15 * R + 4 * CfData.cf + 16, by rw [eQ0]; ring⟩
  have dcM : M ∣ CfData.cf * M := ⟨CfData.cf, by ring⟩
  obtain ⟨s, hds, hlo, hhi, hsx1, hsx2⟩ :=
    tile (x := (x 0).val) dB dQ0 dcM (by omega) (by omega) (by omega) (by omega)
  obtain ⟨sites, hq⟩ := mkCube hM hR (j := 0) (by norm_num) x s (by rw [hb0]; exact hds)
    ⟨hsx1, by rw [s0]; exact hsx2⟩ (by rw [s0]; omega)
    (fun w hw1 hw2 => by rw [s0] at hw2; show Bc M R 0 w ∨ Bc M R 1 w; rw [bc0, bc1]; omega)
    ⟨(x 0).val, hsx1, by rw [s0]; exact hsx2, by rw [bc0]; omega⟩
  exact ⟨sites, 0, hq⟩

theorem cov_thinL {M R : ℕ} (hM : 0 < M) (hR : CfData.cf ≤ R) (x : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)))
    (h1 : neA' 2 M R ≤ (x 0).val) (h2 : (x 0).val < 4 * (R * M) + 2 * M + 2 * (CfData.cf * M)) : CovEx M R x := by
  obtain ⟨eP0, eP1, eA', eB', eA, eB, eQ1, eQ0, eN⟩ := ne2_vals (M := M) (R := R)
  have hcf := CfData.hcf
  have hcR : CfData.cf * M ≤ R * M := Nat.mul_le_mul_right M hR
  have hc10 : 10 * M ≤ CfData.cf * M := Nat.mul_le_mul_right M hcf
  have hRM : M ≤ R * M := Nat.le_mul_of_pos_left M (by omega)
  have hb1 : bigSide M 2 1 = 2 * M := by simp only [bigSide]; ring
  have s1 : CfData.cf * bigSide M 2 1 = 2 * (CfData.cf * M) := by rw [hb1]; ring
  obtain ⟨s, hs'⟩ : ∃ s, s = 2 * M * (2 * R + 1) := ⟨_, rfl⟩
  have hs'' : s = 4 * (R * M) + 2 * M := by rw [hs']; ring
  obtain ⟨sites, hq⟩ := mkCube hM hR (j := 1) (by norm_num) x s (by rw [hb1, hs']; exact Dvd.intro _ rfl)
    ⟨by omega, by rw [s1]; omega⟩ (by rw [s1]; omega)
    (fun w hw1 hw2 => by rw [s1] at hw2; show Bc M R 1 w ∨ Bc M R 2 w; rw [bc1, bc2]; omega)
    ⟨neA' 2 M R - 1, by omega, by rw [s1]; omega, by rw [bc1]; omega⟩
  exact ⟨sites, 1, hq⟩

theorem cov_thinR {M R : ℕ} (hM : 0 < M) (hR : CfData.cf ≤ R) (x : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)))
    (h1 : 4 * (R * M) + 2 * M + 2 * (CfData.cf * M) ≤ (x 0).val) (h2 : (x 0).val < neB' 2 M R) : CovEx M R x := by
  obtain ⟨eP0, eP1, eA', eB', eA, eB, eQ1, eQ0, eN⟩ := ne2_vals (M := M) (R := R)
  have hcf := CfData.hcf
  have hcR : CfData.cf * M ≤ R * M := Nat.mul_le_mul_right M hR
  have hc10 : 10 * M ≤ CfData.cf * M := Nat.mul_le_mul_right M hcf
  have hRM : M ≤ R * M := Nat.le_mul_of_pos_left M (by omega)
  have hb1 : bigSide M 2 1 = 2 * M := by simp only [bigSide]; ring
  have s1 : CfData.cf * bigSide M 2 1 = 2 * (CfData.cf * M) := by rw [hb1]; ring
  obtain ⟨s, hs'⟩ : ∃ s, s = 2 * M * (2 * R + 1 + CfData.cf) := ⟨_, rfl⟩
  have hs'' : s = 4 * (R * M) + 2 * M + 2 * (CfData.cf * M) := by rw [hs']; ring
  obtain ⟨sites, hq⟩ := mkCube hM hR (j := 1) (by norm_num) x s (by rw [hb1, hs']; exact Dvd.intro _ rfl)
    ⟨by omega, by rw [s1]; omega⟩ (by rw [s1]; omega)
    (fun w hw1 hw2 => by rw [s1] at hw2; show Bc M R 1 w ∨ Bc M R 2 w; rw [bc1, bc2]; omega)
    ⟨neB' 2 M R, by omega, by rw [s1]; omega, by rw [bc1]; omega⟩
  exact ⟨sites, 1, hq⟩

theorem cov_fat {M R : ℕ} (hM : 0 < M) (hR : CfData.cf ≤ R) (x : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)))
    (h1 : neA 2 M R ≤ (x 0).val) (h2 : (x 0).val < neB 2 M R) : CovEx M R x := by
  obtain ⟨eP0, eP1, eA', eB', eA, eB, eQ1, eQ0, eN⟩ := ne2_vals (M := M) (R := R)
  have hcf := CfData.hcf
  have hcR : CfData.cf * M ≤ R * M := Nat.mul_le_mul_right M hR
  have hc10 : 10 * M ≤ CfData.cf * M := Nat.mul_le_mul_right M hcf
  have hb2 : bigSide M 2 2 = 4 * M := by simp only [bigSide]; ring
  have s2 : CfData.cf * bigSide M 2 2 = 4 * (CfData.cf * M) := by rw [hb2]; ring
  have dA : 4 * M ∣ neA 2 M R := ⟨R + CfData.cf + 1, by rw [eA]; ring⟩
  have dB4 : 4 * M ∣ neB 2 M R := ⟨3 * R + CfData.cf + 4, by rw [eB]; ring⟩
  have dc4M : 4 * M ∣ 4 * (CfData.cf * M) := ⟨CfData.cf, by ring⟩
  obtain ⟨s, hds, hlo, hhi, hsx1, hsx2⟩ :=
    tile (x := (x 0).val) dA dB4 dc4M (by omega) (by omega) (by omega) (by omega)
  obtain ⟨sites, hq⟩ := mkCube hM hR (j := 2) (by norm_num) x s (by rw [hb2]; exact hds)
    ⟨hsx1, by rw [s2]; exact hsx2⟩ (by rw [s2]; omega)
    (fun w hw1 hw2 => by rw [s2] at hw2; show Bc M R 2 w ∨ Bc M R 3 w; rw [bc2, bc3]; omega)
    ⟨(x 0).val, hsx1, by rw [s2]; exact hsx2, by rw [bc2]; omega⟩
  exact ⟨sites, 2, hq⟩

theorem cov_lev1 {M R : ℕ} (hM : 0 < M) (hR : CfData.cf ≤ R) (x : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)))
    (h1 : neP1 2 M R ≤ (x 0).val) (h2 : (x 0).val < neQ1 2 M R)
    (h3 : ¬ (neA' 2 M R ≤ (x 0).val ∧ (x 0).val < neB' 2 M R)) (h4 : ¬ (neA 2 M R ≤ (x 0).val ∧ (x 0).val < neB 2 M R)) :
    CovEx M R x := by
  obtain ⟨eP0, eP1, eA', eB', eA, eB, eQ1, eQ0, eN⟩ := ne2_vals (M := M) (R := R)
  have hcf := CfData.hcf
  have hcR : CfData.cf * M ≤ R * M := Nat.mul_le_mul_right M hR
  have hc10 : 10 * M ≤ CfData.cf * M := Nat.mul_le_mul_right M hcf
  have hb1 : bigSide M 2 1 = 2 * M := by simp only [bigSide]; ring
  have s1 : CfData.cf * bigSide M 2 1 = 2 * (CfData.cf * M) := by rw [hb1]; ring
  have dP1 : 2 * M ∣ neP1 2 M R := ⟨R + 2, by rw [eP1]; ring⟩
  have dQ1 : 2 * M ∣ neQ1 2 M R := ⟨7 * R + 2 * CfData.cf + 8, by rw [eQ1]; ring⟩
  have dc2M : 2 * M ∣ 2 * (CfData.cf * M) := ⟨CfData.cf, by ring⟩
  obtain ⟨s, hds, hlo, hhi, hsx1, hsx2⟩ :=
    tile (x := (x 0).val) dP1 dQ1 dc2M (by omega) (by omega) (by omega) (by omega)
  obtain ⟨sites, hq⟩ := mkCube hM hR (j := 1) (by norm_num) x s (by rw [hb1]; exact hds)
    ⟨hsx1, by rw [s1]; exact hsx2⟩ (by rw [s1]; omega)
    (fun w hw1 hw2 => by rw [s1] at hw2; show Bc M R 1 w ∨ Bc M R 2 w; rw [bc1, bc2]; omega)
    ⟨(x 0).val, hsx1, by rw [s1]; exact hsx2, by rw [bc1]; omega⟩
  exact ⟨sites, 1, hq⟩

#print axioms cov_L0left
#print axioms cov_L0right
#print axioms cov_thinL
#print axioms cov_thinR
#print axioms cov_fat
#print axioms cov_lev1

end

end CovAssume
