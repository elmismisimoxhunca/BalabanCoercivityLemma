import SoCov3

/-!
# SoCov4 -- fat component and level-1 cases (lane sites_only_20261019)
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
open MXQ.AllC
open NcwdhFam

section
variable [CfData]
local notation "cfv" => CfData.cf

theorem cov_fat {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) (hRc : c ≤ R)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (h1 : neA ell M R ≤ (x 0).val) (h2 : (x 0).val < neB ell M R) : CovEx ell M R c x := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := so_vals hell hM hR hrel hc
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := so_order hell hM hR hrel hc
  obtain ⟨hY1, cm1, e2, hcR, hc1, hc2⟩ := cov_arith (M := M) (R := R) hell hM hc hRc
  obtain ⟨-, -, -, -, -, -, -, -, -, b0P, b0Q, b1P, b1Q, b2A', b2B', b2A, b2B, -, -, -, -⟩ := ne_geo3_two hell hM hR
  have hb2 : bigSide M ell 2 = ell * (ell * M) := by simp only [bigSide]; ring
  have s2 : c * bigSide M ell 2 = c * (ell * (ell * M)) := by rw [hb2]
  have e22 : M * ell ^ 2 = ell * (ell * M) := by ring
  have dA : ell * (ell * M) ∣ neA ell M R := by rw [← e22]; exact b2A
  have dB : ell * (ell * M) ∣ neB ell M R := by rw [← e22]; exact b2B
  have dcY : ell * (ell * M) ∣ c * (ell * (ell * M)) := Dvd.intro_left _ rfl
  obtain ⟨s, hds, hlo, hhi, hsx1, hsx2⟩ :=
    CovAssume.tile (x := (x 0).val) dA dB dcY (by apply Nat.mul_pos (by omega); exact Nat.mul_pos (by omega) (Nat.mul_pos (by omega) hM)) (by omega) (by omega) (by omega)
  obtain ⟨sites, hq⟩ := mkCube hell hM hR hrel hc (j := 2) (by norm_num) x s (by rw [hb2]; exact hds)
    ⟨hsx1, by rw [s2]; exact hsx2⟩ (by rw [s2]; omega)
    (fun w hw1 hw2 => by rw [s2] at hw2; show Bc ell M R 2 w ∨ Bc ell M R 3 w; rw [bc2, bc3]; omega)
    ⟨(x 0).val, hsx1, by rw [s2]; exact hsx2, by rw [bc2]; omega⟩
  exact ⟨sites, 2, hq⟩

theorem cov_lev1 {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) (hRc : c ≤ R)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (h1 : neP1 ell M R ≤ (x 0).val) (h2 : (x 0).val < neQ1 ell M R)
    (h3 : ¬ (neA' ell M R ≤ (x 0).val ∧ (x 0).val < neB' ell M R)) (h4 : ¬ (neA ell M R ≤ (x 0).val ∧ (x 0).val < neB ell M R)) :
    CovEx ell M R c x := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := so_vals hell hM hR hrel hc
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := so_order hell hM hR hrel hc
  obtain ⟨hY1, cm1, e2, hcR, hc1, hc2⟩ := cov_arith (M := M) (R := R) hell hM hc hRc
  obtain ⟨-, -, -, -, -, -, -, -, -, b0P, b0Q, b1P, b1Q, b2A', b2B', b2A, b2B, -, -, -, -⟩ := ne_geo3_two hell hM hR
  have hb1 : bigSide M ell 1 = ell * M := by simp only [bigSide]; ring
  have s1 : c * bigSide M ell 1 = c * (ell * M) := by rw [hb1]
  have eM : M * ell = ell * M := Nat.mul_comm _ _
  have dP1 : ell * M ∣ neP1 ell M R := by rw [← eM]; exact b1P
  have dQ1 : ell * M ∣ neQ1 ell M R := by rw [← eM]; exact b1Q
  have dcY : ell * M ∣ c * (ell * M) := Dvd.intro_left _ rfl
  obtain ⟨s, hds, hlo, hhi, hsx1, hsx2⟩ :=
    CovAssume.tile (x := (x 0).val) dP1 dQ1 dcY (Nat.mul_pos (by omega) hY1) (by omega) (by omega) (by omega)
  obtain ⟨sites, hq⟩ := mkCube hell hM hR hrel hc (j := 1) (by norm_num) x s (by rw [hb1]; exact hds)
    ⟨hsx1, by rw [s1]; exact hsx2⟩ (by rw [s1]; omega)
    (fun w hw1 hw2 => by rw [s1] at hw2; show Bc ell M R 1 w ∨ Bc ell M R 2 w; rw [bc1, bc2]; omega)
    ⟨(x 0).val, hsx1, by rw [s1]; exact hsx2, by rw [bc1]; omega⟩
  exact ⟨sites, 1, hq⟩


end

end AdalyFormal.SitesOnly
