import SoCov

/-!
# SoCov2 -- `CovEx`, `cov_arith`, level-0 shell cases (lane sites_only_20261019)
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

/-- the goal of every case: `x` lies in some class cube of factor `c` (index `j`). -/
def CovEx (ell M R c : ℕ) (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) : Prop :=
  ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))) (j : ℕ),
    IsClassCube ell M c 2 (neS ell M R) sites j ∧ x ∈ sites

/-- the extra atom facts used by every case. -/
theorem cov_arith {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hc : 10 ≤ c) (hRc : c ≤ R) :
    0 < ell * M ∧ 1 * (ell * M) ≤ (c - 1) * (ell * M) ∧ c * (ell * M) = (c - 1) * (ell * M) + ell * M ∧
      c * M ≤ R * M ∧ c * (ell * M) ≤ ell * (R * M) ∧ c * (ell * (ell * M)) ≤ ell * (ell * (R * M)) := by
  refine ⟨Nat.mul_pos (by omega) hM, Nat.mul_le_mul_right _ (by omega), ?_, Nat.mul_le_mul_right M hRc, ?_, ?_⟩
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  · calc c * (ell * M) ≤ R * (ell * M) := Nat.mul_le_mul_right _ hRc
      _ = ell * (R * M) := by ring
  · calc c * (ell * (ell * M)) ≤ R * (ell * (ell * M)) := Nat.mul_le_mul_right _ hRc
      _ = ell * (ell * (R * M)) := by ring

theorem cov_L0left {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) (hRc : c ≤ R)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (h1 : neP0 ell M R ≤ (x 0).val) (h2 : (x 0).val < neP1 ell M R) : CovEx ell M R c x := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := so_vals hell hM hR hrel hc
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := so_order hell hM hR hrel hc
  obtain ⟨hY1, cm1, e2, hcR, hc1, hc2⟩ := cov_arith (M := M) (R := R) hell hM hc hRc
  obtain ⟨-, -, -, -, -, -, -, -, -, b0P, b0Q, b1P, b1Q, b2A', b2B', b2A, b2B, -, -, -, -⟩ := ne_geo3_two hell hM hR
  have hb0 : bigSide M ell 0 = M := by simp [bigSide]
  have s0 : c * bigSide M ell 0 = c * M := by rw [hb0]
  have dcM : M ∣ c * M := ⟨c, by ring⟩
  have dA' : M ∣ neA' ell M R := Dvd.dvd.trans (Dvd.intro (ell ^ 2) rfl) b2A'
  obtain ⟨s, hds, hlo, hhi, hsx1, hsx2⟩ :=
    CovAssume.tile (x := (x 0).val) b0P dA' dcM (Nat.mul_pos (by omega) hM) (by omega) (by omega) (by omega)
  obtain ⟨sites, hq⟩ := mkCube hell hM hR hrel hc (j := 0) (by norm_num) x s (by rw [hb0]; exact hds)
    ⟨hsx1, by rw [s0]; exact hsx2⟩ (by rw [s0]; omega)
    (fun w hw1 hw2 => by rw [s0] at hw2; show Bc ell M R 0 w ∨ Bc ell M R 1 w; rw [bc0, bc1]; omega)
    ⟨(x 0).val, hsx1, by rw [s0]; exact hsx2, by rw [bc0]; omega⟩
  exact ⟨sites, 0, hq⟩

theorem cov_L0right {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) (hRc : c ≤ R)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (h1 : neQ1 ell M R ≤ (x 0).val) (h2 : (x 0).val < neQ0 ell M R) : CovEx ell M R c x := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := so_vals hell hM hR hrel hc
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := so_order hell hM hR hrel hc
  obtain ⟨hY1, cm1, e2, hcR, hc1, hc2⟩ := cov_arith (M := M) (R := R) hell hM hc hRc
  obtain ⟨-, -, -, -, -, -, -, -, -, b0P, b0Q, b1P, b1Q, b2A', b2B', b2A, b2B, -, -, -, -⟩ := ne_geo3_two hell hM hR
  have hb0 : bigSide M ell 0 = M := by simp [bigSide]
  have s0 : c * bigSide M ell 0 = c * M := by rw [hb0]
  have dcM : M ∣ c * M := ⟨c, by ring⟩
  have dB : M ∣ neB ell M R := Dvd.dvd.trans (Dvd.intro (ell ^ 2) rfl) b2B
  obtain ⟨s, hds, hlo, hhi, hsx1, hsx2⟩ :=
    CovAssume.tile (x := (x 0).val) dB b0Q dcM (Nat.mul_pos (by omega) hM) (by omega) (by omega) (by omega)
  obtain ⟨sites, hq⟩ := mkCube hell hM hR hrel hc (j := 0) (by norm_num) x s (by rw [hb0]; exact hds)
    ⟨hsx1, by rw [s0]; exact hsx2⟩ (by rw [s0]; omega)
    (fun w hw1 hw2 => by rw [s0] at hw2; show Bc ell M R 0 w ∨ Bc ell M R 1 w; rw [bc0, bc1]; omega)
    ⟨(x 0).val, hsx1, by rw [s0]; exact hsx2, by rw [bc0]; omega⟩
  exact ⟨sites, 0, hq⟩


end

end AdalyFormal.SitesOnly
