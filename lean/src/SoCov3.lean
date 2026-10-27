import SoCov2

/-!
# SoCov3 -- thin-component cases (lane sites_only_20261019)
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

theorem cov_thinL {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) (hRc : c ≤ R)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (h1 : neA' ell M R ≤ (x 0).val) (h2 : (x 0).val < neA' ell M R + (c - 1) * (ell * M)) : CovEx ell M R c x := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := so_vals hell hM hR hrel hc
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := so_order hell hM hR hrel hc
  obtain ⟨hY1, cm1, e2, hcR, hc1, hc2⟩ := cov_arith (M := M) (R := R) hell hM hc hRc
  obtain ⟨-, -, -, -, -, -, -, -, -, b0P, b0Q, b1P, b1Q, b2A', b2B', b2A, b2B, -, -, -, -⟩ := ne_geo3_two hell hM hR
  have hb1 : bigSide M ell 1 = ell * M := by simp only [bigSide]; ring
  have s1 : c * bigSide M ell 1 = c * (ell * M) := by rw [hb1]
  have dA'1 : ell * M ∣ neA' ell M R := Dvd.dvd.trans (Dvd.intro ell (by ring)) b2A'
  obtain ⟨s, hs'⟩ : ∃ s, s = neA' ell M R - ell * M := ⟨_, rfl⟩
  obtain ⟨sites, hq⟩ := mkCube hell hM hR hrel hc (j := 1) (by norm_num) x s
    (by rw [hb1, hs']; exact Nat.dvd_sub dA'1 (dvd_refl _))
    ⟨by omega, by rw [s1]; omega⟩ (by rw [s1]; omega)
    (fun w hw1 hw2 => by rw [s1] at hw2; show Bc ell M R 1 w ∨ Bc ell M R 2 w; rw [bc1, bc2]; omega)
    ⟨neA' ell M R - 1, by omega, by rw [s1]; omega, by rw [bc1]; omega⟩
  exact ⟨sites, 1, hq⟩

theorem cov_thinR {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) (hRc : c ≤ R)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (h1 : neA' ell M R + (c - 1) * (ell * M) ≤ (x 0).val) (h2 : (x 0).val < neB' ell M R) : CovEx ell M R c x := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := so_vals hell hM hR hrel hc
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := so_order hell hM hR hrel hc
  obtain ⟨hY1, cm1, e2, hcR, hc1, hc2⟩ := cov_arith (M := M) (R := R) hell hM hc hRc
  obtain ⟨-, -, -, -, -, -, -, -, -, b0P, b0Q, b1P, b1Q, b2A', b2B', b2A, b2B, -, -, -, -⟩ := ne_geo3_two hell hM hR
  have hb1 : bigSide M ell 1 = ell * M := by simp only [bigSide]; ring
  have s1 : c * bigSide M ell 1 = c * (ell * M) := by rw [hb1]
  have dA'1 : ell * M ∣ neA' ell M R := Dvd.dvd.trans (Dvd.intro ell (by ring)) b2A'
  obtain ⟨s, hs'⟩ : ∃ s, s = neA' ell M R + (c - 1) * (ell * M) := ⟨_, rfl⟩
  obtain ⟨sites, hq⟩ := mkCube hell hM hR hrel hc (j := 1) (by norm_num) x s
    (by rw [hb1, hs']; exact Nat.dvd_add dA'1 (Dvd.intro_left _ rfl))
    ⟨by omega, by rw [s1]; omega⟩ (by rw [s1]; omega)
    (fun w hw1 hw2 => by rw [s1] at hw2; show Bc ell M R 1 w ∨ Bc ell M R 2 w; rw [bc1, bc2]; omega)
    ⟨neB' ell M R, by omega, by rw [s1]; omega, by rw [bc1]; omega⟩
  exact ⟨sites, 1, hq⟩


end

end AdalyFormal.SitesOnly
