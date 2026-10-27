import SoZ1
import SoCov
import NuE8

/-!
# SoE7 -- chain rows at the decoupled layer edge and the window of four rows inside `Λ`, for general `ell >= 3` (lane sites_only_20261019)

* `layer_isRow_so`  : `soC + 1` and `soC + 1 - ell^2` are starts of level-2 rows (the layer edge `(soC, soC+1)` sits between two consecutive length-`ell^2` rows).
* `layer_rows_so`   : they are consecutive rows `i0, i0 + 1` of the chain.
* `window_rows_so`  : four consecutive length-`ell^2` rows at the unit slices `u0N + (ell - 3) + k`, `k = 0..3` (the slices `neLo + ell - 2 + k`), away from the collars.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.NcwdhTwo

section
variable [CfData]
variable {ell M R : ℕ}

theorem layer_isRow_so {c : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) :
    isRowN ell M R 2 (soC ell M R c + 1) ∧ isRowN ell M R 2 (soC ell M R c + 1 - ell ^ 2) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := SitesOnly.so_vals hell hM hR hrel hc
  have hsucc := soC_succ (ell := ell) (M := M) (R := R) hell hM (by omega : 1 ≤ c)
  have hY1 : 0 < ell * M := Nat.mul_pos (by omega) hM
  have hcm1 : 1 * (ell * M) ≤ (c - 1) * (ell * M) := Nat.mul_le_mul_right _ (by omega)
  have hMe : ell ≤ M := Nat.le_of_dvd hM hdvd
  have hee : ell * ell ≤ ell * M := Nat.mul_le_mul_left ell hMe
  obtain ⟨m, hm⟩ := hdvd
  have hd : ell ^ 2 ∣ soC ell M R c + 1 := by
    rw [hsucc]
    refine Nat.dvd_add (Nat.dvd_add ⟨R * M, by ring⟩ ⟨M, by ring⟩) ⟨(c - 1) * m, ?_⟩
    rw [hm]; ring
  have hsq : ell ^ 2 = ell * ell := pow_two ell
  constructor
  · refine ⟨hd, ?_⟩
    simp only [reg2]
    left
    omega
  · refine ⟨Nat.dvd_sub hd (dvd_refl _), ?_⟩
    simp only [reg2]
    left
    rw [hsq]
    omega

theorem layer_rows_so {c : ℕ} (hg : NGeo ell M R) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) :
    ∃ i0, i0 + 1 < RN hg ∧ neP0 ell M R + stN ell M R i0 = soC ell M R c + 1 - ell ^ 2 ∧ lnN ell M R i0 = ell ^ 2 ∧
      lnN ell M R (i0 + 1) = ell ^ 2 := by
  have hell := hg.hell
  obtain ⟨hrow1, hrow0⟩ := layer_isRow_so hell hdvd hM hR hrel hc
  obtain ⟨i, hiR, hi1, hi2⟩ := chain_row_of_isRowN hg (j := 2) le_rfl hrow1
  obtain ⟨i', hi'R, hi'1, hi'2⟩ := chain_row_of_isRowN hg (j := 2) le_rfl hrow0
  have hsucc : stN ell M R (i' + 1) = stN ell M R i := by
    rw [stN_succ, hi'2]
    have hee : ell ^ 2 ≤ soC ell M R c + 1 := by
      obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
      obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := SitesOnly.so_vals hell hM hR hrel hc
      have hsucc := soC_succ (ell := ell) (M := M) (R := R) hell hM (by omega : 1 ≤ c)
      have hMe : ell ≤ M := Nat.le_of_dvd hM hdvd
      have h1 : ell * ell ≤ ell * M := Nat.mul_le_mul_left ell hMe
      have h2 : ell * M ≤ ell * (ell * M) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
      have hsq : ell ^ 2 = ell * ell := pow_two ell
      rw [hsq]; omega
    have hP0 := hg.cRM
    have := hrow0.2
    omega
  have hii : i' + 1 = i := stN_inj hg hsucc
  refine ⟨i', by omega, hi'1, hi'2, ?_⟩
  rw [hii]; exact hi2

theorem window_rows_so (hg : NGeo ell M R) (hell3 : 3 ≤ ell) (hMe : ell ≤ M) :
    ∃ i1, R * M ≤ i1 ∧ i1 + 3 + R * M < RN hg ∧ (∀ k, k ≤ 3 → lnN ell M R (i1 + k) = ell ^ 2) ∧
      (∀ k, k ≤ 3 → neP0 ell M R + stN ell M R (i1 + k) = ell ^ 2 * (u0N M R + (ell - 3) + k)) := by
  have hP := hg.hP0P1; have h1 := hg.hP1A; have h2 := hg.hAB'; have h3 := hg.hB'A; have h4 := hg.hAB
  have h5 := hg.hBQ1; have h6 := hg.hQ1Q0
  have hcP := hg.cP
  have hTA : neA ell M R ≤ ell ^ 2 * (u0N M R + (ell - 3)) := (fat_bounds hg hMe (j := ell - 3) (by omega)).1
  have hTB : ell ^ 2 * (u0N M R + (ell - 3) + 3) < neB ell M R := by
    have := (fat_bounds hg hMe (j := ell) le_rfl).2
    rwa [show u0N M R + (ell - 3) + 3 = u0N M R + ell by omega]
  have hTle : ell ^ 2 * (u0N M R + (ell - 3)) ≤ ell ^ 2 * (u0N M R + (ell - 3) + 3) := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨i1, hi1R, hi1⟩ := hit_aligned2 hg (T := ell ^ 2 * (u0N M R + (ell - 3))) (dvd_mul_right _ _) (by omega) (by omega)
  have hrows : ∀ k, k ≤ 4 → neP0 ell M R + stN ell M R (i1 + k) = ell ^ 2 * (u0N M R + (ell - 3) + k) := by
    intro k
    induction k with
    | zero => intro _; simpa using hi1
    | succ k ih =>
      intro hk
      have h1' := ih (by omega)
      have hreg : isRowN ell M R 2 (neP0 ell M R + stN ell M R (i1 + k)) := by
        rw [h1']
        have := fat_reg2 hg hMe (j := ell - 3 + k) (by omega)
        rwa [show u0N M R + (ell - 3) + k = u0N M R + (ell - 3 + k) by ring]
      have hl := stN_level2_succ hg hreg
      have e : stN ell M R (i1 + (k + 1)) = stN ell M R (i1 + k) + lnN ell M R (i1 + k) := by
        rw [← Nat.add_assoc]; exact stN_succ _
      have e2 : ell ^ 2 * (u0N M R + (ell - 3) + (k + 1)) = ell ^ 2 * (u0N M R + (ell - 3) + k) + ell ^ 2 := by ring
      rw [e, hl]; omega
  have hln : ∀ k, k ≤ 3 → lnN ell M R (i1 + k) = ell ^ 2 := by
    intro k hk
    have hreg : isRowN ell M R 2 (neP0 ell M R + stN ell M R (i1 + k)) := by
      rw [hrows k (by omega)]
      have := fat_reg2 hg hMe (j := ell - 3 + k) (by omega)
      rwa [show u0N M R + (ell - 3) + k = u0N M R + (ell - 3 + k) by ring]
    exact stN_level2_succ hg hreg
  have hlowc : R * M ≤ i1 := by
    by_contra hcon
    push Not at hcon
    have := stN_left hg i1 hcon.le
    have hh := hrows 0 (by omega)
    simp only [add_zero] at hh
    omega
  have hiQ : i1 + 3 < iQ hg := by
    by_contra hcon
    push Not at hcon
    have h1 := stN_mono hg hcon
    have h2 := iQ_hit hg
    have h3 := hrows 3 (by omega)
    omega
  refine ⟨i1, hlowc, ?_, hln, fun k hk => hrows k (by omega)⟩
  have := iQ_RN hg
  omega

end

#print axioms layer_isRow_so
#print axioms layer_rows_so
#print axioms window_rows_so

end AdalyFormal.SitesOnly
