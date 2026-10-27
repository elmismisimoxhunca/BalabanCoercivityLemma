import GE1

/-!
# GE2 -- which scale do the class cubes near a site live on? (m2_gluegeo, 2026-10-15)

* `cube_scale`: a class cube `C` of index `j` containing a site `q0` that is within `(R - 18) b_m` of `Ω_{m+1}` has index `j >= m`
  (the cubes of index `< m` have diameter `< 36 b_{m-1}` and reach `B^{j}`, which lies `> R b_m` from `Ω_{m+1}`).
* `cube_blockClosed`: a class cube of index `j >= m` is a union of `b_m`-blocks (`b_m = M ell^m`).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2GlueGeo

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle)
open AdalyFormal.M1 (om_anti)
open AdalyFormal.M2Bridge (pdist_lt_three_s')

variable {L : PeriodicLatticeExtent}

theorem bigSide_pos {ell M : ℕ} (hell : 0 < ell) (hM : 0 < M) (j : ℕ) : 0 < bigSide M ell j := by
  unfold bigSide; positivity

theorem bigSide_succ_le {ell M j m : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hjm : j < m) :
    2 * bigSide M ell j ≤ bigSide M ell m := by
  unfold bigSide
  have h1 : ell ^ (j + 1) ≤ ell ^ m := Nat.pow_le_pow_right (by omega) hjm
  have h2 : 2 * ell ^ j ≤ ell ^ (j + 1) := by rw [pow_succ]; nlinarith [pow_pos (show 0 < ell by omega) j]
  calc 2 * (M * ell ^ j) = M * (2 * ell ^ j) := by ring
    _ ≤ M * ell ^ m := Nat.mul_le_mul_left M (h2.trans h1)

theorem bigSide_dvd {ell M j m : ℕ} (hjm : m ≤ j) : bigSide M ell m ∣ bigSide M ell j := by
  unfold bigSide
  exact mul_dvd_mul_left M (pow_dvd_pow ell hjm)

theorem cube_scale {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 0 < M)
    {m : ℕ} (hmk : m ≤ k) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (hq : IsClassCube ell M 12 k S sites j) {q0 x' : PeriodicLatticeSite L} (hq0 : q0 ∈ sites)
    (hx' : x' ∈ S.Om (m + 1)) (hd : pdist q0 x' + 18 * bigSide M ell m ≤ R * bigSide M ell m) : m ≤ j := by
  by_contra hc
  have hjm : j < m := by omega
  obtain ⟨-, ⟨z, -, hbox⟩, -, ⟨y', hy'S, hy'B⟩⟩ := hq.1
  have hy'not : y' ∉ S.Om m := by
    intro h
    have : S.Om m ⊆ S.Om (j + 1) := om_anti hS hjm
    exact hy'B.2 (this h)
  have h5 := hS.2.2.2.2.1 m hmk y' hy'not x' (by
    have : S.Om (m + 1) ⊆ S.Om m := hS.1 m
    exact hx')
  have hq0b : q0 ∈ siteBox z (12 * bigSide M ell j) := hbox ▸ hq0
  have hy'b : y' ∈ siteBox z (12 * bigSide M ell j) := hbox ▸ hy'S
  have h3 := pdist_lt_three_s' hy'b hq0b
  have h4 := pdist_triangle y' q0 x'
  have h6 := bigSide_succ_le (ell := ell) (M := M) hell hM hjm
  omega

theorem cube_blockClosed {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 0 < M)
    {m : ℕ} (hmk : m ≤ k) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (hq : IsClassCube ell M 12 k S sites j) (hmj : m ≤ j) : BlockClosed (bigSide M ell m) sites := by
  obtain ⟨hjk, ⟨z, hgrid, hbox⟩, -, -⟩ := hq.1
  have hdv := bigSide_dvd (ell := ell) (M := M) hmj
  rw [hbox]
  refine siteBox_blockClosed (bigSide_pos (by omega) hM m) (fun μ => hS.2.2.1 m hmk μ) (fun μ => ?_)
    (Dvd.dvd.mul_left hdv 12)
  exact Nat.mod_eq_zero_of_dvd (dvd_trans hdv (Nat.dvd_of_mod_eq_zero (hgrid μ)))

end AdalyFormal.M2GlueGeo
