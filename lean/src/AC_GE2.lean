import GE2
import AC_Base

/-! AC copy of GE2: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2GlueGeo

open AdalyFormal.AllC
variable {fc : ℕ} [CubeFactor fc]

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle)
open AdalyFormal.M1 (om_anti)
open AdalyFormal.M2Bridge (pdist_lt_three_s')

variable {L : PeriodicLatticeExtent}

theorem cube_scaleAC {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 0 < M)
    {m : ℕ} (hmk : m ≤ k) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (hq : IsClassCube ell M fc k S sites j) {q0 x' : PeriodicLatticeSite L} (hq0 : q0 ∈ sites)
    (hx' : x' ∈ S.Om (m + 1))
    (hd : 2 * pdist q0 x' + 3 * (fc * bigSide M ell m) ≤ 2 * (R * bigSide M ell m)) : m ≤ j := by
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
  have hq0b : q0 ∈ siteBox z (fc * bigSide M ell j) := hbox ▸ hq0
  have hy'b : y' ∈ siteBox z (fc * bigSide M ell j) := hbox ▸ hy'S
  have h3 := pdist_lt_three_s' hy'b hq0b
  have h4 := pdist_triangle y' q0 x'
  have h6 := bigSide_succ_le (ell := ell) (M := M) hell hM hjm
  have h8 : fc * (2 * bigSide M ell j) ≤ fc * bigSide M ell m := Nat.mul_le_mul_left fc h6
  have h9 : fc * (2 * bigSide M ell j) = 2 * (fc * bigSide M ell j) := by ring
  omega

theorem cube_blockClosedAC {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 0 < M)
    {m : ℕ} (hmk : m ≤ k) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (hq : IsClassCube ell M fc k S sites j) (hmj : m ≤ j) : BlockClosed (bigSide M ell m) sites := by
  obtain ⟨hjk, ⟨z, hgrid, hbox⟩, -, -⟩ := hq.1
  have hdv := bigSide_dvd (ell := ell) (M := M) hmj
  rw [hbox]
  refine siteBox_blockClosed (bigSide_pos (by omega) hM m) (fun μ => hS.2.2.1 m hmk μ) (fun μ => ?_)
    (Dvd.dvd.mul_left hdv fc)
  exact Nat.mod_eq_zero_of_dvd (dvd_trans hdv (Nat.dvd_of_mod_eq_zero (hgrid μ)))

end AdalyFormal.M2GlueGeo

