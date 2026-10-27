import C5G

/-!
# P4L1 -- the LOCALLY constructed domain `Omega_0(square)` of CMP99b p.408 (see READING.md), and its basic geometry.

Print (p.408, corpus/pages/CMP99b_p408.md line 29): for `square in D_j`, `Omega_j(square) = tilde-square^4`, and for `n < j` `Omega_n(square)` is a cube with the
centre of `square` and `dist(Omega_n(square)^c, Omega_{n+1}(square)) = 2 R_0 M_0 L^n eta`; "For n = 0 ... Omega_0(square) subset tilde-square^5".
Formal reading (all in fine-site units, `g = M ell^j`, `p = R_0 M_0`, half-open periodic cubes `cubeR`):
`Omega_n(square) = cubeR c (5 g + 2 p (ell^n + ... + ell^{j-1}))`.  NOT intersected with the global `Omega_0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409L

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.P409W
open AdalyFormal.P409C5
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle)

variable {L : PeriodicLatticeExtent}

/-- `ell^n + ... + ell^{j-1}`. -/
def collarSum (ell n j : ℕ) : ℕ := ∑ m ∈ Finset.Ico n j, ell ^ m

/-- half side of `Omega_n(square)` (fine sites): `5 g + 2 p (ell^n + ... + ell^{j-1})`, `g = M ell^j`, `p = R_0 M_0`. -/
def localHalf (ell p g j n : ℕ) : ℕ := 5 * g + 2 * p * collarSum ell n j

/-- `Omega_n(square)`, `n <= j`: the cube with the centre `c` of `square` and half side `localHalf`. -/
def localOm (ell p g j n : ℕ) (c : PeriodicLatticeSite L) : Set (PeriodicLatticeSite L) :=
  cubeR c (localHalf ell p g j n)

/-- `Omega_0(square)`. -/
def localOm0 (ell p g j : ℕ) (c : PeriodicLatticeSite L) : Set (PeriodicLatticeSite L) := localOm ell p g j 0 c

/-- `Omega_{j+1}(square) = tilde-square^3 cap B^{j+1}(Lambda_{j+1})` (p.408; recorded for completeness, not used for `Omega_0(square)`). -/
def localOmTop (g : ℕ) (S : Tower L) (j : ℕ) (c : PeriodicLatticeSite L) : Set (PeriodicLatticeSite L) :=
  tildeCube 3 g c ∩ towerBj S (j + 1)

/-- witness (print): `Omega_j(square) = tilde-square^4`. -/
theorem localOm_top (ell p g j : ℕ) (c : PeriodicLatticeSite L) : localOm ell p g j j c = tildeCube 4 g c := by
  unfold localOm localHalf collarSum tildeCube
  simp

/-- witness (print): the collar between consecutive local domains is `2 p ell^n`: `dist(Omega_n^c, Omega_{n+1}) = 2 R_0 M_0 L^n`. -/
theorem localHalf_step (ell p g j n : ℕ) (h : n < j) :
    localHalf ell p g j n = localHalf ell p g j (n + 1) + 2 * p * ell ^ n := by
  unfold localHalf collarSum
  rw [Finset.sum_eq_sum_Ico_succ_bot h]
  ring

theorem localHalf_ge_five (ell p g j n : ℕ) : 5 * g ≤ localHalf ell p g j n := by
  unfold localHalf; omega

theorem collarSum_zero_lt {ell : ℕ} (hell : 2 ≤ ell) (j : ℕ) : collarSum ell 0 j + 1 ≤ ell ^ j := by
  unfold collarSum
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_Ico_succ_top (Nat.zero_le j), pow_succ]
    have : 0 < ell ^ j := by positivity
    nlinarith

/-- print: "dist(Omega_0(square)^c, tilde-square^4) < 2 R_0 M_0 L^j eta, hence Omega_0(square) subset tilde-square^5" -- here with `2 p <= M`
(i.e. `K >= 2` in `M = K R_0 M_0`). -/
theorem localHalf_le_six {ell M p j : ℕ} (hell : 2 ≤ ell) (hp : 2 * p ≤ M) :
    localHalf ell p (bigSide M ell j) j 0 ≤ 6 * bigSide M ell j := by
  have h := collarSum_zero_lt hell j
  unfold localHalf bigSide
  have h1 : 2 * p * collarSum ell 0 j ≤ 2 * p * (ell ^ j) := Nat.mul_le_mul_left _ (by omega)
  have h2 : 2 * p * ell ^ j ≤ M * ell ^ j := Nat.mul_le_mul_right _ hp
  omega

theorem localOm0_sub_cube5 {ell p g j : ℕ} (c : PeriodicLatticeSite L) (h : localHalf ell p g j 0 ≤ 6 * g) :
    localOm0 ell p g j c ⊆ printedCube5 g c := by
  rw [printedCube5_eq]; exact cubeR_mono h

theorem cube4_sub_localOm0 (ell p g j : ℕ) (c : PeriodicLatticeSite L) : tildeCube 4 g c ⊆ localOm0 ell p g j c := by
  unfold tildeCube localOm0 localOm; exact cubeR_mono (by have := localHalf_ge_five ell p g j 0; omega)

/-- for `j >= 1` the tilde-square^5 of a `D_j` cube lies in `Omega_{j-1}` (hence in the global `Omega_0`): the collar clause of admissibility. -/
theorem cube5_sub_Om {ell M R k j : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R) (hA : Admissible ell M R k S)
    (hD : IsDCube ell M k S j c) (hj : 1 ≤ j) :
    printedCube5 (bigSide M ell j) c ⊆ S.Om (j - 1) := by
  obtain ⟨hjk, hgrid, x₀, hx0, hx0c⟩ := hD
  have hell0 : 0 < ell := by omega
  obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hx0c' : x₀ ∈ cubeR c (bigSide M ell j) := by rw [← dCube_eq]; exact hx0c
  intro y hy
  rw [printedCube5_eq] at hy
  have : j - 1 = j' := by omega
  rw [this]
  by_contra hn
  have hx1 : x₀ ∈ S.Om (j' + 1) := hj' ▸ hx0.1
  have hcol := AdalyFormal.M1.collar hA (j := j') (by omega) hn hx1
  have hb : bigSide M ell j = bigSide M ell j' * ell := by rw [hj']; exact AdalyFormal.M1.bigSide_succ M ell j'
  have h1 := cube_dist hx0c' hy
  rw [pdist_comm] at hcol
  have h2 : 21 * bigSide M ell j ≤ R * bigSide M ell j' := by
    rw [hb]
    calc 21 * (bigSide M ell j' * ell) = (21 * ell) * bigSide M ell j' := by ring
      _ ≤ R * bigSide M ell j' := Nat.mul_le_mul_right _ hR
  omega

theorem localOm0_sub_Om0 {ell M R k j p : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R) (hA : Admissible ell M R k S)
    (hD : IsDCube ell M k S j c) (hj : 1 ≤ j) (hp : 2 * p ≤ M) :
    localOm0 ell p (bigSide M ell j) j c ⊆ S.Om 0 := fun y hy =>
  AdalyFormal.M1.om_anti hA (Nat.zero_le (j - 1))
    (cube5_sub_Om hell hM hR hA hD hj (localOm0_sub_cube5 c (localHalf_le_six hell hp) hy))

end AdalyFormal.P409L
