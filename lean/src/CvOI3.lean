import CvOI2
import CvO48

/-!
# CvOI3 -- the slice Euler-Lagrange identity: `zprof (omegaW ..) (fe e) (P0 + x) = BF .. e (single x)` (lane omega)

`fe P0 e`: the profile `v ↦ e_{v - P0}` (zero outside `[P0, P0 + n)`).  `omegaW_edge`: the (0,1)-plaquette weight of the edge `(P0 + y, P0 + y + 1)` is the chain weight `Wt Cc (cos t) y`
(`Cc = neC - P0`), and `0` off the chain.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open Finset
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi

variable {ell M R : ℕ}

/-- the profile of a chain vector. -/
noncomputable def fe {n : ℕ} (P0 : ℕ) (e : Fin n → ℝ) (v : ℕ) : ℝ := if P0 ≤ v then ex e (v - P0) else 0

theorem fe_at {n : ℕ} (P0 : ℕ) (e : Fin n → ℝ) (x : Fin n) : fe P0 e (P0 + x.val) = e x := by
  unfold fe
  rw [if_pos (by omega), show P0 + x.val - P0 = x.val by omega]
  unfold ex; rw [dif_pos x.2]

theorem fe_lt {n : ℕ} (P0 : ℕ) (e : Fin n → ℝ) {v : ℕ} (hv : v < P0) : fe P0 e v = 0 := by
  unfold fe; rw [if_neg (by omega)]

theorem fe_ge {n : ℕ} (P0 : ℕ) (e : Fin n → ℝ) {v : ℕ} (hv : P0 + n ≤ v) : fe P0 e v = 0 := by
  unfold fe; rw [if_pos (by omega)]
  unfold ex; rw [dif_neg (by omega)]

/-- the chain weight of an edge as a real-valued function of an integer index. -/
theorem omegaW_edge (hg : NGeo ell M R) (t : ℝ) {N : ℕ} (hN : neQ0 ell M R ≤ N) (y : ℕ) (hy : y + 1 < nN ell M R) :
    omegaW (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) N (neC ell M R) t (neP0 ell M R + y) =
      AdalyFormal.CoverJacobi.Wt (neC ell M R - neP0 ell M R) (Real.cos t) (y : ℤ) := by
  classical
  have hnxt : nxt N (neP0 ell M R + y) = neP0 ell M R + y + 1 := by
    unfold nxt; rw [if_neg]; unfold nN at hy; omega
  unfold omegaW
  rw [hnxt]
  have hJ : (neP0 ell M R ≤ neP0 ell M R + y ∧ neP0 ell M R + y < neQ0 ell M R) ∧
      (neP0 ell M R ≤ neP0 ell M R + y + 1 ∧ neP0 ell M R + y + 1 < neQ0 ell M R) := by
    unfold nN at hy; omega
  rw [if_pos hJ]
  unfold AdalyFormal.CoverJacobi.Wt
  have hCc : neP0 ell M R ≤ neC ell M R := by
    have := layer_lo hg; have := hg.hP0P1; have := hg.hP1A; omega
  by_cases h1 : y + 1 = neC ell M R - neP0 ell M R
  · have e1 : neP0 ell M R + y + 1 = neC ell M R := by omega
    have e2 : ¬ (neP0 ell M R + y = neC ell M R) := by omega
    rw [if_pos e1, if_neg e2, if_pos (Or.inl (by omega))]
    congr 1; ring
  · by_cases h2 : y = neC ell M R - neP0 ell M R
    · have e1 : ¬ (neP0 ell M R + y + 1 = neC ell M R) := by omega
      have e2 : neP0 ell M R + y = neC ell M R := by omega
      rw [if_neg e1, if_pos e2, if_pos (Or.inr (by omega))]
      rw [show t * (0 - 1) = -t by ring, Real.cos_neg]
    · have e1 : ¬ (neP0 ell M R + y + 1 = neC ell M R) := by omega
      have e2 : ¬ (neP0 ell M R + y = neC ell M R) := by omega
      rw [if_neg e1, if_neg e2, if_neg]
      · simp
      · omega

theorem omegaW_off (hg : NGeo ell M R) (t : ℝ) {N : ℕ} (hN : neQ0 ell M R ≤ N) {u : ℕ}
    (hu : u < neP0 ell M R ∨ neQ0 ell M R ≤ u + 1) (huN : u ≠ N) :
    omegaW (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) N (neC ell M R) t u = 0 := by
  classical
  unfold omegaW
  rw [if_neg]
  unfold nxt
  rw [if_neg huN]
  omega

end AdalyFormal.CoverOmega
