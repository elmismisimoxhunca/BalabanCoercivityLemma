import M2B6a
import M2B2

/-!
# M2B6b -- geometry of the cut-off stencil, the decomposition `ddA(χA) = χ·ddA(A) + η⁻¹ Σ_ν η⁻¹ R_ν`, and the scalar inequality
(m2_bridge_20261014, Layer B1)
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Bridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_shift_le pdist_triangle)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)

variable {L : PeriodicLatticeExtent}

theorem pdist_self' (x : PeriodicLatticeSite L) : pdist x x = 0 := by
  unfold pdist; simp [pcd_self']

theorem pdist_shiftBack_le (x : PeriodicLatticeSite L) (ν : Fin 3) : pdist x (periodicLatticeShiftBack x ν) ≤ 1 := by
  have := pdist_shift_le (periodicLatticeShiftBack x ν) ν
  rw [periodicLatticeShift_shiftBack] at this
  rw [pdist_comm]; exact this

/-- a nonzero value of the cutoff within `2` of `x` puts the whole `4`-ball of `x` in the box. -/
theorem cut_hx4 {sites : Set (PeriodicLatticeSite L)} {χ : PeriodicLatticeSite L → ℝ} {τ1 τ2 : ℝ}
    (hc : CutSpec sites χ τ1 τ2) {x p : PeriodicLatticeSite L} (hp : χ p ≠ 0) (hxp : pdist x p ≤ 2) :
    ∀ y, pdist x y ≤ 4 → y ∈ sites := by
  intro y hy
  apply hc.supp p hp y
  have := pdist_triangle p x y
  rw [pdist_comm p x] at this
  omega

theorem cubeBond_of_near {sites : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hx : ∀ y, pdist x y ≤ 4 → y ∈ sites) {e : Bond L} (he : pdist x e.1 ≤ 3) : CubeBond sites e := by
  refine ⟨hx _ (by omega), hx _ ?_⟩
  have h1 := pdist_triangle x e.1 (periodicLatticeShift e.1 e.2)
  have h2 := pdist_shift_le e.1 e.2
  omega

theorem curlReads_of_near {sites : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hx : ∀ y, pdist x y ≤ 4 → y ∈ sites) {y : PeriodicLatticeSite L} (hy : pdist x y ≤ 1) (a b : Fin 3) :
    CurlReads sites y a b := by
  have hs : ∀ c : Fin 3, pdist x (periodicLatticeShift y c) ≤ 2 := fun c => by
    have h1 := pdist_triangle x y (periodicLatticeShift y c)
    have h2 := pdist_shift_le y c
    omega
  exact ⟨cubeBond_of_near hx (e := (periodicLatticeShift y a, b)) (hs a |>.trans (by norm_num)),
    cubeBond_of_near hx (e := (y, b)) (hy.trans (by norm_num)),
    cubeBond_of_near hx (e := (periodicLatticeShift y b, a)) (hs b |>.trans (by norm_num)),
    cubeBond_of_near hx (e := (y, a)) (hy.trans (by norm_num))⟩

/-- the scalar inequality closing the `ddA` estimate. -/
theorem scal_final {K E η τ1 τ2 X : ℝ} (hK : 0 < K) (hE : 1 ≤ E) (hη : 0 < η) (hX : X = (E * η)⁻¹)
    (h1 : 64 * τ1 * E ≤ 1) (h2 : 24 * (τ2 + τ1 ^ 2) * E ^ 2 ≤ 1) (hτ1 : 0 ≤ τ1) (hτ2 : 0 ≤ τ2) :
    η⁻¹ * (3 * (η⁻¹ * (8 * τ1 * (η * (K * X ^ 2)) + (τ2 + τ1 ^ 2) * (K * X)))) ≤ K * X ^ 3 / 2 := by
  have hE0 : 0 < E := by linarith
  have hX0 : 0 < X := by rw [hX]; positivity
  have hηX : η = (E * X)⁻¹ := by rw [hX]; field_simp
  have eq : η⁻¹ * (3 * (η⁻¹ * (8 * τ1 * (η * (K * X ^ 2)) + (τ2 + τ1 ^ 2) * (K * X))))
      = 3 * (K * X ^ 3) * (8 * τ1 * E + (τ2 + τ1 ^ 2) * E ^ 2) := by
    rw [hηX]
    field_simp
  rw [eq]
  have hKX : 0 ≤ K * X ^ 3 := by positivity
  have hb : 3 * (8 * τ1 * E + (τ2 + τ1 ^ 2) * E ^ 2) ≤ 1 / 2 := by nlinarith [sq_nonneg τ1]
  calc 3 * (K * X ^ 3) * (8 * τ1 * E + (τ2 + τ1 ^ 2) * E ^ 2)
      = (K * X ^ 3) * (3 * (8 * τ1 * E + (τ2 + τ1 ^ 2) * E ^ 2)) := by ring
    _ ≤ (K * X ^ 3) * (1 / 2) := mul_le_mul_of_nonneg_left hb hKX
    _ = K * X ^ 3 / 2 := by ring

end AdalyFormal.M2Bridge

#print axioms AdalyFormal.M2Bridge.cut_hx4
#print axioms AdalyFormal.M2Bridge.curlReads_of_near
#print axioms AdalyFormal.M2Bridge.scal_final
