import SectBIdentity
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HConstruction.SectBP1
open HConstruction.GenK HConstruction.SectBBase
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (RMap)
open AdalyFormal.Balaban.CoarseRestrictTransported (staircaseTransport staircaseBonds axisBonds coarseRestrictSiteCovariantU)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf)
variable (M : PeriodicLatticeExtent) {n : ℕ}

/-- The literal ordered, forward-only contour of the actual transported average
has at most 3(n−1) links inside an n-block, independently of volume. -/
theorem staircase_length_le (hn : 0 < n) (y : Centers M (n := n))
    (x : PeriodicLatticeSite (fineExtent M n)) (hx : x ∈ blockOf y.1 n) :
    (staircaseBonds y.1 x).length ≤ 3*(n-1) := by
  have hlen : (staircaseBonds y.1 x).length =
      ((x 2).val - (y.1 2).val) + ((x 1).val - (y.1 1).val) +
        ((x 0).val - (y.1 0).val) := by
    simp [staircaseBonds, axisBonds]
    omega
  have h0 := (mem_blockOf.mp hx (0:Fin 3))
  have h1 := (mem_blockOf.mp hx (1:Fin 3))
  have h2 := (mem_blockOf.mp hx (2:Fin 3))
  rw [hlen]
  omega

/-- Exact F'₂ site kernel from (3.58)–(3.60), for the declared staircase transport.
The estimate of its kernel is a separate, unproved step, not encoded in this identity. -/
theorem qDrift_block (U : Links M (n := n)) (f : Site M (n := n))
    (y : Centers M (n := n)) :
    qDrift M U f y = (1/(n:ℝ)^3) •
      ∑ x ∈ blockOf y.1 n, (RMap (staircaseTransport U y.1 x) (f x) - f x) := by
  change covQPrime M U f y - flatQPrime M f y = _
  rw [covQPrime_apply, flatQPrime_block]
  unfold coarseRestrictSiteCovariantU
  rw [← smul_sub, ← Finset.sum_sub_distrib]
/-- A2's actual block kernel estimate, conditional only on a concrete supremum
of the transport along the printed-style staircase. No volume-count is taken. -/
theorem qDrift_block_bound (U : Links M (n := n)) (f : Site M (n := n))
    (y : Centers M (n := n)) (β : ℝ)
    (hpath : ∀ x ∈ blockOf y.1 n,
      AdalyFormal.Balaban.RMapLipschitz.frobNorm
        ((↑(staircaseTransport U y.1 x) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ β) :
    ‖qDrift M U f y‖ ≤
      (1/(n:ℝ)^3) * (∑ x ∈ blockOf y.1 n, 2*β*‖f x‖) := by
  rw [qDrift_block, norm_smul, Real.norm_eq_abs]
  have hpos : 0 ≤ (1/(n:ℝ)^3) := by positivity
  rw [abs_of_nonneg hpos]
  apply mul_le_mul_of_nonneg_left _ hpos
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x hx
  have hb := AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le
    (staircaseTransport U y.1 x) (f x)
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hpath x hx) (by norm_num : (0:ℝ) ≤ 2)) (norm_nonneg _))
end HConstruction.SectBP1
