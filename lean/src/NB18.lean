import NB17
/-!
# NB18 -- `prop1_level`: one level of NONABELIAN curvature blocking for the tree's blocking map

See NB17 header.  Statement: `m = s·ell ∣ N_ρ`, `2m < N_ρ`, all `s`-aligned stride-`s` plaquette defects
`≤ P`, `ell⁴ P ≤ 10⁻⁵`  ⟹  at every `m`-aligned `y`:
`dv (pw m (ubarSU2 s ell V) y ν μ) ≤ ell² P + 10⁶ ell⁴ P²`.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf coarseGaugeTransform)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarSU2_gauge)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice coarseLattice_mem_fits)

variable {L : PeriodicLatticeExtent}

theorem arith_bound (l P : ℝ) (hl : 1 ≤ l) (hP0 : 0 ≤ P) (hδ : l ^ 4 * P ≤ 1 / 100000) :
    8 * l * (8 * l * P) ≤ 1 / (8 * Real.pi) ∧
    4 * (9 * l * (8 * l * P) + 200 * Real.pi * (l ^ 2 * (8 * l * P) ^ 2)) ≤ 1 / (2 * Real.pi) ∧
    l ^ 2 * (P + P ^ 3 / 8 + 32 * Real.pi * (8 * l * P) ^ 2)
      + 800 * Real.pi * (l ^ 2 * (8 * l * P) ^ 2)
      + 2 * Real.pi * (4 * (9 * l * (8 * l * P) + 200 * Real.pi * (l ^ 2 * (8 * l * P) ^ 2))) ^ 2
      ≤ l ^ 2 * P + 1000000 * (l ^ 4 * P ^ 2) := by
  have hpi := Real.pi_gt_three
  have hpi2 := Real.pi_lt_d2
  set u := l ^ 2 * P with hu
  have hl2 : 1 ≤ l ^ 2 := by nlinarith
  have hu0 : 0 ≤ u := by positivity
  have hul : u ≤ l ^ 4 * P := by
    have : l ^ 4 * P = l ^ 2 * u := by rw [hu]; ring
    rw [this]; nlinarith
  have hu5 : u ≤ 1 / 100000 := le_trans hul hδ
  have hPu : P ≤ u := by rw [hu]; nlinarith
  have e1 : 8 * l * (8 * l * P) = 64 * u := by rw [hu]; ring
  have e2 : l ^ 2 * (8 * l * P) ^ 2 = 64 * u ^ 2 := by rw [hu]; ring
  have e3 : 9 * l * (8 * l * P) = 72 * u := by rw [hu]; ring
  have e4 : l ^ 4 * P ^ 2 = u ^ 2 := by rw [hu]; ring
  have e5 : l ^ 2 * (32 * Real.pi * (8 * l * P) ^ 2) = 32 * Real.pi * (64 * u ^ 2) := by
    rw [hu]; ring
  have hP3 : l ^ 2 * (P ^ 3 / 8) ≤ u ^ 2 / 8 := by
    have : l ^ 2 * (P ^ 3 / 8) = u * P ^ 2 / 8 := by rw [hu]; ring
    rw [this]
    have hP2 : P ^ 2 ≤ u := by nlinarith
    nlinarith
  have hpiinv8 : (1 : ℝ) / 40 ≤ 1 / (8 * Real.pi) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  have hpiinv2 : (1 : ℝ) / 7 ≤ 1 / (2 * Real.pi) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  have hr : 72 * u + 200 * Real.pi * (64 * u ^ 2) ≤ 73 * u := by
    have : 200 * Real.pi * (64 * u ^ 2) ≤ 200 * 3.15 * 64 * (u * (1 / 100000)) := by
      have := mul_le_mul_of_nonneg_left hu5 hu0
      nlinarith
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; linarith
  · rw [e3, e2]; nlinarith
  · rw [e2, e3, e4]
    have hsq : (4 * (72 * u + 200 * Real.pi * (64 * u ^ 2))) ^ 2 ≤ (4 * (73 * u)) ^ 2 := by
      have h0 : 0 ≤ 4 * (72 * u + 200 * Real.pi * (64 * u ^ 2)) := by positivity
      exact pow_le_pow_left₀ h0 (by linarith) 2
    have hA : 2 * Real.pi * (4 * (72 * u + 200 * Real.pi * (64 * u ^ 2))) ^ 2
        ≤ 2 * 3.15 * (4 * (73 * u)) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ 2 * Real.pi)
      nlinarith [sq_nonneg (4 * (73 * u))]
    have hB : 800 * Real.pi * (64 * u ^ 2) ≤ 800 * 3.15 * 64 * u ^ 2 := by nlinarith [sq_nonneg u]
    have hC : 32 * Real.pi * (64 * u ^ 2) ≤ 32 * 3.15 * 64 * u ^ 2 := by nlinarith [sq_nonneg u]
    have hsplit : l ^ 2 * (P + P ^ 3 / 8 + 32 * Real.pi * (8 * l * P) ^ 2)
        = u + l ^ 2 * (P ^ 3 / 8) + l ^ 2 * (32 * Real.pi * (8 * l * P) ^ 2) := by rw [hu]; ring
    rw [hsplit, e5]
    nlinarith [sq_nonneg u]

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.arith_bound
