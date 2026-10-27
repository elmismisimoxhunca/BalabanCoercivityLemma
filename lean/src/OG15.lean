import OG14

/-!
# OG15 -- the interface with the gluing lane (lane m2_onegap_20261015)
`regionChart_of_chartOn` : MR2's `ChartOn ell U η a' i w r` (the object `m2_glue2.chartOn_of_group` produces from a `GChart`) with `a' ≤ f M α` is a `RegionChart (Ball w r) ell M f α η i U`
(every bond / pair of bonds of the region is read at base points in `Ball w r`).  So `BallChartsAt` is implied by: for every admissible ball a `ChartOn` at level `j-1`, constant `12 M (C α₀)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace AdalyFormal.OneGap

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower pdist CubeBond HT)
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

theorem regionChart_of_chartOn {L : PeriodicLatticeExtent} {ell M f : ℕ} {α η a' : ℝ} {i : ℕ} {w : PeriodicLatticeSite L} {r : ℕ}
    {U : LinkCfg L} (hη : 0 < η) (hell : 0 < ell) (ha : a' ≤ (f : ℝ) * M * α)
    (h : AdalyFormal.M2Route.ChartOn ell U η a' i w r) :
    RegionChart (Ball w r) ell M f α η i U := by
  obtain ⟨g, A, hHT, hexp, h1, h2⟩ := h
  have hX : 0 ≤ ((ell : ℝ) ^ i * η)⁻¹ := by positivity
  refine ⟨g, A, fun e he => hexp e he.1, fun e _ => hHT e, fun e he => ?_, fun μ ν x hx hx' => ?_⟩
  · exact (h1 e he.1).trans_le (by
      rw [pow_one]
      exact mul_le_mul_of_nonneg_right ha hX)
  · refine (h2 μ ν x hx.1 hx'.1).trans_le ?_
    exact mul_le_mul_of_nonneg_right ha (by positivity)

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.regionChart_of_chartOn
