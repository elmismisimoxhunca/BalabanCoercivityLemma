import GW5

/-!
# GW6 -- W5 (`GenP.WellDef`) at `U` from `M1Regular` (M1 gauge lane, 2026-10-14)

`delta_small` / `qsNum_small` : `3 δ*² CEp < 1` from explicit bounds on `x = S*/rr` (k-free: `S* = SstarM` is linear in `α₀`).
`wellDef_M1` : `GenP.WellDef (gparams … U …)` from `w4_M1` (via `U^g`), `Q*` injective (`qs_injective_M1`), and the three
retained inputs: `hD2` (at `U`), `hb` (at `U`), `PatchCoercive` (at `U`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1GaugeW4

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar delStar massComm_M1 qs_injective_M1 rho1_nonneg)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneG (gparams GenP.WellDef)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.M1 (M1Bounds)
open AdalyFormal.W6 (CEp)

theorem CEp_nonneg : 0 ≤ CEp := by
  unfold AdalyFormal.W6.CEp AdalyFormal.W6.CE; norm_num

theorem delta_small (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hx2 : 6 * Real.sqrt CEp * x ≤ 1) :
    3 * (x * Real.exp x) ^ 2 * CEp < 1 := by
  have he : Real.exp x ≤ 3 := by
    have := Real.exp_le_exp.mpr hx1
    have h2 := Real.exp_one_lt_d9
    linarith
  have h1 : x * Real.exp x ≤ 3 * x := by nlinarith
  have hc := CEp_nonneg
  have hsq : Real.sqrt CEp ^ 2 = CEp := Real.sq_sqrt hc
  have h3 : (x * Real.exp x) ^ 2 ≤ (3 * x) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) h1
  have h4 : (6 * Real.sqrt CEp * x) ^ 2 ≤ 1 := by
    have : 0 ≤ 6 * Real.sqrt CEp * x := by positivity
    nlinarith
  have h5 : (6 * Real.sqrt CEp * x) ^ 2 = 36 * CEp * x ^ 2 := by rw [mul_pow, mul_pow, hsq]; ring
  rw [h5] at h4
  have h6 : 3 * (x * Real.exp x) ^ 2 * CEp ≤ 3 * (3 * x) ^ 2 * CEp := by
    apply mul_le_mul_of_nonneg_right _ hc
    linarith
  nlinarith

/-- explicit `k`-free smallness of `S*/rr` (linear in `α₀`). -/
structure QsNum (ell f M : ℕ) (α₀ : ℝ) : Prop where
  h1 : SstarM ell f M α₀ / AdalyFormal.BondComposite.rr ell ≤ 1
  h2 : 6 * Real.sqrt CEp * (SstarM ell f M α₀ / AdalyFormal.BondComposite.rr ell) ≤ 1

theorem qsNum_small (ell f M : ℕ) (α₀ : ℝ) (hα0 : 0 ≤ α₀) (hell : 0 < ell) (h : QsNum ell f M α₀) :
    3 * delStar ell (SstarM ell f M α₀) ^ 2 * CEp < 1 := by
  have hr := AdalyFormal.W6.rr_pos hell
  have hS : 0 ≤ SstarM ell f M α₀ := by
    have := rho1_nonneg f M α₀ hα0
    have := Real.pi_pos
    unfold AdalyFormal.TowerLoc.SstarM AdalyFormal.TowerLoc.Ctheta
    positivity
  have := delta_small (SstarM ell f M α₀ / AdalyFormal.BondComposite.rr ell) (div_nonneg hS hr.le) h.h1 h.h2
  exact this

end AdalyFormal.M1GaugeW4

#print axioms AdalyFormal.M1GaugeW4.delta_small
#print axioms AdalyFormal.M1GaugeW4.qsNum_small
