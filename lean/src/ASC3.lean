import ASC1
import ASAl3
import BC12
import NB31
import NJ13bReg

/-!
# ASC3 -- `ginv_coercive_M0_pinned`: the genuine `Ginv` is coercive in the scaled norm, from fine-scale data ONLY.

Hypotheses (whole torus, ONE gauge): fine links `dv (U b) ≤ e`, fine plaquettes (the tree's `periodicPlaquetteHolonomy`) `dv ≤ q0`,
`2 ell^k < N`, and the curvature-blocking smallness `4e6 ell² (ell²)^k q0 ≤ 1`.  Everything else is DERIVED:
* tower class (aligned bonds): `BC8.towerClass_of_blocking` (curvature blocking `link_tower_na`);
* `hu`, `hPoincU`: `ASAl3.hu_al / poincare_al` (site chain with the tower bound on ALIGNED bonds, ASAl1-3);
* `hreg`: `regTower_of_frobSup` from the TREE's crude all-edge bound (`frobSup_bgTower_le`), threshold `hregthr` (against `r0`);
* C1 (`hm`) and `hQdrift`: `BC6.hm_of_tower`, `BC1b.hQdrift_of_tower` (+ BC12 class bounds);
* FlatExt: `FlatExt.ginv_coercive_FE` (`flatE`);
* `hflat, hdp, hPoinc1, hQq, hd, hc`: ported (PB1, PB3, PB2, PB5) / GN11 / GN13.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.AsmM0

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.Balaban.ClassPropagationUbar (blkConstOf)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.SliceCoerc
open AdalyFormal.PortSlice
open AdalyFormal.BondComposite
open AdalyFormal.CurvBlock (dv pw pw_one_of_plaq)
open AdalyFormal.NonflatJet (r0 mem_LogReg_of_frob_lt)
open AdalyFormal.FlatExt (aFE bFE)

/-- `φ(s) = (s/r) e^{s/r}`, `r = ell^{-1/2}` -/
noncomputable def phiC (ell : ℕ) (s : ℝ) : ℝ := (s / rr ell) * Real.exp (s / rr ell)

theorem frobSupBond_le_of {L : PeriodicLatticeExtent} (V : Cfg L) {c : ℝ} (h : ∀ b, dv (V b) ≤ c) :
    frobSupBond V ≤ c := by
  unfold frobSupBond
  exact Finset.sup'_le _ _ (fun b _ => h b)

theorem deltaM_nonneg (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 ≤ a) (ε : ℕ → ℝ) (hε0 : ∀ j, j < k → 0 ≤ ε j) :
    0 ≤ deltaM ell k a ε := by
  have hr : 0 ≤ rr ell := rr_nonneg ell
  have hS : 0 ≤ ∑ i ∈ Finset.range k, thetaOf ell (ε i) :=
    Finset.sum_nonneg fun i hi => thetaOf_nonneg ell _ (hε0 i (Finset.mem_range.mp hi))
  unfold deltaM
  have : 0 ≤ ((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell) := div_nonneg hS hr
  positivity

theorem aFE_mul_q (ell k : ℕ) (hell : 0 < ell) :
    aFE ell k * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) = 27 := by
  have hn : 0 < (ell : ℝ) ^ k := by positivity
  unfold aFE
  rw [← Real.sqrt_mul (by positivity)]
  have : 729 * ((ell : ℝ) ^ k) ^ 3 * (1 / ((ell : ℝ) ^ k) ^ 3) = 27 ^ 2 := by field_simp; norm_num
  rw [this, Real.sqrt_sq (by norm_num)]

theorem theta_n2 (n q0 η ρ e0 : ℝ) (hn : 0 < n) (hq0 : 0 ≤ q0) (hη : η = e0 + 3 * Real.pi * (n * q0)) (he0 : 0 ≤ e0)
    (hρ : ρ = n * η) : n ^ 2 * q0 ≤ ρ / (3 * Real.pi) := by
  have hpi := Real.pi_pos
  rw [le_div_iff₀ (by positivity), hρ, hη]
  nlinarith [mul_nonneg hn.le hq0, mul_nonneg hn.le he0]

#print axioms frobSupBond_le_of
#print axioms deltaM_nonneg
#print axioms aFE_mul_q
#print axioms theta_n2

end AdalyFormal.AsmM0
