import DLR38

/-!
# DL39 -- **CONCRETE, k-UNIFORM COMBES–THOMAS BOUND FOR THE GENUINE `G` AT M0** (dispatched step (1))

For `U` in the M0 regime (`M0RegimeR` + `KUSmall`), `n = ℓ^k`, `ρ = rhoM0 ℓ k e q0`, any weight `φ` with one-fine-step
Lipschitz constant `θ/n` (decay length `n/θ` fine steps = `1/θ` top-level blocks), and the k-FREE conditions `CondM0 ℓ a ρ θ`
plus `4·EGM0 ℓ a ρ θ ≤ 1/K̂` (`K̂ = KhatM0 ℓ a t ρ`):
  **`G_CT_M0`** : `‖e^{φ} G e^{−φ} g‖ ≤ 2 n² K̂ ‖g‖`,  `G = (G⁻¹)⁻¹` the genuine operator on all fine bonds (`GinvFull`, DL32).
`n²K̂` is the (sharp) unweighted size of `G` (`G⁻¹ ≥ 1/(n²K̂)`); the threshold involves only `(ℓ, a, t, ρ, θ)`.
Proof: the abstract chain DL9–DL17 applied to the SCALED genuine instance (DL34), whose structure constants are bounded by the
k-free parameters of DL38 (`m0_*` facts of DL37), and the identity `G⁻¹' = n² G⁻¹` (DL35).
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 100000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU PlaqFnL2)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.AsmM0 (M0RegimeR rhoM0 Mc KhatM0)
open AdalyFormal.BondComposite (rr TowerClass thetaOf)

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
  (R : M0RegimeR ell k Lu U a t e q0)
include R

theorem m0_n_ge_one : (1 : ℝ) ≤ (ell : ℝ) ^ k := by
  have : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by have := R.hell; omega)
  exact one_le_pow₀ this

theorem m0_mTop_pos : 0 < mTop ell k a := by
  unfold mTop
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast R.hell
  have h1 : 0 < 1 - 1 / ((ell : ℝ) * ell) := by
    rw [sub_pos, div_lt_one (by positivity)]; nlinarith
  have h2 : 0 < ajSeq a ell k := lt_of_lt_of_le (by have := R.ha; positivity) (ajSeq_ge ell R.hell a R.ha k)
  have : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  positivity

/-- `√m_k · n · n^{-3/2} = √a_k ≤ √a` -/
theorem m0_sqm_le : Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k * Real.sqrt ((1 / (ell : ℝ) ^ 3) ^ k) ≤ Real.sqrt a := by
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by have := R.hell; positivity
  have e1 : (1 / (ell : ℝ) ^ 3) ^ k = 1 / ((ell : ℝ) ^ k) ^ 3 := by
    rw [div_pow, one_pow, ← pow_mul, ← pow_mul, mul_comm]
  rw [e1]
  set X := Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hm0 : 0 ≤ mTop ell k a := (m0_mTop_pos ell k Lu U a t e q0 R).le
  have hX2 : X ^ 2 = ajSeq a ell k := by
    rw [hX, mul_pow, mul_pow, Real.sq_sqrt hm0, Real.sq_sqrt (by positivity)]
    unfold mTop
    field_simp
  rw [← Real.sqrt_sq hX0, hX2]
  exact Real.sqrt_le_sqrt (ajSeq_le ell R.hell a R.ha k)

end

end AdalyFormal.DLayer
