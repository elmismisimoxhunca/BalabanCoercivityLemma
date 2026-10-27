import DLR40

/-!
# DL41 -- the bond-level scaled inputs at M0 and **`G_CT_M0`** (the concrete k-uniform Combes–Thomas bound for `G`)

* `m0_hC'`, `m0_hK'`, `m0_hdK'`, `m0_hν'`, `m0_hdν'`, `m0_hB'` : the scaled bond commutators are bounded by the k-free
  parameters `δCS, κS, δKS, νS, δνS, δBS` (DL38) — uses `n²q0 ≤ ρ/(3π)`, `Σθ(ε_i) ≤ 3600ℓρ`, `Rfoot ≤ 5n`.
* `GinvFull_isUnit`.
* **`G_CT_M0`** : `‖e^{φ} G e^{−φ} g‖ ≤ 2n²K̂‖g‖` for every weight with one-step Lipschitz `θ/n`, under `CondM0 ℓ a ρ θ` and
  `4·EGM0 ℓ a ρ θ ≤ 1/K̂` — conditions in `(ℓ, a, t, ρ, θ)` only.
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

theorem m0_hC' (θ : ℝ) (hθ : 0 ≤ θ) :
    (ell : ℝ) ^ k * (6 * (Real.exp (θ / (ell : ℝ) ^ k) - 1)) ≤ δCS θ := by
  have h := n_expm1_le _ θ (m0_n_ge_one ell k Lu U a t e q0 R) hθ
  unfold δCS
  nlinarith [h]

theorem m0_hK' : ((ell : ℝ) ^ k) ^ 2 * (6 * q0) ≤ κS (rhoM0 ell k e q0) := by
  have h := m0_nq0 ell k Lu U a t e q0 R
  unfold κS; nlinarith [h]

theorem m0_hdK' (θ : ℝ) (hθ : 0 ≤ θ) :
    ((ell : ℝ) ^ k) ^ 2 * (6 * q0 * (Real.exp (2 * (θ / (ell : ℝ) ^ k)) - 1)) ≤ δKS (rhoM0 ell k e q0) θ := by
  have h := m0_nq0 ell k Lu U a t e q0 R
  have hn1 := m0_n_ge_one ell k Lu U a t e q0 R
  have he : Real.exp (2 * (θ / (ell : ℝ) ^ k)) - 1 ≤ Real.exp (2 * θ) - 1 := by
    have := n_expm1_le' ((ell : ℝ) ^ k) θ 2 (by norm_num) hn1 hθ
    rwa [mul_div_assoc] at this
  have he0 : 0 ≤ Real.exp (2 * (θ / (ell : ℝ) ^ k)) - 1 := by
    have hn0 : (0 : ℝ) < (ell : ℝ) ^ k := by linarith
    have : 0 ≤ 2 * (θ / (ell : ℝ) ^ k) := by positivity
    linarith [Real.add_one_le_exp (2 * (θ / (ell : ℝ) ^ k))]
  have hq0 := R.hq0
  unfold δKS κS
  calc ((ell : ℝ) ^ k) ^ 2 * (6 * q0 * (Real.exp (2 * (θ / (ell : ℝ) ^ k)) - 1))
      = 6 * (((ell : ℝ) ^ k) ^ 2 * q0) * (Real.exp (2 * (θ / (ell : ℝ) ^ k)) - 1) := by ring
    _ ≤ 6 * (rhoM0 ell k e q0 / (3 * Real.pi)) * (Real.exp (2 * θ) - 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h (by norm_num)) he he0
        have := m0_rho_nonneg ell k Lu U a t e q0 R; have := Real.pi_pos; positivity

theorem m0_hν' : ((ell : ℝ) ^ k) ^ 2 * (816 * (q0 / (4 * Real.sqrt 2))) ≤ νS (rhoM0 ell k e q0) := by
  have h := m0_nq0 ell k Lu U a t e q0 R
  unfold νS
  have hs : 0 < 4 * Real.sqrt 2 := by positivity
  calc ((ell : ℝ) ^ k) ^ 2 * (816 * (q0 / (4 * Real.sqrt 2)))
      = 816 * ((((ell : ℝ) ^ k) ^ 2 * q0) / (4 * Real.sqrt 2)) := by ring
    _ ≤ 816 * (rhoM0 ell k e q0 / (3 * Real.pi) / (4 * Real.sqrt 2)) := by
        gcongr

theorem m0_hdν' (θ : ℝ) (hθ : 0 ≤ θ) :
    ((ell : ℝ) ^ k) ^ 2 * (816 * (q0 / (4 * Real.sqrt 2)) * (Real.exp (2 * (θ / (ell : ℝ) ^ k)) - 1))
      ≤ δνS (rhoM0 ell k e q0) θ := by
  have h := m0_hν' ell k Lu U a t e q0 R
  have hn1 := m0_n_ge_one ell k Lu U a t e q0 R
  have he : Real.exp (2 * (θ / (ell : ℝ) ^ k)) - 1 ≤ Real.exp (2 * θ) - 1 := by
    have := n_expm1_le' ((ell : ℝ) ^ k) θ 2 (by norm_num) hn1 hθ
    rwa [mul_div_assoc] at this
  have he0 : 0 ≤ Real.exp (2 * (θ / (ell : ℝ) ^ k)) - 1 := by
    have hn0 : (0 : ℝ) < (ell : ℝ) ^ k := by linarith
    have : 0 ≤ 2 * (θ / (ell : ℝ) ^ k) := by positivity
    linarith [Real.add_one_le_exp (2 * (θ / (ell : ℝ) ^ k))]
  unfold δνS
  calc _ = (((ell : ℝ) ^ k) ^ 2 * (816 * (q0 / (4 * Real.sqrt 2)))) * (Real.exp (2 * (θ / (ell : ℝ) ^ k)) - 1) := by ring
    _ ≤ νS (rhoM0 ell k e q0) * (Real.exp (2 * θ) - 1) :=
        mul_le_mul h he he0 (by unfold νS; have := m0_rho_nonneg ell k Lu U a t e q0 R; have := Real.pi_pos; positivity)

theorem m0_hB' (θ : ℝ) (hθ : 0 ≤ θ) :
    Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3)
      * (qbM ell k (epsCl ell e q0) * (Real.exp (Rfoot ell k * (θ / (ell : ℝ) ^ k)) - 1) * multB ell k)
      ≤ δBS ell a (rhoM0 ell k e q0) θ := by
  have hell := R.hell
  have hell0 : 0 < ell := by omega
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  have hrr : 0 < rr ell := Real.sqrt_pos.mpr (by positivity)
  have hrr2 : rr ell ^ 2 = 1 / (ell : ℝ) := AdalyFormal.BondComposite.rr_sq ell hell0
  -- (1) the scale factor is √a
  have hsc : Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) * (((ell : ℝ) ^ k)⁻¹ * rr ell ^ k) = Real.sqrt a := by
    have h0 : 0 ≤ Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) * (((ell : ℝ) ^ k)⁻¹ * rr ell ^ k) := by
      have := rr ell; positivity
    have hrk : (rr ell ^ k) ^ 2 = 1 / (ell : ℝ) ^ k := by
      rw [← pow_mul, mul_comm, pow_mul, hrr2, div_pow, one_pow]
    rw [← Real.sqrt_sq h0]
    congr 1
    rw [mul_pow, Real.sq_sqrt (by have := R.ha; positivity), mul_pow, hrk]
    field_simp
  -- (2) the exponential
  have hS := m0_S ell k Lu U a t e q0 R
  have hexp : Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (epsCl ell e q0 i)) / rr ell)
      ≤ Real.exp (3600 * (ell : ℝ) * rhoM0 ell k e q0 / rr ell) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hS hrr.le)
  -- (3) the footprint
  have hRf := Rfoot_le ell hell k
  have hRθ : Real.exp (Rfoot ell k * (θ / (ell : ℝ) ^ k)) - 1 ≤ Real.exp (5 * θ) - 1 := by
    have : (Rfoot ell k : ℝ) * (θ / (ell : ℝ) ^ k) ≤ 5 * θ := by
      have h1 : (Rfoot ell k : ℝ) ≤ 5 * (ell : ℝ) ^ k := by exact_mod_cast hRf
      calc (Rfoot ell k : ℝ) * (θ / (ell : ℝ) ^ k) ≤ 5 * (ell : ℝ) ^ k * (θ / (ell : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = 5 * θ := by field_simp
    linarith [Real.exp_le_exp.mpr this]
  have hRθ0 : 0 ≤ Real.exp (Rfoot ell k * (θ / (ell : ℝ) ^ k)) - 1 := by
    have : 0 ≤ (Rfoot ell k : ℝ) * (θ / (ell : ℝ) ^ k) := by positivity
    linarith [Real.add_one_le_exp ((Rfoot ell k : ℝ) * (θ / (ell : ℝ) ^ k))]
  have hmult : multB ell k ≤ Real.sqrt 648 := by
    unfold multB
    apply Real.sqrt_le_sqrt
    have h1 : Rfoot ell k / ell ^ k ≤ 5 := Nat.div_le_of_le_mul (by linarith [hRf])
    have h2 : 3 * (Rfoot ell k / ell ^ k + 1) ^ 3 ≤ 648 := by
      have : (Rfoot ell k / ell ^ k + 1) ^ 3 ≤ 6 ^ 3 := Nat.pow_le_pow_left (by omega) 3
      omega
    exact_mod_cast h2
  have hm0 : 0 ≤ multB ell k := Real.sqrt_nonneg _
  unfold qbM δBS
  calc Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3)
        * (((ell : ℝ) ^ k)⁻¹ * (rr ell ^ k * Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (epsCl ell e q0 i)) / rr ell))
          * (Real.exp (Rfoot ell k * (θ / (ell : ℝ) ^ k)) - 1) * multB ell k)
      = (Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) * (((ell : ℝ) ^ k)⁻¹ * rr ell ^ k))
          * Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (epsCl ell e q0 i)) / rr ell)
          * (Real.exp (Rfoot ell k * (θ / (ell : ℝ) ^ k)) - 1) * multB ell k := by ring
    _ = Real.sqrt a * Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (epsCl ell e q0 i)) / rr ell)
          * (Real.exp (Rfoot ell k * (θ / (ell : ℝ) ^ k)) - 1) * multB ell k := by rw [hsc]
    _ ≤ Real.sqrt a * Real.exp (3600 * (ell : ℝ) * rhoM0 ell k e q0 / rr ell) * (Real.exp (5 * θ) - 1)
          * Real.sqrt 648 := by
        have : 0 ≤ Real.exp (5 * θ) - 1 := by linarith [Real.add_one_le_exp (5 * θ)]
        gcongr

end

#print axioms m0_hC'
#print axioms m0_hK'
#print axioms m0_hdK'
#print axioms m0_hν'
#print axioms m0_hdν'
#print axioms m0_hB'

end AdalyFormal.DLayer
