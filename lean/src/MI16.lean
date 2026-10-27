import MI15

/-!
# MI16 -- the gauge-fixing square: concrete first-order IMS (M1 lane E, 2026-10-13)

**`T_ims_concrete`**: on an admissible tower, with `IsUnit LP`, a two-sided inverse `Gi` of `Γ = X*X`, the `ψ`-weighted
hatted chain (`HatPack`) and the SHARP row bound `hγ : ‖ℓ^{strat} u‖ ≤ γ ‖X u‖`,
  `Σ_p ‖T(h_p A)‖² ≤ (1+ε) ‖T A‖² + 2 (1 + 1/ε) · CT · ‖ℓ^{−strat(tail)} A‖²`
with `CT = 3 KG + 5 (g2² 3KG F0² + g1² 3ℓ⁴KG F0⁴ + g1² q² 9aKG F0² + g1² 9aKG q² F0² + g1² 9aKG γ² F0²)`,
`F0 = g3 q γ`, `q = √(max a 1)`, `g1 = 4ℓ/cs`, `g2 = ℓ√(48/cs)`, `g3 = ℓ(√(12/cs) + 4δD/cs)` — free of `k`, the torus, the tower.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)

variable {L : PeriodicLatticeExtent}

theorem norm_sum5_sq {V : Type*} [NormedAddCommGroup V] (a b c d e : V) :
    ‖a + b + c + d + e‖ ^ 2 ≤ 5 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 + ‖e‖ ^ 2) := by
  have h := norm_add_le (a + b + c + d) e
  have h2 := norm_add_le (a + b + c) d
  have h3 := norm_add_le (a + b) c
  have h4 := norm_add_le a b
  have hs : ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by linarith
  have h0 := norm_nonneg (a + b + c + d + e)
  have hsq := pow_le_pow_left₀ h0 hs 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖a‖ - ‖d‖), sq_nonneg (‖a‖ - ‖e‖),
    sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖b‖ - ‖d‖), sq_nonneg (‖b‖ - ‖e‖), sq_nonneg (‖c‖ - ‖d‖),
    sq_nonneg (‖c‖ - ‖e‖), sq_nonneg (‖d‖ - ‖e‖)]

section T
variable {Lf : PeriodicLatticeExtent} {ell M R k κ c : ℕ} {S : Tower Lf}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c) {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
include hS hκ hM hell hR1 hR hc hW hWR

/-- the five-term commutator of `X`, summed over the partition. -/
theorem cX_sum (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (u : YP (geomOf ell k S)) :
    ∑ p, ‖siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (Xop (geomOf ell k S) U a u)
        - Xop (geomOf ell k S) U a (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) u)‖ ^ 2
      ≤ 5 * ((ell * Real.sqrt (48 / cs)) ^ 2 * (3 * KG ell M κ c * ‖Xop (geomOf ell k S) U a u‖ ^ 2)
        + (4 * ell / cs) ^ 2 * (3 * (ell : ℝ) ^ 4 * KG ell M κ c *
            ‖bondWt (sigG (geomOf ell k S)) (Dm (geomOf ell k S) U (Xop (geomOf ell k S) U a u))‖ ^ 2)
        + (4 * ell / cs) ^ 2 * (max a 1 * (9 * a * KG ell M κ c * ‖Xop (geomOf ell k S) U a u‖ ^ 2))
        + (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * (max a 1 * ‖Xop (geomOf ell k S) U a u‖ ^ 2))
        + (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ^ 2)) := by
  classical
  have hell0 : 0 < ell := by omega
  have hw : ∀ j, 0 ≤ wq (geomOf ell k S) a j := hw_of hS hW hell hR1 (by omega) hWR a hp.ha
  have hLG : ∀ s, (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) ∘L Dm (geomOf ell k S) U
      + ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) ∘L QpP (geomOf ell k S) U a) (LinvP (geomOf ell k S) U a s) = s := by
    intro s; rw [← LP_eq_L (geomOf ell k S) U a hw]; exact LP_LinvP (geomOf ell k S) U a hp.hu s
  have hGL : ∀ s, LinvP (geomOf ell k S) U a ((ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) ∘L Dm (geomOf ell k S) U
      + ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) ∘L QpP (geomOf ell k S) U a) s) = s := by
    intro s; rw [← LP_eq_L (geomOf ell k S) U a hw]; exact LinvP_LP (geomOf ell k S) U a hp.hu s
  set f := Xop (geomOf ell k S) U a u with hf
  set hS' := fun p => siteMul (AdalyFormal.M1.hpart ell M k κ c S p)
  -- the commutator identity, per p
  have hid := fun p => cX_eq (Dm (geomOf ell k S) U) (QpP (geomOf ell k S) U a) (LinvP (geomOf ell k S) U a) hLG hGL (hS' p) (bondMul (hbond ell M k κ c S p))
    (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p)) u
  have hXu : LinvP (geomOf ell k S) U a (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) u) = f := rfl
  -- g-bounds
  have g1b := fun y => g1 hS hW hell hR1 (by omega) hWR U a cs hp y
  have g2b := fun w => g2 hS hW hell hR1 (by omega) hWR U a cs hp w
  have hcs := hp.hcs
  -- per-p bound by five squares
  have hpp : ∀ p, ‖siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f
        - Xop (geomOf ell k S) U a (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) u)‖ ^ 2
      ≤ 5 * ((ell * Real.sqrt (48 / cs)) ^ 2 * ‖bondWt (sigG (geomOf ell k S)) (bondMul (hbond ell M k κ c S p) (Dm (geomOf ell k S) U f)
              - Dm (geomOf ell k S) U (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f))‖ ^ 2
          + (4 * ell / cs) ^ 2 * ‖siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S)) (siteMul (AdalyFormal.M1.hpart ell M k κ c S p)
              (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) (Dm (geomOf ell k S) U f))
              - ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) (bondMul (hbond ell M k κ c S p) (Dm (geomOf ell k S) U f)))‖ ^ 2
          + (4 * ell / cs) ^ 2 * (max a 1 * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) (QpP (geomOf ell k S) U a f)
              - QpP (geomOf ell k S) U a (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f))‖ ^ 2)
          + (4 * ell / cs) ^ 2 * ‖siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S)) (siteMul (AdalyFormal.M1.hpart ell M k κ c S p)
              (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (QpP (geomOf ell k S) U a f))
              - ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) (QpP (geomOf ell k S) U a f)))‖ ^ 2
          + (4 * ell / cs) ^ 2 * ‖siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S)) (siteMul (AdalyFormal.M1.hpart ell M k κ c S p)
              (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) u)
              - ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) u))‖ ^ 2) := by
    intro p
    have e : siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f - Xop (geomOf ell k S) U a (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) u)
        = (-(LinvP (geomOf ell k S) U a (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) (bondMul (hbond ell M k κ c S p) (Dm (geomOf ell k S) U f)
              - Dm (geomOf ell k S) U (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f)))))
          + (-(LinvP (geomOf ell k S) U a (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) (Dm (geomOf ell k S) U f))
              - ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) (bondMul (hbond ell M k κ c S p) (Dm (geomOf ell k S) U f)))))
          + (-(LinvP (geomOf ell k S) U a (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) (QpP (geomOf ell k S) U a f)
              - QpP (geomOf ell k S) U a (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f)))))
          + (-(LinvP (geomOf ell k S) U a (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (QpP (geomOf ell k S) U a f))
              - ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) (QpP (geomOf ell k S) U a f)))))
          + LinvP (geomOf ell k S) U a (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) u)
              - ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) u)) := by
      have h := hid p
      simp only [hS', hXu] at h
      rw [show Xop (geomOf ell k S) U a (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) u)
          = LinvP (geomOf ell k S) U a (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) u)) from rfl]
      rw [h]
      simp only [map_add]
      abel
    rw [e]
    refine (norm_sum5_sq _ _ _ _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    simp only [norm_neg]
    have b1 := g2b (bondMul (hbond ell M k κ c S p) (Dm (geomOf ell k S) U f) - Dm (geomOf ell k S) U (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f))
    have b2 := g1b (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) (Dm (geomOf ell k S) U f))
              - ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) (bondMul (hbond ell M k κ c S p) (Dm (geomOf ell k S) U f)))
    have b3a := g1b (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) (QpP (geomOf ell k S) U a f)
              - QpP (geomOf ell k S) U a (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f)))
    have b3b := Qs_row_bound hS hell U a hp.ha (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) (QpP (geomOf ell k S) U a f)
              - QpP (geomOf ell k S) U a (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f))
    have b4 := g1b (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (QpP (geomOf ell k S) U a f))
              - ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) (QpP (geomOf ell k S) U a f)))
    have b5 := g1b (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) u)
              - ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) u))
    have hsq : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → x ^ 2 ≤ y ^ 2 := fun h0 h => pow_le_pow_left₀ h0 h 2
    have c1 := hsq (norm_nonneg _) b1
    have c2 := hsq (norm_nonneg _) b2
    have c3 := hsq (norm_nonneg _) b3a
    have c4 := hsq (norm_nonneg _) b4
    have c5 := hsq (norm_nonneg _) b5
    rw [mul_pow] at c1 c2 c3 c4 c5
    have c3' : (4 * ell / cs) ^ 2 * ‖siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S)) (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a)
          (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) (QpP (geomOf ell k S) U a f) - QpP (geomOf ell k S) U a (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f)))‖ ^ 2
        ≤ (4 * ell / cs) ^ 2 * (max a 1 * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) (QpP (geomOf ell k S) U a f)
          - QpP (geomOf ell k S) U a (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f))‖ ^ 2) :=
      mul_le_mul_of_nonneg_left b3b (by positivity)
    linarith
  -- sum over p
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => hpp p)
  refine hsum.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have s1 := cD_sum hS hκ hM hell hR1 hR hc U f
  have s2 := cDs_sum hS hκ hM hell hR1 hR hc U (Dm (geomOf ell k S) U f)
  have s3 := cQ_sum hS hκ hM hell hR1 hR hc U a hp.ha f
  have s4 := cQs_sum hS hκ hM hell hR1 hR hc U a hp.ha (QpP (geomOf ell k S) U a f)
  have s5 := cQs_sum hS hκ hM hell hR1 hR hc U a hp.ha u
  have q4 := Q_row_bound hS hell U a hp.ha f
  have hK0 := KG_nonneg ell M κ c
  have hA : 0 ≤ (4 * (ell : ℝ) / cs) ^ 2 := sq_nonneg _
  have hB : 0 ≤ ((ell : ℝ) * Real.sqrt (48 / cs)) ^ 2 := sq_nonneg _
  have hm1 : 0 ≤ max a 1 := le_trans zero_le_one (le_max_right _ _)
  have t1 := mul_le_mul_of_nonneg_left s1 hB
  have t2 := mul_le_mul_of_nonneg_left s2 hA
  have t3 : (4 * (ell : ℝ) / cs) ^ 2 * (max a 1 * ∑ p, ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p)
        (QpP (geomOf ell k S) U a f) - QpP (geomOf ell k S) U a (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f))‖ ^ 2)
      ≤ (4 * ell / cs) ^ 2 * (max a 1 * (9 * a * KG ell M κ c * ‖f‖ ^ 2)) := by
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left s3 hm1) hA
  have t4 : (4 * (ell : ℝ) / cs) ^ 2 * ∑ p, ‖siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S)) (siteMul (AdalyFormal.M1.hpart ell M k κ c S p)
        (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (QpP (geomOf ell k S) U a f))
        - ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) (QpP (geomOf ell k S) U a f)))‖ ^ 2
      ≤ (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * (max a 1 * ‖f‖ ^ 2)) := by
    refine mul_le_mul_of_nonneg_left (s4.trans ?_) hA
    exact mul_le_mul_of_nonneg_left q4 (by have := hp.ha; positivity)
  have t5 := mul_le_mul_of_nonneg_left s5 hA
  linarith

/-- **the gauge-fixing square, concrete first-order IMS**. -/
theorem T_ims_concrete (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (Gi : YP (geomOf ell k S) →L[ℝ] YP (geomOf ell k S))
    (hG1 : ∀ u, (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) (Gi u) = u)
    (hG2 : ∀ u, Gi ((ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) u) = u)
    (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ : ∀ u, ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ≤ γ * ‖Xop (geomOf ell k S) U a u‖)
    (A : BondFnL2 Lf) (ε : ℝ) (hε : 0 < ε) :
    ∑ p, ‖Tfull (geomOf ell k S) U (bondMul (hbond ell M k κ c S p) A)‖ ^ 2
      ≤ (1 + ε) * ‖Tfull (geomOf ell k S) U A‖ ^ 2
        + 2 * (1 + 1 / ε) *
          ((5 * ((ell * Real.sqrt (48 / cs)) ^ 2 * (3 * KG ell M κ c)
              + (4 * ell / cs) ^ 2 * (3 * (ell : ℝ) ^ 4 * KG ell M κ c) *
                  ((ell * (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs)))
                    * Real.sqrt (max a 1) * γ) ^ 2
              + (4 * ell / cs) ^ 2 * (max a 1 * (9 * a * KG ell M κ c))
              + (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * max a 1)
              + (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * γ ^ 2)))
            * ((ell * (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs)))
                * Real.sqrt (max a 1) * γ) ^ 2
            + 3 * KG ell M κ c) * ‖bondWt (-sigG (geomOf ell k S)) A‖ ^ 2 := by
  classical
  have hell0 : 0 < ell := by omega
  have hP := properTower_geomOf hell0 hS
  have hw0 : ∀ j, 0 ≤ wq (geomOf ell k S) a j := hw_of hS hW hell hR1 (by omega) hWR a hp.ha
  have hwpos : ∀ j, 0 < wq (geomOf ell k S) a j := fun j => wq_pos hell hP a j hp.ha
  set X := Xop (geomOf ell k S) U a
  set Dst := ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U)
  set u := Gi (ContinuousLinearMap.adjoint X (Dst A)) with hu
  -- the decomposition
  have hRe := fun v => Rproj_eq_strat (geomOf ell k S) U a hwpos hp.hu Gi hG1 v
  have hdec : Dst A = Rproj (geomOf ell k S) U (Dst A) + X u := by rw [hRe (Dst A)]; abel
  have hRX : ∀ w, Rproj (geomOf ell k S) U (X w) = 0 := by
    intro w; rw [hRe (X w)]
    have : Gi (ContinuousLinearMap.adjoint X (X w)) = w := hG2 w
    rw [this, sub_self]
  have hT : ∀ B : BondFnL2 Lf, Tfull (geomOf ell k S) U B = Rproj (geomOf ell k S) U (Dst B) := by
    intro B
    show Rproj (geomOf ell k S) U (gradAdj U B) = Rproj (geomOf ell k S) U (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) B)
    rw [Dm_adjoint' hS hκ hM hell hR1 hR hc, ContinuousLinearMap.comp_apply, Rproj_mask_right]
  have hpart : ∑ p, ‖siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (Rproj (geomOf ell k S) U (Dst A))‖ ^ 2 = ‖Rproj (geomOf ell k S) U (Dst A)‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [siteMul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ (geomOf ell k S).Om0
    · rw [AdalyFormal.M1.sum_hpart_sq hc hκ hM hell0 hx, one_mul]
    · have : Rproj (geomOf ell k S) U (Dst A) x = 0 := by
        rw [← Rproj_mask_left, siteMask_off _ _ _ hx]
      rw [this, norm_zero]; simp
  have hmain := T_ims_upper Dst X (Rproj (geomOf ell k S) U) (Rproj_norm_le (geomOf ell k S) U) hRX
    (fun p => bondMul (hbond ell M k κ c S p)) (fun p => siteMul (AdalyFormal.M1.hpart ell M k κ c S p))
    (fun p => ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p)) A u hdec hpart ε hε
  simp only [← hT] at hmain
  refine hmain.trans ?_
  -- E2: the divergence commutator
  have hE2 : ∑ p, ‖Dst (bondMul (hbond ell M k κ c S p) A) - siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (Dst A)‖ ^ 2
      ≤ 3 * KG ell M κ c * ‖bondWt (-sigG (geomOf ell k S)) A‖ ^ 2 := by
    have := cDs_sum0 hS hκ hM hell hR1 hR hc U A
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun p _ => ?_))) this
    rw [← norm_neg, neg_sub]
  -- E1: the X commutator
  have hE1 := cX_sum hS hκ hM hell hR1 hR hc hW hWR U a cs hp u
  -- f bounds
  set f := X u with hf
  set q := Real.sqrt (max a 1)
  set g3c := (ell * (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs)))
  have hm1 : 0 ≤ max a 1 := le_trans zero_le_one (le_max_right _ _)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hg30 : 0 ≤ g3c := by
    have := dD_nonneg hS hW hell hR1 (by omega) hWR; have := hp.hcs; positivity
  have hDf : ‖bondWt (sigG (geomOf ell k S)) (Dm (geomOf ell k S) U f)‖ ≤ g3c * q * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ := by
    have h1 := g3 hS hW hell hR1 (by omega) hWR U a cs hp (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) u)
    have h2 := Qs_row_bound hS hell U a hp.ha u
    have h2' : ‖siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S)) (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) u)‖ ≤ q * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ := by
      rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg (ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u)), ← Real.sqrt_mul hm1]
      exact Real.sqrt_le_sqrt h2
    calc ‖bondWt (sigG (geomOf ell k S)) (Dm (geomOf ell k S) U f)‖ ≤ g3c * ‖siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S)) (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) u)‖ := h1
      _ ≤ g3c * (q * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖) := mul_le_mul_of_nonneg_left h2' hg30
      _ = _ := by ring
  have hfsq : ‖f‖ ^ 2 = ⟪bondWt (sigG (geomOf ell k S)) (Dm (geomOf ell k S) U f), bondWt (-sigG (geomOf ell k S)) A⟫ := by
    have h1 := f_sq_eq Dst X (Rproj (geomOf ell k S) U) (Rproj_symm (geomOf ell k S) U) hRX A u hdec
    rw [h1]
    show ⟪f, ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) A⟫ = _
    rw [ContinuousLinearMap.adjoint_inner_right, bondWt_symm, bondWt_neg_cancel]
  have hfA : ‖f‖ ≤ g3c * q * γ * ‖bondWt (-sigG (geomOf ell k S)) A‖ := by
    have h1 : ‖f‖ ^ 2 ≤ ‖bondWt (sigG (geomOf ell k S)) (Dm (geomOf ell k S) U f)‖ * ‖bondWt (-sigG (geomOf ell k S)) A‖ := by
      rw [hfsq]; exact real_inner_le_norm _ _
    have h2 : ‖bondWt (sigG (geomOf ell k S)) (Dm (geomOf ell k S) U f)‖ ≤ g3c * q * γ * ‖f‖ := by
      refine hDf.trans ?_
      have := hγ u
      calc g3c * q * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ≤ g3c * q * (γ * ‖f‖) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    by_cases h0 : ‖f‖ = 0
    · rw [h0]; have := norm_nonneg (bondWt (-sigG (geomOf ell k S)) A); positivity
    · have hp0 : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have : ‖f‖ ^ 2 ≤ g3c * q * γ * ‖f‖ * ‖bondWt (-sigG (geomOf ell k S)) A‖ :=
        h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
      nlinarith
  set F0 := g3c * q * γ
  set NA := ‖bondWt (-sigG (geomOf ell k S)) A‖
  have hF0 : 0 ≤ F0 := by positivity
  have hNA : 0 ≤ NA := norm_nonneg _
  have hfA2 : ‖f‖ ^ 2 ≤ F0 ^ 2 * NA ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hfA 2
  have hDf2 : ‖bondWt (sigG (geomOf ell k S)) (Dm (geomOf ell k S) U f)‖ ^ 2 ≤ F0 ^ 2 * (F0 ^ 2 * NA ^ 2) := by
    have h1 : ‖bondWt (sigG (geomOf ell k S)) (Dm (geomOf ell k S) U f)‖ ≤ F0 * ‖f‖ := by
      refine hDf.trans ?_
      have := hγ u
      calc g3c * q * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ≤ g3c * q * (γ * ‖f‖) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = F0 * ‖f‖ := by ring
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left hfA2 (by positivity))
  have hu2 : ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ^ 2 ≤ γ ^ 2 * (F0 ^ 2 * NA ^ 2) := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hγ u) 2
    rw [mul_pow] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hfA2 (sq_nonneg _))
  -- assemble E1
  have hK0 := KG_nonneg ell M κ c
  have hcs := hp.hcs
  have hE1' : ∑ p, ‖siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f - X (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) u)‖ ^ 2
      ≤ 5 * ((ell * Real.sqrt (48 / cs)) ^ 2 * (3 * KG ell M κ c)
              + (4 * ell / cs) ^ 2 * (3 * (ell : ℝ) ^ 4 * KG ell M κ c) * F0 ^ 2
              + (4 * ell / cs) ^ 2 * (max a 1 * (9 * a * KG ell M κ c))
              + (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * max a 1)
              + (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * γ ^ 2)) * (F0 ^ 2 * NA ^ 2) := by
    refine hE1.trans ?_
    have ha := hp.ha
    have e1 : (ell * Real.sqrt (48 / cs)) ^ 2 * (3 * KG ell M κ c * ‖f‖ ^ 2)
        ≤ (ell * Real.sqrt (48 / cs)) ^ 2 * (3 * KG ell M κ c) * (F0 ^ 2 * NA ^ 2) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hfA2 (by positivity)
    have e2 : (4 * ell / cs) ^ 2 * (3 * (ell : ℝ) ^ 4 * KG ell M κ c * ‖bondWt (sigG (geomOf ell k S)) (Dm (geomOf ell k S) U f)‖ ^ 2)
        ≤ (4 * ell / cs) ^ 2 * (3 * (ell : ℝ) ^ 4 * KG ell M κ c) * F0 ^ 2 * (F0 ^ 2 * NA ^ 2) := by
      have := mul_le_mul_of_nonneg_left hDf2 (show (0:ℝ) ≤ (4 * ell / cs) ^ 2 * (3 * (ell : ℝ) ^ 4 * KG ell M κ c) by positivity)
      linarith
    have e3 : (4 * ell / cs) ^ 2 * (max a 1 * (9 * a * KG ell M κ c * ‖f‖ ^ 2))
        ≤ (4 * ell / cs) ^ 2 * (max a 1 * (9 * a * KG ell M κ c)) * (F0 ^ 2 * NA ^ 2) := by
      have := mul_le_mul_of_nonneg_left hfA2 (show (0:ℝ) ≤ (4 * ell / cs) ^ 2 * (max a 1 * (9 * a * KG ell M κ c)) by positivity)
      linarith
    have e4 : (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * (max a 1 * ‖f‖ ^ 2))
        ≤ (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * max a 1) * (F0 ^ 2 * NA ^ 2) := by
      have := mul_le_mul_of_nonneg_left hfA2 (show (0:ℝ) ≤ (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * max a 1) by positivity)
      linarith
    have e5 : (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ^ 2)
        ≤ (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * γ ^ 2) * (F0 ^ 2 * NA ^ 2) := by
      have := mul_le_mul_of_nonneg_left hu2 (show (0:ℝ) ≤ (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c) by positivity)
      linarith
    nlinarith
  have hε0 : 0 ≤ 2 * (1 + 1 / ε) := by positivity
  have : ∑ p, ‖siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f - X (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) u)‖ ^ 2
      + ∑ p, ‖Dst (bondMul (hbond ell M k κ c S p) A) - siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (Dst A)‖ ^ 2
      ≤ ((5 * ((ell * Real.sqrt (48 / cs)) ^ 2 * (3 * KG ell M κ c)
              + (4 * ell / cs) ^ 2 * (3 * (ell : ℝ) ^ 4 * KG ell M κ c) * F0 ^ 2
              + (4 * ell / cs) ^ 2 * (max a 1 * (9 * a * KG ell M κ c))
              + (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * max a 1)
              + (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * γ ^ 2))) * F0 ^ 2 + 3 * KG ell M κ c) * NA ^ 2 := by
    nlinarith [hE1', hE2]
  have hmono := mul_le_mul_of_nonneg_left this hε0
  linarith

end T

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.norm_sum5_sq
#print axioms AdalyFormal.M1IMS.cX_sum
#print axioms AdalyFormal.M1IMS.T_ims_concrete
