import PSC7
import PSC1

/-!
# SC8 -- the SCALED form of the explicit bound: `ell^{2k} ⟨x, G₁⁻¹ x⟩ ≥ hfun(a) ‖x‖²` with `hfun` independent of
`k` and of the volume, and the wiring into the `hunit` chain.  Standard axioms only.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.FlatCoercivity

namespace AdalyFormal.ScaledCoercivity

section Scaled
variable {n : ℕ}

/-- the `k`-independent scaled coercivity function -/
noncomputable def hfun (a : ℝ) : ℝ :=
  muStar a / (1 + muStar a) * ((2 / Real.pi) ^ 8 * min (a / 4) (4 / (4 + (2 / Real.pi) ^ 8)))

theorem scaled_cell (hn : 0 < n) (a : ℝ) (ha : 0 ≤ a) :
    (n : ℝ) ^ 2 * cellC n (a * (n : ℝ) / (n : ℝ) ^ 8) = hfun a := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcn2 : cn n ^ 2 * (n : ℝ) ^ 3 = 1 := cn_sq hn
  set γ8 : ℝ := (2 / Real.pi) ^ 8 with hγ8
  have hγpos : 0 < γ8 := by have := Real.pi_pos; positivity
  have hk : a * (n : ℝ) / (n : ℝ) ^ 8 * (n : ℝ) ^ 7 = a := by field_simp
  have hA2 : ((n : ℝ) * ‖epsV n‖) ^ 2 = (n : ℝ) ^ 5 := by
    rw [mul_pow, norm_epsV_sq hn]; ring
  have hq02 : (cn n * (2 * (n : ℝ) / Real.pi) ^ 4) ^ 2 = γ8 * (n : ℝ) ^ 5 := by
    rw [mul_pow, ← pow_mul]
    have : (2 * (n : ℝ) / Real.pi) ^ (4 * 2) = γ8 * (n : ℝ) ^ 8 := by
      rw [hγ8, show 2 * (n : ℝ) / Real.pi = (2 / Real.pi) * n by ring, mul_pow]
    rw [this]
    calc cn n ^ 2 * (γ8 * (n : ℝ) ^ 8) = (cn n ^ 2 * (n : ℝ) ^ 3) * (γ8 * (n : ℝ) ^ 5) := by ring
      _ = _ := by rw [hcn2, one_mul]
  have hlam : lamN (a * (n : ℝ) / (n : ℝ) ^ 8) (4 / (n : ℝ) ^ 2) ((n : ℝ) * ‖epsV n‖)
      (cn n * (2 * (n : ℝ) / Real.pi) ^ 4) = γ8 / (n : ℝ) ^ 2 * min (a / 4) (4 / (4 + γ8)) := by
    unfold lamN
    rw [hq02, hA2]
    have e1 : a * (n : ℝ) / (n : ℝ) ^ 8 * (γ8 * (n : ℝ) ^ 5) / 4 = γ8 / (n : ℝ) ^ 2 * (a / 4) := by
      field_simp
    have e2 : 4 / (n : ℝ) ^ 2 * (γ8 * (n : ℝ) ^ 5) / (4 * (n : ℝ) ^ 5 + γ8 * (n : ℝ) ^ 5)
        = γ8 / (n : ℝ) ^ 2 * (4 / (4 + γ8)) := by
      have h5 : (0 : ℝ) < (n : ℝ) ^ 5 := by positivity
      field_simp
    rw [e1, e2, ← mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ γ8 / (n : ℝ) ^ 2)]
  unfold cellC
  rw [hk, hlam]
  unfold hfun
  rw [← hγ8]
  field_simp

end Scaled

section Genuine
variable (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (Lam : Set (PeriodicLatticeSite Lu))

theorem hfun_pos (ha : 0 < a) : 0 < hfun a := by
  unfold hfun muStar
  have hpi := Real.pi_pos
  have := cA_pos
  have h1 : 0 < cA * a / (3 * Real.pi ^ 2 + a + a * (3 * Real.pi ^ 2) / 4) := by positivity
  have h2 : 0 < (2 / Real.pi) ^ 8 * min (a / 4) (4 / (4 + (2 / Real.pi) ^ 8)) := by
    apply mul_pos (by positivity)
    exact lt_min (by positivity) (by positivity)
  have h3 : 0 < 1 + cA * a / (3 * Real.pi ^ 2 + a + a * (3 * Real.pi ^ 2) / 4) := by linarith
  exact mul_pos (div_pos h1 h3) h2

/-- **THE SCALED k-UNIFORM COERCIVITY OF THE GENUINE FLAT `G₁⁻¹`** (explicit constant). -/
theorem scaled_G1inv (ha : 0 < a) (x : ↥(bondSupp (PK ell k Lu hell a Lam).G)) :
    hfun a * ‖x‖ ^ 2 ≤ (ell : ℝ) ^ (2 * k) * inner ℝ x ((PK ell k Lu hell a Lam).G1inv x) := by
  have hn : 0 < ell ^ k := pow_pos hell k
  have h := G1inv_coercive_explicit ell k hell a ha Lu Lam x
  have hs := scaled_cell hn a ha.le
  have hp : (((ell ^ k : ℕ) : ℝ)) ^ 2 = (ell : ℝ) ^ (2 * k) := by
    push_cast; rw [pow_mul', ← pow_mul]
  rw [← hs, hp] at *
  have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (ell : ℝ) ^ (2 * k))
  calc (ell : ℝ) ^ (2 * k) * cellC (ell ^ k) (a * ((ell ^ k : ℕ) : ℝ) / ((ell ^ k : ℕ) : ℝ) ^ 8) * ‖x‖ ^ 2
      = (ell : ℝ) ^ (2 * k) * (cellC (ell ^ k) (a * ((ell ^ k : ℕ) : ℝ) / ((ell ^ k : ℕ) : ℝ) ^ 8) * ‖x‖ ^ 2) := by ring
    _ ≤ _ := this

/-- the scaled constant feeds `hunit`: `IsUnit(Q G₁ Q*)` at flat `U`, any `k`, with the explicit `hfun a / ell^{2k}`. -/
theorem hunit_scaled_flat (ha : 0 < a) (hN : ∀ μ, 1 ≤ Lu μ) :
    IsUnit (((PK ell k Lu hell a Lam).Qin.comp (PK ell k Lu hell a Lam).G1in).comp
      (ContinuousLinearMap.adjoint (PK ell k Lu hell a Lam).Qin)) := by
  have hp : (0 : ℝ) < (ell : ℝ) ^ (2 * k) := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  refine hunit_of_coercive ell k Lu hell a Lam hN (hfun a / (ell : ℝ) ^ (2 * k))
    (div_pos (hfun_pos a ha) hp) (fun x => ?_)
  have := scaled_G1inv ell k hell a Lu Lam ha x
  rw [div_mul_eq_mul_div, div_le_iff₀ hp]
  simpa [mul_comm] using this

/-- compatibility with the plain-norm ceiling: the scaled constant never exceeds `a` (`flat_scaled_ceiling`):
so `hfun a ≤ a` for every `a > 0`. -/
theorem hfun_le (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (Lam : Set (PeriodicLatticeSite Lu)) (ha : 0 < a) (hN : ∀ μ, 1 ≤ Lu μ) : hfun a ≤ a := by
  have hn : 0 < ell := hell
  have h := fun x => scaled_G1inv ell k hell a Lu Lam ha x
  exact flat_scaled_ceiling ell k Lu hell a Lam hN (hfun a) h

end Genuine

#print axioms scaled_cell
#print axioms scaled_G1inv
#print axioms hunit_scaled_flat
#print axioms hfun_le

end AdalyFormal.ScaledCoercivity
