import SC6
import PSC8
import SC10d
import PGFC22

/-!
# SC10e -- v2: EXPLICIT scaled coercivity of the genuine flat `G₁⁻¹` with `hfun2`.

`scaled_G1inv2`:  for every `ell k a>0`, every unit torus `Lu` and every `Λ`,
    `ell^{2k} ⟨x, G₁⁻¹ x⟩ ≥ hfun2(a) ‖x‖²`, with `hfun2` independent of `k` and of the volume.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
open scoped ComplexInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.FlatCoercivity

namespace AdalyFormal.ScaledCoercivity

/-- **EXPLICIT volume-independent coercivity of the genuine flat `G₁⁻¹`**. -/
theorem G1inv_coercive_explicit2 (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 < a)
    (Lu : PeriodicLatticeExtent) (Lam : Set (PeriodicLatticeSite Lu))
    (x : ↥(bondSupp (PK ell k Lu hell a Lam).G)) :
    hfun2 a / ((ell ^ k : ℕ) : ℝ) ^ 2 * ‖x‖ ^ 2
      ≤ inner ℝ x ((PK ell k Lu hell a Lam).G1inv x) := by
  have hn : 0 < ell ^ k := pow_pos hell k
  have hnR : (0 : ℝ) < ((ell ^ k : ℕ) : ℝ) := by exact_mod_cast hn
  set κ : ℝ := a * ((ell ^ k : ℕ) : ℝ) / ((ell ^ k : ℕ) : ℝ) ^ 8 with hκ
  have hκpos : 0 < κ := by positivity
  have hFS : (PK ell k Lu hell a Lam).FullSupp := PK_fullSupp ell k Lu hell a Lam
  have hform := Gen.G1inv_form (PK ell k Lu hell a Lam) hFS (PK_Om0_univ ell k Lu hell a Lam) rfl x
  rw [hform]
  set A : BondFnL2 (scaleUp ell k Lu) := iE (PK ell k Lu hell a Lam).G x with hA
  have hdvd : ∀ μ, ell ^ k ∣ scaleUp ell k Lu μ + 1 := scaleUp_tiling ell k Lu hell
  have hx : ‖x‖ = ‖A‖ := rfl
  have h1 := curl_energy A
  have h2 := R_lower ell k Lu hell A
  have h3 := Qnorm_eq ell k Lu hell a Lam x
  rw [← hA] at h3
  have h4 := Qsum hn hdvd (WithLp.ofLp A)
  have h5 := norm_bond A
  have hT : ‖Tfull (PK ell k Lu hell a Lam).G (PK ell k Lu hell a Lam).U A‖
      = ‖Rproj (geomOf ell k (fullTower ell k Lu)) (flatCfg : PeriodicLinkConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (gradAdj flatCfg A)‖ := rfl
  show hfun2 a / ((ell ^ k : ℕ) : ℝ) ^ 2 * ‖x‖ ^ 2 ≤ ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) A‖ ^ 2 +
      ‖Tfull (PK ell k Lu hell a Lam).G (PK ell k Lu hell a Lam).U A‖ ^ 2 +
      (PK ell k Lu hell a Lam).a * ((PK ell k Lu hell a Lam).ell : ℝ) ^ (PK ell k Lu hell a Lam).k * ‖(PK ell k Lu hell a Lam).data.Q x‖ ^ 2
  have e : (PK ell k Lu hell a Lam).a * ((PK ell k Lu hell a Lam).ell : ℝ) ^ (PK ell k Lu hell a Lam).k
      = a * (ell : ℝ) ^ k := rfl
  have hT2 : ‖Tfull (PK ell k Lu hell a Lam).G (PK ell k Lu hell a Lam).U A‖ ^ 2
      = ‖Rproj (geomOf ell k (fullTower ell k Lu)) (flatCfg : PeriodicLinkConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (gradAdj flatCfg A)‖ ^ 2 := by
    have := congrArg (fun t => t ^ 2) hT
    exact this
  have hQ2 : a * (ell : ℝ) ^ k * ‖(PK ell k Lu hell a Lam).data.Q x‖ ^ 2
      = κ * ∑ j, ‖L2 hdvd (coordB (WithLp.ofLp A) j)‖ ^ 2 := by
    refine (congrArg (fun t => a * (ell : ℝ) ^ k * t) (h3.trans h4)).trans ?_
    rw [hκ]; push_cast; field_simp
  rw [e, hQ2]
  have hka : κ * ((ell ^ k : ℕ) : ℝ) ^ 7 = a := by rw [hκ]; field_simp
  have hper : ∀ j, hfun2 a / ((ell ^ k : ℕ) : ℝ) ^ 2 * ‖coordB (WithLp.ofLp A) j‖ ^ 2 ≤
      ‖L1 (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j)‖ ^ 2 + κ * ‖L2 hdvd (coordB (WithLp.ofLp A) j)‖ ^ 2
        + ‖L3 hdvd (coordB (WithLp.ofLp A) j)‖ ^ 2 := by
    intro j
    exact torus_coercive_kappa hn hκpos.le
      (fun z w S hS0 hS => by
        have := cell_coercive_explicit2 hn κ hκpos z w S hS0 hS
        rwa [hka] at this)
      (scaleUp ell k Lu) hdvd (coordB (WithLp.ofLp A) j)
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hper j)
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hxx : hfun2 a / ((ell ^ k : ℕ) : ℝ) ^ 2 * ‖x‖ ^ 2 = hfun2 a / ((ell ^ k : ℕ) : ℝ) ^ 2 * ∑ j, ‖coordB (WithLp.ofLp A) j‖ ^ 2 := by
    rw [hx, h5]
  rw [hxx, h1, hT2]
  exact hsum.trans (by
    have := add_le_add_left h2 (∑ j, ‖L1 (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j)‖ ^ 2
      + κ * ∑ j, ‖L2 hdvd (coordB (WithLp.ofLp A) j)‖ ^ 2)
    linarith)

#print axioms G1inv_coercive_explicit2


theorem hfun2_pos (a : ℝ) (ha : 0 < a) : 0 < hfun2 a := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hmuF : ∀ σ x : ℝ, 0 < σ → 0 < x → 0 < muF σ a x := by
    intro σ x hσ hx; unfold muF; positivity
  have hrat : ∀ m : ℝ, 0 < m → 0 < rat m := by intro m hm; unfold rat; positivity
  have hL : ∀ σ : ℝ, 0 < σ → 0 < LmF σ a := by
    intro σ hσ; unfold LmF; exact lt_min (by positivity) (by positivity)
  unfold hfun2 cS2 cL2
  refine lt_min (mul_pos (hrat _ (hmuF _ _ (by norm_num) (hL _ (by norm_num)))) (hL _ (by norm_num))) (lt_min ?_ ?_)
  · exact mul_pos (by norm_num) (hrat _ (hmuF _ _ (by positivity) (by positivity)))
  · exact mul_pos (by positivity) (hrat _ (hmuF _ _ (by positivity) (by norm_num)))

/-- **THE SCALED k-UNIFORM COERCIVITY OF THE GENUINE FLAT `G₁⁻¹`, v2** -/
theorem scaled_G1inv2 (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 < a)
    (Lu : PeriodicLatticeExtent) (Lam : Set (PeriodicLatticeSite Lu))
    (x : ↥(bondSupp (PK ell k Lu hell a Lam).G)) :
    hfun2 a * ‖x‖ ^ 2 ≤ (ell : ℝ) ^ (2 * k) * inner ℝ x ((PK ell k Lu hell a Lam).G1inv x) := by
  have hn : 0 < ell ^ k := pow_pos hell k
  have h := G1inv_coercive_explicit2 ell k hell a ha Lu Lam x
  have hp : (((ell ^ k : ℕ) : ℝ)) ^ 2 = (ell : ℝ) ^ (2 * k) := by
    push_cast; rw [pow_mul', ← pow_mul]
  have hpp : (0 : ℝ) < (ell : ℝ) ^ (2 * k) := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  rw [hp] at h
  rw [div_mul_eq_mul_div, div_le_iff₀ hpp] at h
  simpa [mul_comm] using h

theorem hunit_scaled_flat2 (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 < a)
    (Lu : PeriodicLatticeExtent) (Lam : Set (PeriodicLatticeSite Lu)) (hN : ∀ μ, 1 ≤ Lu μ) :
    IsUnit (((PK ell k Lu hell a Lam).Qin.comp (PK ell k Lu hell a Lam).G1in).comp
      (ContinuousLinearMap.adjoint (PK ell k Lu hell a Lam).Qin)) := by
  have hp : (0 : ℝ) < (ell : ℝ) ^ (2 * k) := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  refine hunit_of_coercive ell k Lu hell a Lam hN (hfun2 a / (ell : ℝ) ^ (2 * k))
    (div_pos (hfun2_pos a ha) hp) (fun x => ?_)
  have := scaled_G1inv2 ell k hell a ha Lu Lam x
  rw [div_mul_eq_mul_div, div_le_iff₀ hp]
  simpa [mul_comm] using this

theorem hfun2_le (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (Lam : Set (PeriodicLatticeSite Lu)) (ha : 0 < a) (hN : ∀ μ, 1 ≤ Lu μ) : hfun2 a ≤ a :=
  flat_scaled_ceiling ell k Lu hell a Lam hN (hfun2 a) (fun x => scaled_G1inv2 ell k hell a ha Lu Lam x)

#print axioms scaled_G1inv2
#print axioms hunit_scaled_flat2
#print axioms hfun2_le
#print axioms hfun2_pos

end AdalyFormal.ScaledCoercivity
