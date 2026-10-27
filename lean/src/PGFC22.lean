import PGFC21

/-!
# GFC22 -- **VOLUME-INDEPENDENT COERCIVITY OF THE FLAT `G₁⁻¹ = Δ_a(1)`** in the repo's genuine objects.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
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

namespace AdalyFormal.FlatCoercivity

theorem comb_real (c0 m κ S1 S2 S3 B : ℝ) (hm1 : m ≤ 1) (hm2 : m ≤ κ) (hmp : 0 < m)
    (h : c0 * B ≤ S1 + S2 + S3) (hc0 : 0 < c0) (s1 : 0 ≤ S1) (s2 : 0 ≤ S2) (s3 : 0 ≤ S3) :
    c0 * m * B ≤ S1 + κ * S2 + S3 := by
  have a1 : m * S1 ≤ S1 := by nlinarith
  have a2 : m * S2 ≤ κ * S2 := mul_le_mul_of_nonneg_right hm2 s2
  have a3 : m * S3 ≤ S3 := by nlinarith
  have a4 : m * (c0 * B) ≤ m * (S1 + S2 + S3) := mul_le_mul_of_nonneg_left h hmp.le
  nlinarith

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))
local notation "PP" => PK ell k Lu hell a Lam

theorem Qnorm_eq (x : ↥(bondSupp (PP).G)) :
    ‖(PP).data.Q x‖ ^ 2 = ∑ b : CoarseBond (scaleUp ell k Lu) (ell ^ k),
      ‖lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp (iE (PP).G x)) b‖ ^ 2 := by
  have hFS : (PP).FullSupp := PK_fullSupp ell k Lu hell a Lam
  have hQ : (PP).data.Q x = (PP).sector.Qfull (iE (PP).G x) := rfl
  rw [hQ, PiLp.norm_sq_eq_of_L2]
  rw [← Equiv.sum_comp ((PP).eqv hFS)]
  simp only [Qfull_top ell k Lu hell a Lam]
  exact Equiv.sum_comp (bondsE ell k Lu hell) (fun b => ‖lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp (iE (PP).G x)) b‖ ^ 2)

end

/-- **VOLUME-INDEPENDENT COERCIVITY of the flat `G₁⁻¹` (genuine objects), explicit dependence on `a` and `k`:**
there is `c = c₀(ell^k) · min(1, a (ell^k)^{-7}) > 0`, independent of the unit torus `Lu` and of `Λ`,
with `c ‖x‖² ≤ ⟨x, G₁⁻¹ x⟩`. -/
theorem G1inv_coercive_volume_free (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Lu : PeriodicLatticeExtent) (Lam : Set (PeriodicLatticeSite Lu))
      (x : ↥(bondSupp (PK ell k Lu hell a Lam).G)), c * ‖x‖ ^ 2 ≤ inner ℝ x ((PK ell k Lu hell a Lam).G1inv x) := by
  have hn : 0 < ell ^ k := pow_pos hell k
  obtain ⟨c0, hc0, hc⟩ := torus_coercive hn
  have hnR : (0 : ℝ) < ((ell ^ k : ℕ) : ℝ) := by exact_mod_cast hn
  set κ : ℝ := a * ((ell ^ k : ℕ) : ℝ) / ((ell ^ k : ℕ) : ℝ) ^ 8 with hκ
  have hκpos : 0 < κ := by positivity
  refine ⟨c0 * min 1 κ, mul_pos hc0 (lt_min one_pos hκpos), ?_⟩
  intro Lu Lam x
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
  show c0 * min 1 κ * ‖x‖ ^ 2 ≤ ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
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
  have hper : ∀ j, c0 * min 1 κ * ‖coordB (WithLp.ofLp A) j‖ ^ 2 ≤
      ‖L1 (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j)‖ ^ 2 + κ * ‖L2 hdvd (coordB (WithLp.ofLp A) j)‖ ^ 2
        + ‖L3 hdvd (coordB (WithLp.ofLp A) j)‖ ^ 2 := by
    intro j
    have hcj := hc (scaleUp ell k Lu) hdvd (coordB (WithLp.ofLp A) j)
    have hm1 : min 1 κ ≤ 1 := min_le_left _ _
    have hm2 : min 1 κ ≤ κ := min_le_right _ _
    have hmp : 0 < min 1 κ := lt_min one_pos hκpos
    have s1 := sq_nonneg ‖L1 (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j)‖
    have s2 := sq_nonneg ‖L2 hdvd (coordB (WithLp.ofLp A) j)‖
    have s3 := sq_nonneg ‖L3 hdvd (coordB (WithLp.ofLp A) j)‖
    exact comb_real c0 (min 1 κ) κ _ _ _ _ hm1 hm2 hmp hcj hc0 s1 s2 s3
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hper j)
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hxx : c0 * min 1 κ * ‖x‖ ^ 2 = c0 * min 1 κ * ∑ j, ‖coordB (WithLp.ofLp A) j‖ ^ 2 := by rw [hx, h5]
  rw [hxx, h1, hT2]
  exact hsum.trans (by
    have := add_le_add_left h2 (∑ j, ‖L1 (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j)‖ ^ 2 + κ * ∑ j, ‖L2 hdvd (coordB (WithLp.ofLp A) j)‖ ^ 2)
    linarith)

#print axioms G1inv_coercive_volume_free

end AdalyFormal.FlatCoercivity
