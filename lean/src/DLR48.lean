import DLR46
import DLR47

/-!
# DL48 -- the SMOOTH right inverse of the genuine top-level bond map, as an operator `FSp → BondFnL2` (full tower)

* `Wof` : `FSp ≅ (coarse bonds → su(2))` (MF5e's identification through `eqv` and `bondsE`), `Wof_sum` : `Σ_c ‖Wof u c‖² = ‖u‖²`.
* `Eop` : `u ↦ sbondE n (Wof u)` (DL44), a CLM.
* **`Eop_rightInv`** : `Q₁(Eop u) = u` (`Q₁` = the genuine `Qfull` at `U = 1`; via FE2b `Qfull_top_gen` and `sbondE_rightInv`).
* **`Eop_norm_sq`** : `‖Eop u‖² ≤ (81/4)² n³ ‖u‖²`;  **`Eop_grad`** : `gradE (Eop u) ν ≤ 419904 n ‖u‖²` (every `ν`).
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 20000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.M0Finish (PU)

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)

/-- the reference parameter set (flat, `a = 1`, `Λ = ∅`) used only for the index identification -/
noncomputable abbrev Pfl : IngrBParams := PU ell k Lu hell flatCfg 1 ∅

theorem Pfl_FS : (Pfl ell k Lu hell).FullSupp := fullTower_fullSupp ell k Lu hell flatCfg 1 ∅

/-- the coarse-bond field of a unit-bond vector -/
noncomputable def Wof (u : FSp (GF ell k Lu)) : CoarseBond (scaleUp ell k Lu) (ell ^ k) → SuTwo :=
  fun c => (WithLp.ofLp u) ((Pfl ell k Lu hell).eqv (Pfl_FS ell k Lu hell)
    ((AdalyFormal.GenuineU1.bondsE ell k Lu hell).symm c))

theorem Wof_sum (u : FSp (GF ell k Lu)) :
    ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ k), ‖Wof ell k Lu hell u c‖ ^ 2 = ‖u‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  have e1 : ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ k), ‖Wof ell k Lu hell u c‖ ^ 2
      = ∑ e' : Bond Lu, ‖(WithLp.ofLp u) ((Pfl ell k Lu hell).eqv (Pfl_FS ell k Lu hell) e')‖ ^ 2 := by
    refine Fintype.sum_equiv (AdalyFormal.GenuineU1.bondsE ell k Lu hell).symm _ _ (fun c => ?_)
    rfl
  rw [e1]
  exact Fintype.sum_equiv ((Pfl ell k Lu hell).eqv (Pfl_FS ell k Lu hell)) _ _ (fun e' => rfl)

/-- the smooth right inverse as a linear map -/
noncomputable def EopL : FSp (GF ell k Lu) →ₗ[ℝ] BondFnL2 (scaleUp ell k Lu) where
  toFun u := WithLp.toLp 2 (sbondE (ell ^ k) (Wof ell k Lu hell u))
  map_add' u v := by
    refine PiLp.ext (fun b => ?_)
    simp only [sbondE, gbondE, Wof, PiLp.add_apply, WithLp.ofLp_add, Pi.add_apply, smul_add, Finset.sum_add_distrib,
      PiLp.toLp_apply]
  map_smul' r u := by
    refine PiLp.ext (fun b => ?_)
    simp only [sbondE, gbondE, Wof, PiLp.smul_apply, WithLp.ofLp_smul, Pi.smul_apply, RingHom.id_apply,
      PiLp.toLp_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    exact smul_comm _ _ _

/-- the smooth right inverse -/
noncomputable def Eop : FSp (GF ell k Lu) →L[ℝ] BondFnL2 (scaleUp ell k Lu) :=
  LinearMap.toContinuousLinearMap (EopL ell k Lu hell)

theorem Eop_apply (u : FSp (GF ell k Lu)) (b : Bond (scaleUp ell k Lu)) :
    (Eop ell k Lu hell u) b = sbondE (ell ^ k) (Wof ell k Lu hell u) b := rfl

/-- **`Q₁ (Eop u) = u`** -/
theorem Eop_rightInv (u : FSp (GF ell k Lu)) :
    (bondSectorOf (GF ell k Lu) (trivialU _)).Qfull (Eop ell k Lu hell u) = u := by
  set P := Pfl ell k Lu hell with hP
  have hFS : P.FullSupp := Pfl_FS ell k Lu hell
  have hdvdf : ∀ ν, ell ^ k ∣ scaleUp ell k Lu ν + 1 := AdalyFormal.GenuineU1.scaleUp_tiling ell k Lu hell
  refine PiLp.ext (fun p => ?_)
  obtain ⟨e', rfl⟩ := (P.eqv hFS).surjective p
  have h1 := AdalyFormal.FlatEllGeneral.Qfull_top_gen (PU ell k Lu hell flatCfg 1 ∅) rfl (Eop ell k Lu hell u) e'
    (IngrBParams.mem_of_fullSupp P hFS e')
  have h2 := sbondE_rightInv (ell ^ k) (pow_pos hell k) hdvdf (Wof ell k Lu hell u)
    (AdalyFormal.GenuineU1.bondsE ell k Lu hell e')
  show (bondSectorOf (GF ell k Lu) (trivialU _)).Qfull (Eop ell k Lu hell u)
      (AdalyFormal.StatementLaneG.pe P e' (IngrBParams.mem_of_fullSupp P hFS e')) = _
  rw [show (bondSectorOf (GF ell k Lu) (trivialU _)).Qfull (Eop ell k Lu hell u)
        (AdalyFormal.StatementLaneG.pe P e' (IngrBParams.mem_of_fullSupp P hFS e'))
      = ((PU ell k Lu hell flatCfg 1 ∅).sector.Qfull (Eop ell k Lu hell u))
          (AdalyFormal.StatementLaneG.pe (PU ell k Lu hell flatCfg 1 ∅) e' (IngrBParams.mem_of_fullSupp P hFS e'))
      from rfl, h1]
  show lineCoarseRestrictSuTwo (ell ^ k) (sbondE (ell ^ k) (Wof ell k Lu hell u))
    (AdalyFormal.GenuineU1.bondsE ell k Lu hell e') = _
  rw [h2]
  simp only [Wof, Equiv.symm_apply_apply]
  rfl

/-- **`‖Eop u‖² ≤ (81/4)² n³ ‖u‖²`** -/
theorem Eop_norm_sq (u : FSp (GF ell k Lu)) :
    ‖Eop ell k Lu hell u‖ ^ 2 ≤ (81 / 4) ^ 2 * ((ell : ℝ) ^ k) ^ 3 * ‖u‖ ^ 2 := by
  have hdvdf : ∀ ν, ell ^ k ∣ scaleUp ell k Lu ν + 1 := AdalyFormal.GenuineU1.scaleUp_tiling ell k Lu hell
  have h := sbondE_norm_sq (ell ^ k) (pow_pos hell k) hdvdf (Wof ell k Lu hell u)
  rw [Wof_sum] at h
  rw [PiLp.norm_sq_eq_of_L2]
  have e2 : ((ell ^ k : ℕ) : ℝ) = (ell : ℝ) ^ k := by rw [Nat.cast_pow]
  rw [e2] at h
  have e3 : (9 * (3 / 2 : ℝ) ^ 2) ^ 2 = (81 / 4) ^ 2 := by norm_num
  rw [e3] at h
  exact h

theorem Eop_norm (u : FSp (GF ell k Lu)) :
    ‖Eop ell k Lu hell u‖ ≤ (81 / 4) * Real.sqrt (((ell : ℝ) ^ k) ^ 3) * ‖u‖ := by
  have h := Eop_norm_sq ell k Lu hell u
  have hn : (0 : ℝ) ≤ ((ell : ℝ) ^ k) ^ 3 := by positivity
  have h2 : ‖Eop ell k Lu hell u‖ ^ 2 ≤ ((81 / 4) * Real.sqrt (((ell : ℝ) ^ k) ^ 3) * ‖u‖) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hn]; linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

/-- **the extension is smooth: `gradE (Eop u) ν ≤ 419904 n ‖u‖²`** -/
theorem Eop_grad (u : FSp (GF ell k Lu)) (ν : Fin 3) :
    gradE (Eop ell k Lu hell u) ν ≤ 419904 * (ell : ℝ) ^ k * ‖u‖ ^ 2 := by
  have hdvdf : ∀ ν, ell ^ k ∣ scaleUp ell k Lu ν + 1 := AdalyFormal.GenuineU1.scaleUp_tiling ell k Lu hell
  have h := sbondE_grad_sq (ell ^ k) (pow_pos hell k) hdvdf ν (Wof ell k Lu hell u)
  rw [Wof_sum] at h
  have e2 : ((ell ^ k : ℕ) : ℝ) = (ell : ℝ) ^ k := by rw [Nat.cast_pow]
  rw [e2] at h
  exact h

end

#print axioms Wof_sum
#print axioms Eop
#print axioms Eop_rightInv
#print axioms Eop_norm_sq
#print axioms Eop_norm
#print axioms Eop_grad

end AdalyFormal.DLayer
