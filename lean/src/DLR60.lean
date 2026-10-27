import DLR53
import DLR59

/-!
# DL60 -- **`hJs_class`: premise hJs of DL5 on the printed class at the full tower**

`‖(PU ℓ k Lu hell U a Λ).Jf b‖ ≤ JSfree(fMα₀) / n³` for every fine bond `b`, every `U` in
`PerCubeRegular2 ℓ M f k (fullTower ℓ k Lu) α₀ (ℓ^k)⁻¹` with `4 ≤ f`, `0 < M`, `4fMα₀ ≤ 1` (all k-free).
* `Jf_norm` : `‖P.Jf b‖ = frobNorm (JfieldLoc (plaqIn Ω₀) U b.1 b.2)/√2` (`‖Y‖² = ½ frobSq Y` on `𝔰𝔲(2)`; η = 1 body);
* `plaqIn_full` : `plaqIn Ω₀ = univ` on the full tower.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 20000

namespace AdalyFormal.DLayer

open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq norm_sq_eq_half_frobSq)
open AdalyFormal.Balaban.SourceJ (Jfield)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane2 (PerCubeRegular2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.M0Finish (PU)

theorem plaqIn_full (ell k : ℕ) (Lu : PeriodicLatticeExtent) :
    plaqIn (geomOf ell k (fullTower ell k Lu)).Om0 = Set.univ := by
  ext p
  simp [plaqIn, geomOf, fullTower]

theorem Jf_norm (P : IngrBParams) (b : Bond (scaleUp P.ell P.k P.Lu)) :
    ‖P.Jf b‖ = frobNorm (AdalyFormal.IngredientFamily.JfieldLoc (plaqIn P.G.Om0) P.U b.1 b.2) / Real.sqrt 2 := by
  have e1 : P.Jf b = -(AdalyFormal.IngredientFamily.JSU2Loc 1 (plaqIn P.G.Om0) P.U b) := rfl
  rw [e1, norm_neg]
  set Y := AdalyFormal.IngredientFamily.JSU2Loc 1 (plaqIn P.G.Om0) P.U b with hY
  have hcoe : (Y : Matrix (Fin 2) (Fin 2) ℂ)
      = ((-Complex.I) * (((1 : ℝ)⁻¹ ^ 3 : ℝ) : ℂ)) • AdalyFormal.IngredientFamily.JfieldLoc (plaqIn P.G.Om0) P.U b.1 b.2 := rfl
  have hsq := norm_sq_eq_half_frobSq Y
  rw [hcoe, frobSq_csmul] at hsq
  have hn : Complex.normSq ((-Complex.I) * (((1 : ℝ)⁻¹ ^ 3 : ℝ) : ℂ)) = 1 := by simp
  rw [hn, one_mul] at hsq
  have h2 : ‖Y‖ = Real.sqrt ((1 / 2 : ℝ) * frobSq (AdalyFormal.IngredientFamily.JfieldLoc (plaqIn P.G.Om0) P.U b.1 b.2)) := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [h2, Real.sqrt_mul (by norm_num)]
  have e : Real.sqrt (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_one]
  rw [e]
  unfold frobNorm
  ring

/-- **premise hJs on the class** -/
theorem hJs_class (ell M f k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (α₀ : ℝ) (hM : 0 < M) (hf : 4 ≤ f)
    (hP : PerCubeRegular2 ell M f k (fullTower ell k Lu) α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hsm : 4 * ((f : ℝ) * M * α₀) ≤ 1) (b : Bond (scaleUp ell k Lu)) :
    ‖(PU ell k Lu hell U a Lam).Jf b‖ ≤ JSfree ((f : ℝ) * M * α₀) / ((ell : ℝ) ^ k) ^ 3 := by
  rw [Jf_norm]
  have hpl : plaqIn (PU ell k Lu hell U a Lam).G.Om0 = Set.univ := plaqIn_full ell k Lu
  rw [hpl, AdalyFormal.IngredientFamily.JfieldLoc_univ]
  have h := J_class_frob ell M f k Lu hell U α₀ hM hf hP hsm b.1 b.2
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  have hs2 : 0 < Real.sqrt 2 := by positivity
  rw [div_le_div_iff₀ hs2 (by positivity)]
  unfold JSfree
  rw [div_mul_eq_mul_div, le_div_iff₀ hs2]
  have e : (((ell : ℝ) ^ k)⁻¹) ^ 3 = 1 / ((ell : ℝ) ^ k) ^ 3 := by rw [inv_pow, one_div]
  rw [e] at h
  have h' : frobNorm (Jfield U b.1 b.2) * ((ell : ℝ) ^ k) ^ 3
      ≤ ((f * M * α₀) + 40 * (f * M * α₀) ^ 2 + 4144 * (f * M * α₀) ^ 3 + 8192 * (f * M * α₀) ^ 4) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at h
    linarith
  nlinarith [Real.sqrt_nonneg 2, frobNorm_nonneg (Jfield U b.1 b.2)]

#print axioms plaqIn_full
#print axioms Jf_norm
#print axioms hJs_class

end AdalyFormal.DLayer
