import GenKGeometry
import AdalyFormal.Balaban.FullySupplied
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace HConstruction.GenK
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo curlCovariantLM)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue curlCovariantLM_trivialU_eq_flatCurlLM)
open AdalyFormal.Balaban.DeltaKUnified (BFL2 bfl2Equiv)
open AdalyFormal.Balaban.FullySupplied (suTwoLift suTwoLift_add suTwoLift_smul lineCoarseRestrictSuTwo_suTwoLift)
open AdalyFormal.Balaban.RegularUGamma0 (ell_coarseCurlEnergy_le_plaqEnergy_trivialU)

variable (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n)
abbrev Fine := BFL2 (fineExtent M n)
abbrev Unit := BFL2 M
abbrev Plaq := PiLp 2 (fun _ : PeriodicLatticePlaquette (fineExtent M n) => SuTwo)

def incoming : Fine M (n := n) →L[ℝ] Unit M :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A => bfl2Equiv.symm (unitField M hn
      (lineCoarseRestrictCovLM (trivialU (fineExtent M n)) n (bfl2Equiv A)))
    map_add' := by intro A B; apply bfl2Equiv.injective; funext b; simp [unitField]
    map_smul' := by intro r A; apply bfl2Equiv.injective; funext b; simp [unitField] }

lemma incoming_apply (A : Fine M (n := n)) (b : Bond M) :
    bfl2Equiv (incoming M hn A) b = lineCoarseRestrictSuTwo n (bfl2Equiv A) (bonds M hn b) :=
  lineCoarseRestrictCov_trivialU n _ _

/-- A genuine fine-carrier section, supported on each block's last layers. -/
def lift : Unit M →L[ℝ] Fine M (n := n) := LinearMap.toContinuousLinearMap {
  toFun := fun B => bfl2Equiv.symm (suTwoLift n (fun c => bfl2Equiv B ((bonds M hn).symm c)))
  map_add' := by
    intro A B; apply bfl2Equiv.injective; funext b
    simp only [map_add,LinearEquiv.apply_symm_apply,Pi.add_apply,suTwoLift]
    split_ifs <;> simp only [smul_add,add_zero]
  map_smul' := by
    intro r A; apply bfl2Equiv.injective; funext b
    simp only [map_smul,LinearEquiv.apply_symm_apply,Pi.smul_apply,RingHom.id_apply,suTwoLift]
    split_ifs
    · exact smul_comm _ _ _
    · exact (smul_zero _).symm }

lemma lift_apply (B : Unit M) : bfl2Equiv (lift M hn B) =
    suTwoLift n (fun c => bfl2Equiv B ((bonds M hn).symm c)) := rfl

attribute [local irreducible] incoming lift

lemma incoming_lift (B : Unit M) : incoming M hn (lift M hn B) = B := by
  apply bfl2Equiv.injective; funext b
  rw [incoming_apply]
  rw [lift_apply]
  rw [lineCoarseRestrictSuTwo_suTwoLift hn (fineTiling M hn)]
  simp only [Equiv.symm_apply_apply]

/-- Unscaled fine curl; physical curl at eta=1/n is n times this map. -/
def curl : Fine M (n := n) →L[ℝ] Plaq M (n := n) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp
      ((curlCovariantLM (trivialU (fineExtent M n))).comp bfl2Equiv.toLinearMap))

lemma curl_apply (A : Fine M (n := n)) (p : PeriodicLatticePlaquette (fineExtent M n)) :
    curl M A p = flatCurlValue (bfl2Equiv A) p := by
  change (curlCovariantLM (trivialU _) (bfl2Equiv A)) p = _
  rw [curlCovariantLM_trivialU_eq_flatCurlLM]; rfl

lemma curl_norm (A : Fine M (n := n)) : ‖curl M A‖^2 = curlEnergy (bfl2Equiv A) := by
  rw [norm_sq_coordinates]
  simp only [curl_apply,curlEnergy]

def fineEnergy (A : Fine M (n := n)) : ℝ := (1/(n:ℝ))*‖curl M A‖^2

include hn in
/-- The density is eta^3; physical curl is eta^-1 times the unit-step curl.
The two factors compensate to 1/n, exactly the Stokes comparison factor. -/
lemma physical_density (A : Fine M (n := n)) :
    (1/(n:ℝ)^3)*‖(n:ℝ) • curl M A‖^2 = fineEnergy M A := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg n)]
  unfold fineEnergy
  have hne : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- CMP95 (1.67), lower direction: constant ONE at every scale and volume.
It is valid for every fine field, not just a minimizer. -/
theorem comparison (A : Fine M (n := n)) :
    curlEnergy (bfl2Equiv (incoming M hn A)) ≤ fineEnergy M A := by
  have h := ell_coarseCurlEnergy_le_plaqEnergy_trivialU hn (fineTiling M hn) (bfl2Equiv A)
  have hc : curlCovariantLM (trivialU (fineExtent M n)) (bfl2Equiv A) = flatCurlValue (bfl2Equiv A) := by
    rw [curlCovariantLM_trivialU_eq_flatCurlLM]; rfl
  rw [hc, ← curlEnergy_reindex M hn] at h
  have hi : unitField M hn (lineCoarseRestrictCovLM (trivialU (fineExtent M n)) n (bfl2Equiv A)) =
      bfl2Equiv (incoming M hn A) := by unfold incoming; rfl
  rw [hi] at h
  change (n:ℝ) * curlEnergy (bfl2Equiv (incoming M hn A)) ≤ curlEnergy (bfl2Equiv A) at h
  unfold fineEnergy
  rw [curl_norm,one_div_mul_eq_div]
  exact (le_div_iff₀ (by exact_mod_cast hn : (0:ℝ)<n)).mpr (by simpa [mul_comm] using h)

/-- Every actual lift of an axial outgoing-Q-null unit field pays the same floor.
There is no compactness constant and no per-depth casework. -/
theorem every_extension_lower (hM : ∀ μ : Fin 3, 4 ≤ M μ)
    (heven : ∀ μ : Fin 3, 2 ∣ (M μ+1))
    (A : Fine M (n := n))
    (hAx : Axial (bfl2Equiv (incoming M hn A)))
    (hQ : ∀ c, lineCoarseRestrictSuTwo 2 (bfl2Equiv (incoming M hn A)) c = 0) :
    (1/1728:ℝ)*‖incoming M hn A‖^2 ≤ fineEnergy M A := by
  have h := lemma24_kernel hM heven _ hAx hQ
  rw [bondEnergy_norm] at h
  exact h.trans (comparison M hn A)

#print axioms incoming_lift
#print axioms physical_density
#print axioms comparison
#print axioms every_extension_lower
end HConstruction.GenK
