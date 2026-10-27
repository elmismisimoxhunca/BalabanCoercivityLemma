import GenKComparison
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace HConstruction.GenK
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)

variable (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n)
attribute [local irreducible] incoming lift curl

def nullSpace : Submodule ℝ (Fine M (n := n)) := (incoming M hn).ker

def nullCurl : nullSpace M hn →ₗ[ℝ] Plaq M (n := n) :=
  (curl M).toLinearMap.comp (nullSpace M hn).subtype

def curlImage : Submodule ℝ (Plaq M (n := n)) := (nullCurl M hn).range

/-- A linear section on the actual image, not an assumed inverse on the whole space. -/
def imageSection : curlImage M hn →ₗ[ℝ] nullSpace M hn :=
  Classical.choose ((nullCurl M hn).rangeRestrict.exists_rightInverse_of_surjective
    (nullCurl M hn).range_rangeRestrict)

lemma imageSection_right (v : curlImage M hn) :
    nullCurl M hn (imageSection M hn v) = v := by
  have h := Classical.choose_spec ((nullCurl M hn).rangeRestrict.exists_rightInverse_of_surjective
    (nullCurl M hn).range_rangeRestrict)
  exact congrArg Subtype.val (LinearMap.congr_fun h v)

def correction : Unit M →L[ℝ] Fine M (n := n) :=
  (nullSpace M hn).subtypeL.comp ((imageSection M hn).toContinuousLinearMap.comp
    ((curlImage M hn).orthogonalProjectionOnto.comp ((curl M).comp (lift M hn))))

/-- The single scale-parametric minimizing lift, full fine carrier retained. -/
def H : Unit M →L[ℝ] Fine M (n := n) := lift M hn - correction M hn

lemma correction_in_kernel (B : Unit M) : incoming M hn (correction M hn B) = 0 :=
  (imageSection M hn ((curlImage M hn).orthogonalProjectionOnto (curl M (lift M hn B)))).2

lemma curl_correction (B : Unit M) :
    curl M (correction M hn B) = (curlImage M hn).starProjection (curl M (lift M hn B)) :=
  imageSection_right M hn _

lemma H_interpolates (B : Unit M) : incoming M hn (H M hn B) = B := by
  rw [H,_root_.sub_apply,map_sub,incoming_lift,correction_in_kernel,sub_zero]

lemma curl_H (B : Unit M) :
    curl M (H M hn B) = curl M (lift M hn B) -
      (curlImage M hn).starProjection (curl M (lift M hn B)) := by
  rw [H,_root_.sub_apply,map_sub,curl_correction]

lemma curl_sub_lift_mem (A : Fine M (n := n)) (B : Unit M)
    (hq : incoming M hn A = B) : curl M (A-lift M hn B) ∈ curlImage M hn := by
  refine ⟨⟨A-lift M hn B, ?_⟩,rfl⟩
  change incoming M hn (A-lift M hn B) = 0
  rw [map_sub,hq,incoming_lift,sub_self]

lemma curl_H_eq_residual (A : Fine M (n := n)) (B : Unit M)
    (hq : incoming M hn A = B) :
    curl M (H M hn B) = curl M A - (curlImage M hn).starProjection (curl M A) := by
  have h := (curlImage M hn).starProjection_eq_self_iff.mpr (curl_sub_lift_mem M hn A B hq)
  rw [map_sub,map_sub] at h
  rw [curl_H]
  calc
    curl M (lift M hn B) - (curlImage M hn).starProjection (curl M (lift M hn B)) =
      curl M A - (curl M A - curl M (lift M hn B)) -
        (curlImage M hn).starProjection (curl M (lift M hn B)) := by abel
    _ = curl M A - ((curlImage M hn).starProjection (curl M A) -
        (curlImage M hn).starProjection (curl M (lift M hn B))) -
        (curlImage M hn).starProjection (curl M (lift M hn B)) := by rw [h]
    _ = _ := by abel

/-- Attained minimum on the full incoming-Q fibre, not a formal infimum of an
empty set and not an energy artificially assigned to the coarse field. -/
theorem minimum (A : Fine M (n := n)) (B : Unit M) (hq : incoming M hn A = B) :
    fineEnergy M (H M hn B) ≤ fineEnergy M A := by
  have h := (curlImage M hn).norm_sq_eq_add_norm_sq_starProjection (curl M A)
  rw [Submodule.starProjection_orthogonal_val] at h
  rw [fineEnergy,fineEnergy,curl_H_eq_residual M hn A B hq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [sq_nonneg ‖(curlImage M hn).starProjection (curl M A)‖]

/-- The source's flat pullback precision with the physical density included. -/
def Delta : Unit M →L[ℝ] Unit M :=
  (1/(n:ℝ)) • ((curl M).comp (H M hn)).adjoint.comp ((curl M).comp (H M hn))

/-- CMP95 (1.65) in the flat physical normalization, for the constructed minimizer. -/
theorem pullback (B : Unit M) :
    (inner ℝ B (Delta M hn B) : ℝ) = fineEnergy M (H M hn B) := by
  simp only [Delta,_root_.smul_apply,ContinuousLinearMap.comp_apply,inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right,real_inner_self_eq_norm_sq,fineEnergy]

theorem Delta_comparison (B : Unit M) :
    curlEnergy (bfl2Equiv B) ≤ (inner ℝ B (Delta M hn B) : ℝ) := by
  rw [pullback]
  have h := comparison M hn (H M hn B)
  rwa [H_interpolates] at h

/-- A single explicit floor on every compatible unit torus and every n>0.
This is not an induction on compactness witnesses. -/
theorem uniform_coercivity (hM : ∀ μ : Fin 3, 4 ≤ M μ)
    (heven : ∀ μ : Fin 3, 2 ∣ (M μ+1))
    (B : Unit M) (hAx : Axial (bfl2Equiv B))
    (hQ : ∀ c, lineCoarseRestrictSuTwo 2 (bfl2Equiv B) c = 0) :
    (1/1728:ℝ)*‖B‖^2 ≤ (inner ℝ B (Delta M hn B) : ℝ) := by
  have h := lemma24_kernel hM heven _ hAx hQ
  rw [bondEnergy_norm] at h
  exact h.trans (Delta_comparison M hn B)

/-- The genuine incoming depth is a parameter, not a case split over 1,2,3. -/
def depthDelta (k : ℕ) : Unit M →L[ℝ] Unit M := Delta M (pow_pos (by decide : 0<2) k)

theorem depth_uniform (hM : ∀ μ : Fin 3, 4 ≤ M μ)
    (heven : ∀ μ : Fin 3, 2 ∣ (M μ+1)) :
    ∀ k : ℕ, ∀ B : Unit M, Axial (bfl2Equiv B) →
      (∀ c, lineCoarseRestrictSuTwo 2 (bfl2Equiv B) c = 0) →
      (1/1728:ℝ)*‖B‖^2 ≤ (inner ℝ B (depthDelta M k B) : ℝ) := by
  intro k B ha hq
  exact uniform_coercivity M (pow_pos (by decide : 0<2) k) hM heven B ha hq

#print axioms H_interpolates
#print axioms minimum
#print axioms pullback
#print axioms Delta_comparison
#print axioms depth_uniform
end HConstruction.GenK
