import GenKGauge
import ScaledPerturbation
/-! Exact identities for GenK's actual R gauge. These are not a uniform mass
estimate: the final mass identity retains its signed cross term. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace HConstruction.MassU1
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open HConstruction.GenK
variable (M : PeriodicLatticeExtent) {n : ℕ}
attribute [local irreducible] incoming curl H physicalH gaugePotential

def mass (A : Fine M (n := n)) : ℝ := (1/(n:ℝ)^3)*‖A‖^2

/-- Literal phase-R physical mass, not the unscaled fine norm. -/
theorem mass_eq_phaseR (A : Fine M (n := n)) :
    mass M A = RegU.mass n (bfl2Equiv A) := by
  unfold mass RegU.mass
  change (1/(n:ℝ)^3)*‖A‖^2 = (1/(n:ℝ)^3)*GenK.bondEnergy (bfl2Equiv A)
  rw [bondEnergy_norm]

lemma delta_inner (f g : Site M (n := n)) :
    inner ℝ (siteDelta M f) g = inner ℝ (grad M f) (grad M g) := by
  exact (grad M).adjoint_inner_left g (grad M f)

lemma delta_symmetric (f g : Site M (n := n)) :
    inner ℝ (siteDelta M f) g = inner ℝ f (siteDelta M g) := by
  rw [delta_inner]
  exact ((grad M).adjoint_inner_right f (grad M g)).symm

lemma grad_zero_of_delta_zero (f : Site M (n := n)) (hf : siteDelta M f = 0) :
    grad M f = 0 := by
  have h := delta_inner M f f
  rw [hf, inner_zero_left, real_inner_self_eq_norm_sq] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (grad M f)])

lemma delta_mem_image (f : Site M (n := n)) (hf : siteAverage M f = 0) :
    siteDelta M f ∈ gaugeImage M := ⟨⟨f,hf⟩,rfl⟩

lemma R_delta (f : Site M (n := n)) (hf : siteAverage M f = 0) :
    R M (siteDelta M f) = siteDelta M f :=
  (gaugeImage M).starProjection_eq_self_iff.mpr (delta_mem_image M f hf)

/-- The actual R gauge excludes every nonzero gradient of a Q'-null potential.
This does not replace Q' by the bond-Q kernel. -/
theorem pure_gauge_excluded (f : Site M (n := n)) (hf : siteAverage M f = 0)
    (hg : gaugeConstraint M (grad M f) = 0) : grad M f = 0 := by
  apply grad_zero_of_delta_zero M f
  change R M (siteDelta M f) = 0 at hg
  rwa [R_delta M f hf] at hg

lemma divergence_gaugePi (A : Fine M (n := n)) :
    (grad M).adjoint (gaugePi M A) =
      (grad M).adjoint A - R M ((grad M).adjoint A) := by
  change (grad M).adjoint (A-grad M (gaugePotential M A)) = _
  rw [map_sub]
  change _ - siteDelta M (gaugePotential M A) = _
  rw [potential_laplacian]

/-- Orthogonal projection acts on the divergence, NOT on the fine bond field. -/
theorem divergence_pythagoras (A : Fine M (n := n)) :
    ‖(grad M).adjoint A‖^2 = ‖(grad M).adjoint (gaugePi M A)‖^2 +
      ‖R M ((grad M).adjoint A)‖^2 := by
  rw [divergence_gaugePi]
  exact (gaugeImage M).norm_sq_eq_add_norm_sq_starProjection
    ((grad M).adjoint A) |>.trans (by rw [Submodule.starProjection_orthogonal_val]; exact add_comm _ _)

theorem divergence_contraction (A : Fine M (n := n)) :
    ‖(grad M).adjoint (gaugePi M A)‖^2 ≤ ‖(grad M).adjoint A‖^2 := by
  have h := divergence_pythagoras M A
  nlinarith [sq_nonneg ‖R M ((grad M).adjoint A)‖]

lemma gaugePi_of_feasible (A : Fine M (n := n)) (hA : gaugeConstraint M A = 0) :
    gaugePi M A = A := by
  have hp : siteDelta M (gaugePotential M A) = 0 := (potential_laplacian M A).trans hA
  change A-grad M (gaugePotential M A) = A
  rw [grad_zero_of_delta_zero M _ hp, sub_zero]

theorem gaugePi_fixed_iff (A : Fine M (n := n)) :
    gaugePi M A = A ↔ gaugeConstraint M A = 0 := by
  constructor
  · intro h; rw [←h]; exact gaugePi_feasible M A
  · exact gaugePi_of_feasible M A

theorem gaugePi_idempotent (A : Fine M (n := n)) :
    gaugePi M (gaugePi M A) = gaugePi M A :=
  gaugePi_of_feasible M _ (gaugePi_feasible M A)

/-- No choice of the algebraic site section survives on a pure gauge. -/
theorem gaugePi_grad_null (f : Site M (n := n)) (hf : siteAverage M f = 0) :
    gaugePi M (grad M f) = 0 := by
  have hd : siteDelta M (f-gaugePotential M (grad M f)) = 0 := by
    rw [map_sub, potential_laplacian]
    change siteDelta M f - R M (siteDelta M f) = 0
    rw [R_delta M f hf, sub_self]
  have hz := grad_zero_of_delta_zero M _ hd
  rw [map_sub] at hz
  exact hz

theorem gaugePi_orbit_invariant (A : Fine M (n := n))
    (f : Site M (n := n)) (hf : siteAverage M f = 0) :
    gaugePi M (A+grad M f) = gaugePi M A := by
  rw [map_add, gaugePi_grad_null M f hf, add_zero]

/-- Orthogonality is to Delta(ker Q'), not to ker Q' itself. -/
theorem feasible_iff_div_orthogonal (A : Fine M (n := n)) :
    gaugeConstraint M A = 0 ↔ (grad M).adjoint A ∈ (gaugeImage M)ᗮ := by
  exact (gaugeImage M).starProjection_apply_eq_zero_iff

/-- Exact fourth-order normal equation for the actual lattice gauge slice. -/
theorem feasible_iff_delta_div (A : Fine M (n := n)) :
    gaugeConstraint M A = 0 ↔
      ∀ f : Site M (n := n), siteAverage M f = 0 →
        inner ℝ (siteDelta M ((grad M).adjoint A)) f = 0 := by
  rw [feasible_iff_div_orthogonal, Submodule.mem_orthogonal']
  constructor
  · intro h f hf
    rw [delta_symmetric]
    exact h _ (delta_mem_image M f hf)
  · intro h x hx
    obtain ⟨f,hf⟩ := hx
    rw [←hf]
    exact (delta_symmetric M ((grad M).adjoint A) f).symm.trans (h f f.2)

/-- The gradient correction minimizes divergence on the actual Q'-null orbit. -/
theorem divergence_orbit_minimum (A : Fine M (n := n))
    (f : Site M (n := n)) (hf : siteAverage M f = 0) :
    ‖(grad M).adjoint (gaugePi M A)‖^2 ≤
      ‖(grad M).adjoint (A+grad M f)‖^2 := by
  have h := divergence_contraction M (A+grad M f)
  rwa [gaugePi_orbit_invariant M A f hf] at h

/-- Exact signed mass balance. R's norm-one estimate is not a bound on gaugePi. -/
theorem mass_balance (A : Fine M (n := n)) :
    mass M (gaugePi M A) = mass M A -
      (1/(n:ℝ)^3)*‖grad M (gaugePotential M A)‖^2 -
      2*(1/(n:ℝ)^3)*inner ℝ ((grad M).adjoint (gaugePi M A)) (gaugePotential M A) := by
  have hnorm := norm_sub_sq_real A (grad M (gaugePotential M A))
  have hi := (grad M).adjoint_inner_left (gaugePotential M A) A
  have hp := delta_inner M (gaugePotential M A) (gaugePotential M A)
  rw [real_inner_self_eq_norm_sq] at hp
  have hdiv : inner ℝ ((grad M).adjoint (gaugePi M A)) (gaugePotential M A) =
      inner ℝ ((grad M).adjoint A) (gaugePotential M A) -
        ‖grad M (gaugePotential M A)‖^2 := by
    change inner ℝ ((grad M).adjoint (A-grad M (gaugePotential M A))) _ = _
    rw [map_sub, inner_sub_left]
    change _ - inner ℝ (siteDelta M (gaugePotential M A)) _ = _
    rw [hp]
  rw [hdiv, mass, mass]
  change (1/(n:ℝ)^3)*‖A-grad M (gaugePotential M A)‖^2 = _
  rw [hnorm, ←hi]
  ring

/-- The missing mass control is on the actual physicalH, after its true R gauge. -/
theorem physicalH_mass_balance (hn : 0 < n) (B : Unit M) :
    mass M (physicalH M hn B) = mass M (H M hn B) -
      (1/(n:ℝ)^3)*‖grad M (gaugePotential M (H M hn B))‖^2 -
      2*(1/(n:ℝ)^3)*inner ℝ ((grad M).adjoint (physicalH M hn B))
        (gaugePotential M (H M hn B)) := by
  simp only [physicalH, ContinuousLinearMap.comp_apply]
  exact mass_balance M (H M hn B)

theorem physicalH_delta_div (hn : 0 < n) (B : Unit M)
    (f : Site M (n := n)) (hf : siteAverage M f = 0) :
    inner ℝ (siteDelta M ((grad M).adjoint (physicalH M hn B))) f = 0 :=
  (feasible_iff_delta_div M _).mp (physicalH_gauge M hn B) f hf

/-- Energy normalization agrees exactly with phase R at U=1. -/
theorem energy_eq_phaseR (A : Fine M (n := n)) :
    fineEnergy M A = RegU.energy n
      (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU _) (bfl2Equiv A) := by
  rw [fineEnergy, curl_norm, RegU.energy]
  congr 1
  rw [AdalyFormal.Balaban.CovU1Reduction.curlCovariantLM_trivialU_eq_flatCurlLM]
  rfl

end HConstruction.MassU1
