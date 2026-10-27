import GaugeMass
/-! Unconditional normal equations on GenK's full fine carrier. No spectral
budget, assumed estimate, or target coercivity premise occurs below. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HConstruction.MassU1
open AdalyFormal.Target.ClayStatement
open HConstruction.GenK
variable (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n)
attribute [local irreducible] incoming curl H physicalH gaugePotential

lemma physicalH_curl (B : Unit M) :
    curl M (physicalH M hn B) = curl M (H M hn B) := by
  simp only [physicalH, ContinuousLinearMap.comp_apply, gaugePi_curl]

/-- The attained minimizer satisfies the full Euler equation on ker incoming.
This is not an equation only on a postulated small subspace. -/
theorem physicalH_curl_normal (B : Unit M) (Z : Fine M (n := n))
    (hZ : incoming M hn Z = 0) :
    inner ℝ (curl M (physicalH M hn B)) (curl M Z) = 0 := by
  have hz : curl M Z ∈ curlImage M hn := ⟨⟨Z,hZ⟩,rfl⟩
  rw [physicalH_curl, curl_H]
  exact (curlImage M hn).starProjection_inner_eq_zero _ _ hz

/-- Exact energy error on every incoming fibre, with n^-1 physical scaling. -/
theorem physicalH_energy_pythagoras (B : Unit M) (A : Fine M (n := n))
    (hq : incoming M hn A = B) :
    fineEnergy M A = fineEnergy M (physicalH M hn B) +
      fineEnergy M (A-physicalH M hn B) := by
  have hz : incoming M hn (A-physicalH M hn B) = 0 := by
    rw [map_sub, hq, physicalH_Q, sub_self]
  have horth := physicalH_curl_normal M hn B _ hz
  have hsum : curl M A = curl M (physicalH M hn B) + curl M (A-physicalH M hn B) := by
    rw [map_sub]; abel
  unfold fineEnergy
  conv_lhs => rw [hsum, norm_add_sq_real, horth]
  ring

/-- The actual lift solves BOTH distinct normal equations and its actual Q
constraint. The second normal equation is not div(H B)=0. -/
theorem actual_normal_equations (B : Unit M) :
    incoming M hn (physicalH M hn B) = B ∧
    (∀ Z : Fine M (n := n), incoming M hn Z = 0 →
      inner ℝ (curl M (physicalH M hn B)) (curl M Z) = 0) ∧
    (∀ f : Site M (n := n), siteAverage M f = 0 →
      inner ℝ (siteDelta M ((grad M).adjoint (physicalH M hn B))) f = 0) :=
  ⟨physicalH_Q M hn B, physicalH_curl_normal M hn B, physicalH_delta_div M hn B⟩

/-- Full all-depth version on every unit extent; this is a normal-equation
characterization only, NOT an all-depth mass estimate. -/
theorem actual_normal_equations_every_depth (k : ℕ) (B : Unit M) :
    let hk : 0 < 2^k := pow_pos (by decide : 0 < 2) k
    incoming M hk (physicalH M hk B) = B ∧
    (∀ Z : Fine M (n := 2^k), incoming M hk Z = 0 →
      inner ℝ (curl M (physicalH M hk B)) (curl M Z) = 0) ∧
    (∀ f : Site M (n := 2^k), siteAverage M f = 0 →
      inner ℝ (siteDelta M ((grad M).adjoint (physicalH M hk B))) f = 0) :=
  actual_normal_equations M (pow_pos (by decide : 0 < 2) k) B

/-- Different gauge-fixed minimizers in one fibre can only differ by a
simultaneously incoming-null, curl-null, R-gauge-null field. No assertion that
this joint kernel vanishes is silently imported. -/
theorem minimizer_difference (B : Unit M) (A : Fine M (n := n))
    (hq : incoming M hn A = B) (hg : gaugeConstraint M A = 0)
    (he : fineEnergy M A = fineEnergy M (physicalH M hn B)) :
    incoming M hn (A-physicalH M hn B) = 0 ∧
    gaugeConstraint M (A-physicalH M hn B) = 0 ∧
    curl M (A-physicalH M hn B) = 0 := by
  refine ⟨by rw [map_sub,hq,physicalH_Q,sub_self],
    by rw [map_sub,hg,physicalH_gauge,sub_self],?_⟩
  have hp := physicalH_energy_pythagoras M hn B A hq
  have hz : fineEnergy M (A-physicalH M hn B) = 0 := by linarith
  unfold fineEnergy at hz
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hs := (mul_eq_zero.mp hz).resolve_left (by positivity : (1/(n:ℝ)) ≠ 0)
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (curl M (A-physicalH M hn B))])

/-- If two representatives of one Q'-null gradient orbit are R-fixed, they
coincide. This is proved without a norm bound for an algebraic section. -/
theorem gauge_orbit_unique (A A' : Fine M (n := n))
    (f : Site M (n := n)) (hf : siteAverage M f = 0)
    (hAA' : A' = A+grad M f)
    (hg : gaugeConstraint M A = 0) (hg' : gaugeConstraint M A' = 0) : A' = A := by
  rw [←gaugePi_of_feasible M A' hg',hAA',gaugePi_orbit_invariant M A f hf,
    gaugePi_of_feasible M A hg]

end HConstruction.MassU1
