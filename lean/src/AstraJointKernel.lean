import CurvatureControl
import SiteConst
/-! The inhomogeneous replacement for an axial tree: Q removes the harmonic
classes, and the actual R gauge removes the remaining Q'-null gradients.
This is a kernel/uniqueness result, not a uniform quantitative estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace HConstruction.MassCMP122Astra
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU coarseRestrictSiteCovariant periodicLatticeShiftEquiv)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open HConstruction.GenK HConstruction.MassU1
variable (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n)
attribute [local irreducible] incoming curl H physicalH gaugePotential blockOf CoarseLattice

def directionConstant (c : Fin 3 → SuTwo) : Fine M (n := n) :=
  bfl2Equiv.symm (fun b => c b.2)

def siteConstant (v : SuTwo) : Site M (n := n) :=
  (WithLp.linearEquiv 2 ℝ _).symm (fun _ => v)

lemma grad_siteConstant (v : SuTwo) : grad M (siteConstant M (n := n) v) = 0 := by
  apply bfl2Equiv.injective
  funext b
  rw [grad_apply]
  change (n:ℝ) • (v-v) = 0
  rw [sub_self,smul_zero]

include hn in
lemma siteAverage_constant (v : SuTwo) (y : Centers M (n := n)) :
    siteAverage M (siteConstant M v) y = v := by
  rw [siteAverage_apply]
  change coarseRestrictSiteCovariant n (fun _ => v) y.1 = v
  simp only [coarseRestrictSiteCovariant, Finset.sum_const]
  rw [card_blockOf_of_coarse (fineTiling M hn) y.2, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Nat.cast_pow, one_div_mul_cancel (pow_ne_zero 3 hnR), one_smul]

lemma incoming_directionConstant (c : Fin 3 → SuTwo) (b : Bond M) :
    bfl2Equiv (incoming M hn (directionConstant M c)) b = c b.2 := by
  rw [incoming_apply]
  change lineCoarseRestrictSuTwo n (fun e => c e.2) (bonds M hn b) = _
  simp only [lineCoarseRestrictSuTwo, Finset.sum_const, Finset.card_range]
  change (1/(n:ℝ)^4) • (blockOf (sites M hn b.1).1 n).card • n • c b.2 = c b.2
  rw [card_blockOf_of_coarse (fineTiling M hn) (sites M hn b.1).2]
  simp only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_pow]
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (1/(n:ℝ)^4)*((n:ℝ)^3*(n:ℝ)) = 1 := by field_simp
  rw [he,one_smul]

/-- The physical n in grad cancels the 1/n in the faithful line-Q Ward identity. -/
lemma incoming_grad (f : Site M (n := n)) (b : Bond M) :
    bfl2Equiv (incoming M hn (grad M f)) b =
      siteAverage M f (sites M hn (periodicLatticeShift b.1 b.2)) -
      siteAverage M f (sites M hn b.1) := by
  have hg : bfl2Equiv (grad M f) =
      (n:ℝ) • gradValueCovariant (trivialU (fineExtent M n)) (fun x => f x) := by
    funext e
    rw [grad_apply]
    simp only [Pi.smul_apply, gradValueCovariant, trivialU, RMap_one, LinearMap.id_apply]
  rw [incoming_apply, ← lineCoarseRestrictCov_trivialU, hg, lineCoarseRestrictCov_smul]
  change (n:ℝ) • lineCoarseRestrictCov (trivialU _) n
    (gradValueCovariant (trivialU _) (fun x => f x)) (sites M hn b.1,b.2) = _
  rw [lineCoarseRestrictCov_gradCovariant_trivialU_intertwines hn
    (fineTiling M hn b.2) (sites M hn b.1).2, smul_smul]
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [mul_one_div_cancel hnR, one_smul, siteAverage_apply, siteAverage_apply, sites_shift]

include hn in
/-- All periodic cohomology is retained until the true Q constraint is used. -/
theorem curl_hodge (A : Fine M (n := n)) (hA : curl M A = 0) :
    ∃ (f : Site M (n := n)) (c : Fin 3 → SuTwo),
      A = grad M f + directionConstant M c := by
  classical
  let β := Module.finBasis ℝ SuTwo
  have hc (p : PeriodicLatticePlaquette (fineExtent M n)) :
      AdalyFormal.Balaban.CovU1Reduction.flatCurlValue (bfl2Equiv A) p = 0 := by
    have h := congrArg (fun X : Plaq M (n := n) => X p) hA
    simpa only [curl_apply, PiLp.zero_apply] using h
  have hs (i : Fin (Module.finrank ℝ SuTwo)) :
      AdalyFormal.Balaban.U1AnchorPoincare.CurlFree
        (fun b => β.repr (bfl2Equiv A b) i) := by
    intro p
    have h := congrArg (fun X : SuTwo => β.repr X i) (hc p)
    simpa [AdalyFormal.Balaban.CovU1Reduction.flatCurlValue,
      AdalyFormal.Balaban.LatticeOperators.curlValue, map_add, map_sub] using h
  choose f c he using fun i =>
    AdalyFormal.Balaban.U1AnchorPoincare.curlFree_eq_grad_add_const (hs i)
  let ff : Site M (n := n) := (WithLp.linearEquiv 2 ℝ _).symm
    (fun x => (1/(n:ℝ)) • ∑ i, f i x • β i)
  let cc : Fin 3 → SuTwo := fun μ => ∑ i, c i μ • β i
  refine ⟨ff,cc,?_⟩
  apply bfl2Equiv.injective
  funext b
  have hh : bfl2Equiv A b =
      (∑ i, f i (periodicLatticeShift b.1 b.2) • β i) -
      (∑ i, f i b.1 • β i) + ∑ i, c i b.2 • β i := by
    calc
      bfl2Equiv A b = ∑ i, β.repr (bfl2Equiv A b) i • β i := (β.sum_repr _).symm
      _ = ∑ i, (f i (periodicLatticeShift b.1 b.2) - f i b.1 + c i b.2) • β i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [he i b]
      _ = _ := by simp only [add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [map_add, Pi.add_apply, grad_apply]
  change _ = (n:ℝ) • ((1/(n:ℝ)) • _ - (1/(n:ℝ)) • _) + cc b.2
  rw [← smul_sub, smul_smul, mul_one_div_cancel (by exact_mod_cast hn.ne' : (n:ℝ) ≠ 0), one_smul]
  exact hh

/-- The all-depth, all-extent exactness missing from the earlier mass lanes. -/
theorem curl_Q_kernel_potential (A : Fine M (n := n))
    (hC : curl M A = 0) (hQ : incoming M hn A = 0) :
    ∃ f : Site M (n := n), siteAverage M f = 0 ∧ A = grad M f := by
  classical
  obtain ⟨f,c,hA⟩ := curl_hodge M hn A hC
  let g : PeriodicLatticeSite M → SuTwo := fun x => siteAverage M f (sites M hn x)
  have he (x : PeriodicLatticeSite M) (μ : Fin 3) :
      g (periodicLatticeShift x μ) - g x + c μ = 0 := by
    have h := congrArg (fun X => bfl2Equiv X (x,μ)) hQ
    rw [hA, map_add, map_add, Pi.add_apply, incoming_grad,
      incoming_directionConstant, map_zero] at h
    exact h
  have hc (μ : Fin 3) : c μ = 0 := by
    have hh := Finset.sum_eq_zero (s := Finset.univ) (fun x _ => he x μ)
    have hsum : (∑ x : PeriodicLatticeSite M, g (periodicLatticeShift x μ)) = ∑ x, g x :=
      Equiv.sum_comp (periodicLatticeShiftEquiv μ) g
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum,
      sub_self, zero_add, Finset.sum_const, Finset.card_univ] at hh
    rw [← Nat.cast_smul_eq_nsmul ℝ] at hh
    exact (smul_eq_zero.mp hh).resolve_left (by
      exact_mod_cast (ne_of_gt (Fintype.card_pos (α := PeriodicLatticeSite M))))
  have hg : gradValueCovariant (trivialU M) g = 0 := by
    funext b
    have h := he b.1 b.2
    rw [hc,add_zero] at h
    simpa only [gradValueCovariant,trivialU,RMap_one,LinearMap.id_apply,Pi.zero_apply] using h
  let z : PeriodicLatticeSite M := fun _ => 0
  have hconst := HConstruction.G0CoerceFinal.Reproduced.const_of_grad_eq_zero g hg
  have hAz : A = grad M f := by
    rw [hA]
    have hz : directionConstant M (n := n) c = 0 := by
      apply bfl2Equiv.injective
      funext b
      exact hc b.2
    rw [hz,add_zero]
  refine ⟨f-siteConstant M (g z), ?_, ?_⟩
  · rw [map_sub]
    funext y
    change siteAverage M f y - siteAverage M (siteConstant M (g z)) y = 0
    rw [siteAverage_constant M hn]
    have hy : siteAverage M f y = g ((sites M hn).symm y) := by simp only [g, Equiv.apply_symm_apply]
    rw [hy,hconst _ z,sub_self]
  · rw [map_sub,grad_siteConstant,sub_zero]
    exact hAz

/-- Inhomogeneous analogue of the tree's qualitative injectivity. No mass
constant, compactness budget, or lower spectral bound is an assumption. -/
theorem joint_kernel_zero (A : Fine M (n := n))
    (hC : curl M A = 0) (hQ : incoming M hn A = 0)
    (hR : gaugeConstraint M A = 0) : A = 0 := by
  obtain ⟨f,hf,hA⟩ := curl_Q_kernel_potential M hn A hC hQ
  rw [hA] at hR ⊢
  exact pure_gauge_excluded M f hf hR

/-- A competitor with the same curl and incoming datum identifies the actual
choice-defined minimizer after imposing the actual R gauge. -/
theorem physicalH_eq_of_same_curl (B : Unit M) (A : Fine M (n := n))
    (hQ : incoming M hn A = B) (hR : gaugeConstraint M A = 0)
    (hC : curl M A = curl M (physicalH M hn B)) : A = physicalH M hn B := by
  apply sub_eq_zero.mp
  apply joint_kernel_zero M hn
  · rw [map_sub,hC,sub_self]
  · rw [map_sub,hQ,physicalH_Q,sub_self]
  · rw [map_sub,hR,physicalH_gauge,sub_self]

/-- The earlier energy minimizer difference result now yields uniqueness at
every depth, not just on a fixed benchmark torus. -/
theorem physicalH_unique_minimizer (B : Unit M) (A : Fine M (n := n))
    (hQ : incoming M hn A = B) (hR : gaugeConstraint M A = 0)
    (hE : fineEnergy M A = fineEnergy M (physicalH M hn B)) :
    A = physicalH M hn B := by
  obtain ⟨hq,hr,hc⟩ := minimizer_difference M hn B A hQ hR hE
  exact sub_eq_zero.mp (joint_kernel_zero M hn _ hc hq hr)
end HConstruction.MassCMP122Astra
