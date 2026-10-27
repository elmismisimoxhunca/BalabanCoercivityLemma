import DK3FineAnalytic

/-! The genuine nonlinear depth-three modified average, not the linear Q composite
and not the outer unitD2. The input exponential uses eta=1/8 ONCE. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 1000
noncomputable section
open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
attribute [local instance 20000] AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo
  AdalyFormal.Balaban.SuTwoInner.instInnerProductSpaceSuTwo
attribute [local irreducible] AdalyFormal.Balaban.AdmissibleSubspace.blockOf
  AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice
  HConstruction.DK3.unitCoordinates HConstruction.DK3.CovarianceScale.outputCoordinates
namespace HConstruction.DK3.FineScale
open CovarianceScale (F outputCoordinates outputBondEquiv)
open HConstruction.Carrier HConstruction.Predicate HConstruction.SmallNFSmooth
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Log_one)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SuTwoInner
open AdalySI1.Multiscale.M1 (iteratedAverage modifiedAverageS)
local instance : SeminormedAddCommGroup SuTwo := instNormedAddCommGroupSuTwo.toSeminormedAddCommGroup
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

def fluctuation (A : F) : PeriodicLinkConfiguration SU2 fineL :=
  bondExp 8 (fineCoordinates A)

theorem fluctuation_zero : fluctuation 0 = trivialU fineL := by
  simp only [fluctuation, map_zero, bondExp_zero]

def nonlinearTower (t : ℝ) (A : F) (j : ℕ) : PeriodicLinkConfiguration SU2 fineL :=
  iteratedAverage (tower t) 2 j (fluctuation A)

theorem nonlinearTower_zero (t : ℝ) (j : ℕ) : nonlinearTower t 0 j = trivialU fineL := by
  induction j with
  | zero => exact fluctuation_zero
  | succ j ih =>
    change modifiedAverageS (2^j) (tower t j) 2 (nonlinearTower t 0 j) = _
    rw [ih, Analytic.modified_zero]

theorem smooth_fluctuation (b : Bond fineL) :
    ContDiffAt ℝ ⊤ (fun z : ℝ × F => (fluctuation z.2 b : M2)) (0,0) := by
  have hc := (fineCoordinates (L := fineL)).toLinearMap.toContinuousLinearMap.contDiff.contDiffAt.comp
    (0,0) (contDiffAt_snd (𝕜 := ℝ) (n := ⊤) (p := ((0,0) : ℝ × F)))
  have h := smooth_bondExp (L := fineL) 8 b
  have hz : (fineCoordinates (L := fineL)) (0 : F) = 0 := map_zero _
  rw [← hz] at h
  have hd := h.comp (0,0) hc
  exact hd

theorem smooth_nonlinearTower (j : ℕ) (b : Bond fineL) :
    ContDiffAt ℝ ⊤ (fun z : ℝ × F => (nonlinearTower z.1 z.2 j b : M2)) (0,0) := by
  induction j generalizing b with
  | zero => exact smooth_fluctuation b
  | succ j ih =>
    have hu (e : Bond fineL) : ContDiffAt ℝ ⊤
        (fun z : ℝ × F => (tower z.1 j e : M2)) (0,0) := by
      have h := (smooth_tower j e).comp (0,0)
        (contDiffAt_fst (𝕜 := ℝ) (n := ⊤) (p := ((0,0) : ℝ × F)))
      exact h
    exact Analytic.smooth_modified hu ih (tower_zero j) (nonlinearTower_zero 0 j) (2^j) 2 b

/-- CMP99b (3.13) at depth 3, in the anti-Hermitian chart. Its physical
normalization is ell^3 eta=1, so no output scalar is needed. -/
def nonlinearQ (t : ℝ) (A : F) : K :=
  outputCoordinates.symm (fun c => Unit.recover (su2Log (nonlinearTower t A 3 (c.1.1,c.2))))

theorem nonlinearQ_exact (t : ℝ) (A : F) (c : CoarseBond fineL 8) :
    ((outputCoordinates (nonlinearQ t A) c : SuTwo) : M2) =
      su2Log (iteratedAverage (tower t) 2 3 (bondExp 8 (fineCoordinates A)) (c.1.1,c.2)) := by
  simp only [nonlinearQ, LinearEquiv.apply_symm_apply]
  have h := Unit.recover_coe
    (AdalyFormal.DeltaKR66.principalSuTwoLog (nonlinearTower t A 3 (c.1.1,c.2)))
  exact congrArg (fun X : SuTwo => (X : M2)) h

theorem nonlinearQ_zero (t : ℝ) : nonlinearQ t 0 = 0 := by
  apply outputCoordinates.injective
  funext c
  simp only [nonlinearQ, LinearEquiv.apply_symm_apply, nonlinearTower_zero,
    trivialU, su2Log_one, map_zero, Pi.zero_apply]

theorem smooth_nonlinearQ_joint :
    ContDiffAt ℝ ⊤ (fun z : ℝ × F => nonlinearQ z.1 z.2) (0,0) := by
  apply outputCoordinates.symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp (0,0)
  apply contDiffAt_pi.mpr
  intro c
  apply Unit.recover.contDiff.contDiffAt.comp
  apply HConstruction.LocalLog.contDiffAt_log_at_one (smooth_nonlinearTower 3 (c.1.1,c.2))
  rw [nonlinearTower_zero]
  rfl

attribute [local irreducible] nonlinearQ nonlinearTower fluctuation

def firstPartial (z : ℝ × F) : F →L[ℝ] K := fderiv ℝ (nonlinearQ z.1) z.2

theorem smooth_firstPartial : ContDiffAt ℝ ⊤ firstPartial (0,0) := by
  have hg : ContDiffAt ℝ ⊤ (fun z : (ℝ × F) × F => (z.1.1,z.2)) ((0,0),0) :=
    (contDiffAt_fst.fst).prodMk contDiffAt_snd
  exact (smooth_nonlinearQ_joint.comp ((0,0),0) hg).fderiv contDiffAt_snd (by simp)

/-- Internal fine Hessian. Both input arguments are in the full F. -/
def averagingHessian (t : ℝ) : F →L[ℝ] F →L[ℝ] K :=
  fderiv ℝ (fderiv ℝ (nonlinearQ t)) 0

def averagingC2 (t : ℝ) (A : F) : K := (1/2 : ℝ) • averagingHessian t A A

theorem smooth_averagingHessian : ContDiffAt ℝ ⊤ averagingHessian 0 :=
  smooth_firstPartial.fderiv contDiffAt_const (by simp)

theorem eventually_nonlinearQ_smooth : ∀ᶠ t in nhds (0 : ℝ),
    ContDiffAt ℝ 2 (nonlinearQ t) 0 := by
  have hev : ∀ᶠ z in nhds ((0,0) : ℝ × F),
      ContDiffAt ℝ 2 (fun z : ℝ × F => nonlinearQ z.1 z.2) z :=
    (smooth_nonlinearQ_joint.of_le (by simp)).eventually (by simp)
  have hl : Filter.Tendsto (fun t : ℝ => (t,(0:F))) (nhds 0) (nhds ((0,0) : ℝ × F)) :=
    continuousAt_id.prodMk continuousAt_const
  filter_upwards [hl.eventually hev] with t ht
  exact ht.comp 0 (contDiffAt_const.prodMk contDiffAt_id)

theorem jet_radius_exists : ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r →
    ContDiffAt ℝ 2 (nonlinearQ t) 0 := by
  obtain ⟨r,hr,hb⟩ := Metric.eventually_nhds_iff.mp eventually_nonlinearQ_smooth
  exact ⟨r,hr,fun t ht => hb (by simpa only [dist_zero_right,Real.norm_eq_abs] using ht)⟩

def jetThreshold : ℝ := min interval (Classical.choose jet_radius_exists / 2)

theorem jetThreshold_pos : 0 < jetThreshold :=
  lt_min interval_pos (half_pos (Classical.choose_spec jet_radius_exists).1)

theorem nonlinearQ_smooth_small (t : ℝ) (ht : |t| ≤ jetThreshold) :
    ContDiffAt ℝ 2 (nonlinearQ t) 0 := by
  apply (Classical.choose_spec jet_radius_exists).2 t
  have h := ht.trans (min_le_right interval (Classical.choose jet_radius_exists / 2))
  linarith [(Classical.choose_spec jet_radius_exists).1]

/-- Unconditional positive interval: not a totalized-derivative assumption. -/
theorem averagingC2_ray (t : ℝ) (ht : |t| ≤ jetThreshold) (A : F) :
    averagingC2 t A = HConstruction.Reproduced.Dtilde2Shape (nonlinearQ t) A := by
  unfold HConstruction.Reproduced.Dtilde2Shape HConstruction.Reproduced.taylorQuadraticTerm
  rw [Unit.second_ray_eq_hessian (nonlinearQ_smooth_small t ht)]
  rfl

theorem averagingC2_homogeneous (t r : ℝ) (A : F) :
    averagingC2 t (r • A) = r^2 • averagingC2 t A := by
  simp only [averagingC2, map_smul, _root_.smul_apply, smul_smul]
  congr 1
  ring

#print axioms nonlinearQ_exact
#print axioms smooth_nonlinearQ_joint
#print axioms averagingC2_ray
#print axioms jetThreshold_pos
end HConstruction.DK3.FineScale
