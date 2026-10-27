import NsCvOP4
import NsCvON4
import NsCvON5
import NsCvON3

/-!
# NsOdd12 -- `H0` along the odd staggered family: the determinant is analytic in `t` and nonzero at the flat point (lane ncwdh_strong_20261017)

For odd `ell ≥ 5` the unit-level background `Ū²` of the nested staggered family is `cartanOf (unitFld t b₂ d₂ c_u)` (NsOdd9c) -- NOT a pure gauge
(its unit loops are small but nonzero), so `H0` is not bijective by gauge covariance.  Instead:
* `H0 (neLam M R) (Q1jet ell (U t)) = Φ ∘ A(t) ∘ Ψ` with `A(t) = QlinStepL 1 ell (U t)` analytic in `t` (CvOP3) and `Φ, Ψ` fixed linear maps;
* `t ↦ det (Φ A(t) Ψ)` is analytic (`analyticAt_det_sandwich`);
* at `t = 0` the background is flat and `H0` is bijective (`H0_flat_bijective`), so the determinant is nonzero there.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)

/-- bijective endomorphism of a finite-dimensional real space iff the determinant is nonzero. -/
theorem bijective_iff_det_ne_zero {X : Type*} [AddCommGroup X] [Module ℝ X] [Module.Finite ℝ X] (f : X →ₗ[ℝ] X) :
    Function.Bijective f ↔ LinearMap.det f ≠ 0 := by
  rw [← Module.End.isUnit_iff, LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- the sandwich `Φ ∘ A(t) ∘ Ψ` has analytic determinant. -/
theorem analyticAt_det_sandwich {X Y : Type*} [AddCommGroup X] [Module ℝ X] [Module.Finite ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (Φ : Y →ₗ[ℝ] X) (Ψ : X →ₗ[ℝ] Y) {A : ℝ → Y →L[ℝ] Y} {t0 : ℝ} (hA : AnalyticAt ℝ A t0) :
    AnalyticAt ℝ (fun t => LinearMap.det (Φ ∘ₗ ((A t : Y →L[ℝ] Y) : Y →ₗ[ℝ] Y) ∘ₗ Ψ)) t0 := by
  let b := Module.finBasis ℝ X
  have hdet : ∀ t, LinearMap.det (Φ ∘ₗ ((A t : Y →L[ℝ] Y) : Y →ₗ[ℝ] Y) ∘ₗ Ψ) =
      (LinearMap.toMatrix b b (Φ ∘ₗ ((A t : Y →L[ℝ] Y) : Y →ₗ[ℝ] Y) ∘ₗ Ψ)).det := fun t => (LinearMap.det_toMatrix b _).symm
  simp only [hdet]
  have hent : ∀ i j, AnalyticAt ℝ (fun t => LinearMap.toMatrix b b (Φ ∘ₗ ((A t : Y →L[ℝ] Y) : Y →ₗ[ℝ] Y) ∘ₗ Ψ) i j) t0 := by
    intro i j
    have hentry : ∀ t, LinearMap.toMatrix b b (Φ ∘ₗ ((A t : Y →L[ℝ] Y) : Y →ₗ[ℝ] Y) ∘ₗ Ψ) i j = (b.coord i) (Φ ((A t) (Ψ (b j)))) := by
      intro t; rw [LinearMap.toMatrix_apply]; rfl
    simp only [hentry]
    have hlam : AnalyticAt ℝ (fun y : Y => (b.coord i) (Φ y)) (A t0 (Ψ (b j))) := by
      have := (LinearMap.toContinuousLinearMap ((b.coord i).comp Φ)).analyticAt (A t0 (Ψ (b j)))
      exact this
    have hA' : AnalyticAt ℝ (fun t => (A t) (Ψ (b j))) t0 :=
      AdalyFormal.CoverOmega.Struct.anal_apply hA (analyticAt_const (v := Ψ (b j)))
    exact AnalyticAt.comp (f := fun t => (A t) (Ψ (b j))) hlam hA'
  exact AdalyFormal.CoverOmega.Struct.analyticAt_det hent


section H0fam
variable {Lu : PeriodicLatticeExtent}

/-- the fixed output map of `Q1jet`: read the coarse bonds of `Λ'` from an `XS`-field. -/
noncomputable def H0Phi (ell : ℕ) (Lam : Set (PeriodicLatticeSite Lu)) : XS Lu →ₗ[ℝ] (Dset Lu ell Lam → SuTwo) where
  toFun x := fun d => ((ell : ℝ)⁻¹) • (suCoordFInv x) (d.1.1.1, d.1.2)
  map_add' x y := by funext d; simp [smul_add]
  map_smul' r x := by
    funext d
    simp only [RingHom.id_apply, Pi.smul_apply, map_smul]
    exact smul_comm ((ell : ℝ)⁻¹) r _

/-- the fixed input map: a dropped-bond field, as an `XS`-field. -/
noncomputable def H0Psi (ell : ℕ) (Lam : Set (PeriodicLatticeSite Lu)) : (Dset Lu ell Lam → SuTwo) →ₗ[ℝ] XS Lu :=
  suCoordF ∘ₗ iotaD ell Lam

theorem H0_eq_sandwich (ell : ℕ) (Lam : Set (PeriodicLatticeSite Lu)) (V : PeriodicLinkConfiguration SU2 Lu) :
    H0 Lam (Q1jet ell V) = H0Phi ell Lam ∘ₗ ((QlinStepL 1 ell V : XS Lu →L[ℝ] XS Lu) : XS Lu →ₗ[ℝ] XS Lu) ∘ₗ H0Psi ell Lam := rfl

end H0fam


variable {ell M R : ℕ} {Lu : PeriodicLatticeExtent}

theorem contDiffAt_unitFld {L : PeriodicLatticeExtent} (b d : ℝ) (cu : ℕ) (e : PeriodicLatticeEdge L) (t0 : ℝ) :
    ContDiffAt ℝ ⊤ (fun t => (unitFld t b d cu : PeriodicLatticeEdge L → ℝ) e) t0 := by
  unfold unitFld shapeFld fld
  by_cases h : e.2 = 0
  · simp only [if_pos h]
    exact (contDiffAt_id.mul contDiffAt_const).mul contDiffAt_const
  · simp only [if_neg h]
    by_cases h1 : e.2 = 1
    · simp only [if_pos h1]
      exact (contDiffAt_id.mul contDiffAt_const).mul contDiffAt_const
    · simp only [if_neg h1]
      exact contDiffAt_const

theorem unitFld_zero {L : PeriodicLatticeExtent} (b d : ℝ) (cu : ℕ) :
    (unitFld 0 b d cu : PeriodicLatticeEdge L → ℝ) = 0 := by
  funext e
  unfold unitFld shapeFld fld
  by_cases h : e.2 = 0
  · simp [h]
  · by_cases h1 : e.2 = 1
    · simp [h, h1]
    · simp [h, h1]

noncomputable def unitU (ell cu : ℕ) {Lu : PeriodicLatticeExtent} (t : ℝ) : PeriodicLinkConfiguration SU2 Lu :=
  cartanOf (unitFld t (b2 ell) (d2 ell) cu)

theorem Pn_unitBgU_odd (hell3 : 3 ≤ ell) (hO : ell % 2 = 1) (h5 : 5 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a : ℝ)
    (cu : ℕ) (hcu : neC ell M R = ell * ell * cu) (t : ℝ) (ht : |t| < 8 / 5) :
    (Pn ell M R (by omega) a t).unitBgU = unitU ell cu t := by
  have hell : 0 < ell := by omega
  have G := nested_oddGeo hell3 hO h5 hdvd hM hR
  show unitBg ell 2 (neLu M R) hell (UbarTower su2LogExp ell (stagCfg (neC ell M R) t : PeriodicLinkConfiguration SU2 (scaleUp ell 2 (neLu M R))) 2) = _
  rw [unitBg_eq_cartan hell G t ht, phiu_eq_unitFld hell G cu hcu t]
  rfl

theorem unitU_reg (hO : ell % 2 = 1) (h5 : 5 ≤ ell) (hN : 2 ∣ Lu 1 + 1) (cu : ℕ) (t : ℝ) (ht : |t| < 8 / 5) :
    RegBg2 1 ell (unitU ell cu t : PeriodicLinkConfiguration SU2 Lu) :=
  regBg2_cartanOf_of_loops (fun cc x hx => lt_of_le_of_lt
    (unitFld_loop_le hN hO cu t (b2 ell) (d2 ell) (b2_range h5) (d2_range h5) cc x hx) (lt_trans ht pi_gt_8_5))

theorem unitU_zero (ell cu : ℕ) : (unitU ell cu 0 : PeriodicLinkConfiguration SU2 Lu) = (fun _ : PeriodicLatticeEdge Lu => (1 : SU2)) := by
  funext e
  simp only [unitU, unitFld_zero, cartanOf, Pi.zero_apply, cartan_zero]

/-- **`H0` along the odd staggered family**: the determinant is analytic on `(-8/5, 8/5)`, nonzero at the flat point `t = 0`,
and nonzero implies `H0` bijective. -/
theorem pn_H0_odd (hell3 : 3 ≤ ell) (hO : ell % 2 = 1) (h5 : 5 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a : ℝ) :
    ∃ dH : ℝ → ℝ, AnalyticOnNhd ℝ dH (Ioo (-(8 / 5 : ℝ)) (8 / 5)) ∧ dH 0 ≠ 0 ∧
      ∀ t : ℝ, |t| < 8 / 5 → dH t ≠ 0 → Function.Bijective (H0 (neLam M R) (Pn ell M R (by omega) a t).Q1) := by
  have hell : 0 < ell := by omega
  have G := nested_oddGeo hell3 hO h5 hdvd hM hR
  obtain ⟨cu, hcu⟩ := G.hcd
  have hN := two_dvd_unit hO G.hN
  have hana : ∀ t0 : ℝ, AdalyFormal.CoverOmega.Struct.AnaFam (fun t => (unitU ell cu t : PeriodicLinkConfiguration SU2 (neLu M R))) t0 := fun t0 =>
    AdalyFormal.CoverOmega.Struct.AnaFam_cartanOf (fun t => unitFld t (b2 ell) (d2 ell) cu) (fun e => contDiffAt_unitFld _ _ cu e t0)
  have hD : AnalyticOnNhd ℝ (fun t => LinearMap.det (H0 (neLam M R) (Q1jet ell (unitU ell cu t : PeriodicLinkConfiguration SU2 (neLu M R)))))
      (Ioo (-(8 / 5 : ℝ)) (8 / 5)) := by
    intro t0 ht0
    have hA := AdalyFormal.CoverOmega.Struct.QlinStepL_analytic 1 ell (fun t => (unitU ell cu t : PeriodicLinkConfiguration SU2 (neLu M R)))
      (hana t0) (unitU_reg hO h5 hN cu t0 (abs_lt.2 ht0))
    have e : (fun t => LinearMap.det (H0 (neLam M R) (Q1jet ell (unitU ell cu t : PeriodicLinkConfiguration SU2 (neLu M R))))) =
        fun t => LinearMap.det (H0Phi ell (neLam M R) ∘ₗ ((QlinStepL 1 ell (unitU ell cu t : PeriodicLinkConfiguration SU2 (neLu M R)) : XS (neLu M R) →L[ℝ] XS (neLu M R)) : XS (neLu M R) →ₗ[ℝ] XS (neLu M R)) ∘ₗ H0Psi ell (neLam M R)) := by
      funext t; rw [H0_eq_sandwich]
    rw [e]
    exact analyticAt_det_sandwich (H0Phi ell (neLam M R)) (H0Psi ell (neLam M R)) hA
  refine ⟨fun t => LinearMap.det (H0 (neLam M R) (Q1jet ell (unitU ell cu t : PeriodicLinkConfiguration SU2 (neLu M R)))), hD, ?_, ?_⟩
  · show LinearMap.det (H0 (neLam M R) (Q1jet ell (unitU ell cu 0 : PeriodicLinkConfiguration SU2 (neLu M R)))) ≠ 0
    rw [unitU_zero]
    exact (bijective_iff_det_ne_zero _).mp (H0_flat_bijective hell (unit_hdiv hdvd hM) (neLam M R))
  · intro t ht hDt
    have h1 : (Pn ell M R hell a t).Q1 = Q1jet ell (unitU ell cu t : PeriodicLinkConfiguration SU2 (neLu M R)) :=
      congrArg (Q1jet ell) (Pn_unitBgU_odd hell3 hO h5 hdvd hM hR a cu hcu t ht)
    rw [h1]
    exact (bijective_iff_det_ne_zero _).mpr hDt

#print axioms bijective_iff_det_ne_zero
#print axioms analyticAt_det_sandwich
#print axioms pn_H0_odd

end AdalyFormal.CoverOmega
