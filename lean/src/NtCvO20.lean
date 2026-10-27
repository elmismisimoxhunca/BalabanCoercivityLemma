import NtOdd10

/-!
# CvO20 -- `QlinCompX` of the staggered tower on Z-fields (lane omega)

`stag_QlinCompX_Z`: for `θ` with `FormF 1 f θ` (a sigma_3, direction-1, transverse-constant field) and `StagPar L ell` (`ell` even, or odd `≥ 3` with the odd-block geometry; `|t| < tcap ell`; `ell^2 ∣ N_μ`):
`QlinCompX ell bg 1 (aF θ) = aF (thetaSeq ell 1 θ)`, `QlinCompX ell bg 2 (aF θ) = aF (thetaSeq ell 2 θ)`, with
`FormF (ell^j) (fSum ell j f) (thetaSeq ell j θ)`.  I.e. on the Z-sector the genuine bond constraint `L^j Q_j(U)` of the staggered tower is the sum of
`ell^j` consecutive slices, for the actual `fderiv`-defined operator at angles `t ≈ π/2`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2 (XS qCompX QlinCompX QlinStepX)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge UbarTower UbarTower_succ UbarTower_zero)

variable {L : PeriodicLatticeExtent}

theorem QlinCompX_zero (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) :
    QlinCompX ell bg 0 = ContinuousLinearMap.id ℝ (XS L) := by
  unfold QlinCompX
  exact fderiv_id

theorem stag_QlinCompX_Z (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : StagPar L ell) (hell : 0 < ell) (hdiv : ∀ μ, ell * ell ∣ L μ + 1)
    (c : ℕ) (t : ℝ) (htπ : |t| < tcap ell) (hc1 : ell ≤ c) (hc2 : c + ell * ell < L 0 + 1)
    {f : ℕ → ℝ} {θ : PeriodicLatticeEdge L → ℝ} (hθ : FormF 1 f θ) :
    QlinCompX ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 1 (aF θ) = aF (thetaSeq ell 1 θ) ∧
    QlinCompX ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 2 (aF θ) = aF (thetaSeq ell 2 θ) ∧
    FormF ell (fSum ell 1 f) (thetaSeq ell 1 θ) ∧ FormF (ell ^ 2) (fSum ell 2 f) (thetaSeq ell 2 θ) := by
  have hreg := stag_regTower_u hN hE hell c t htπ hc1 hc2
  have hdiv1 : ∀ μ, ell ∣ L μ + 1 := fun μ => dvd_trans (dvd_mul_right ell ell) (hdiv μ)
  have hdiv0 : ∀ μ, 1 * ell ∣ L μ + 1 := fun μ => by rw [one_mul]; exact hdiv1 μ
  -- level 1
  have hF1 : FormF (1 * ell) (fun v => ∑ n ∈ Finset.range ell, f (v + 1 * n)) (Rsig 1 ell θ) :=
    formF_Rsig one_pos hell hdiv0 hθ
  have h1 : QlinCompX ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 1 (aF θ) = aF (Rsig 1 ell θ) := by
    have := QlinCompX_succ2 ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 2 hreg 0 (by norm_num)
    rw [zero_add] at this
    rw [this, ContinuousLinearMap.comp_apply, QlinCompX_zero]
    simp only [ContinuousLinearMap.id_apply, pow_zero, UbarTower_zero, stagCfg_eq]
    exact QlinStepX_sigma3 1 ell (stagφ c t) (stag_hphi0_u hN hE c t htπ)
      (by simpa [stagCfg_eq, pow_zero, UbarTower_zero] using hreg 0 (by norm_num)) θ
  -- level 2
  have hF1' : FormF ell (fSum ell 1 f) (thetaSeq ell 1 θ) := by
    show FormF ell (fun v => ∑ n ∈ Finset.range ell, f (v + ell ^ 0 * n)) (Rsig (ell ^ 0) ell θ)
    simpa [pow_zero] using hF1
  have hdiv2 : ∀ μ, ell ^ 1 * ell ∣ L μ + 1 := fun μ => by rw [pow_one]; exact hdiv μ
  have hF2 : FormF (ell ^ 1 * ell) (fun v => ∑ n ∈ Finset.range ell, (fSum ell 1 f) (v + ell ^ 1 * n)) (Rsig (ell ^ 1) ell (thetaSeq ell 1 θ)) :=
    formF_Rsig (pow_pos hell 1) hell hdiv2 (by simpa [pow_one] using hF1')
  refine ⟨h1, ?_, hF1', ?_⟩
  · have := QlinCompX_succ2 ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 2 hreg 1 (by norm_num)
    rw [this, ContinuousLinearMap.comp_apply, h1]
    have hb1 : UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) 1 = cartanOf (phiU ell c t) := by
      simp only [UbarTower_succ, UbarTower_zero, pow_zero]
      exact bg1_eq_u hN hE hell c t htπ hc1 hc2
    rw [hb1]
    have hreg1 : RegBg2 (ell ^ 1) ell (cartanOf (phiU ell c t) : PeriodicLinkConfiguration SU2 L) := by
      have := hreg 1 (by norm_num); rwa [hb1] at this
    rw [QlinStepX_sigma3 (ell ^ 1) ell (phiU ell c t) (by simpa [pow_one] using stag_hphi1_u hN hE hell c t htπ hc2) hreg1]
    rfl
  · simpa [thetaSeq, fSum, pow_two, pow_one] using hF2



open AdalyFormal.IngredientFamilyR2 (C2CompX C2StepX)

theorem C2CompX_zero (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (a : XS L) : C2CompX ell bg 0 a = 0 := by
  unfold C2CompX
  have : fderiv ℝ (qCompX ell bg 0) = fun _ => ContinuousLinearMap.id ℝ (XS L) := by
    funext x; exact fderiv_id
  rw [this]
  simp

/-- **the staggered tower on ARBITRARY sigma_3 fields**: `Q_j` is `Rsig`-iterated and `C^{(2)}_j` vanishes, for `j = 1, 2`. -/
theorem stag_levels_sigma3 (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : StagPar L ell) (hell : 0 < ell)
    (c : ℕ) (t : ℝ) (htπ : |t| < tcap ell) (hc1 : ell ≤ c) (hc2 : c + ell * ell < L 0 + 1) (θ : PeriodicLatticeEdge L → ℝ) :
    QlinCompX ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 1 (aF θ) = aF (thetaSeq ell 1 θ) ∧
    QlinCompX ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 2 (aF θ) = aF (thetaSeq ell 2 θ) ∧
    C2CompX ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 1 (aF θ) = 0 ∧
    C2CompX ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 2 (aF θ) = 0 := by
  have hreg := stag_regTower_u hN hE hell c t htπ hc1 hc2
  have hb0 : UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) 0 = cartanOf (stagφ c t) := by
    rw [UbarTower_zero]; exact stagCfg_eq c t
  have hb1 : UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) 1 = cartanOf (phiU ell c t) := by
    simp only [UbarTower_succ, UbarTower_zero, pow_zero]
    exact bg1_eq_u hN hE hell c t htπ hc1 hc2
  have hreg0 : RegBg2 1 ell (cartanOf (stagφ c t) : PeriodicLinkConfiguration SU2 L) := by
    have := hreg 0 (by norm_num); rwa [hb0, pow_zero] at this
  have hreg1 : RegBg2 ell ell (cartanOf (phiU ell c t) : PeriodicLinkConfiguration SU2 L) := by
    have := hreg 1 (by norm_num); rwa [hb1, pow_one] at this
  have hQ0 := fun θ' => QlinStepX_sigma3 1 ell (stagφ c t) (stag_hphi0_u hN hE c t htπ) hreg0 θ'
  have hQ1 := fun θ' => QlinStepX_sigma3 ell ell (phiU ell c t) (stag_hphi1_u hN hE hell c t htπ hc2) hreg1 θ'
  have hC0 := fun θ' => C2StepX_sigma3 1 ell (stagφ c t) (stag_hphi0_u hN hE c t htπ) hreg0 θ'
  have hC1 := fun θ' => C2StepX_sigma3 ell ell (phiU ell c t) (stag_hphi1_u hN hE hell c t htπ hc2) hreg1 θ'
  have s1 := QlinCompX_succ2 ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 2 hreg 0 (by norm_num)
  have s2 := QlinCompX_succ2 ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 2 hreg 1 (by norm_num)
  have d1 := fun a => C2CompX_succ2 ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 2 hreg 0 (by norm_num) a
  have d2 := fun a => C2CompX_succ2 ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 2 hreg 1 (by norm_num) a
  simp only [zero_add, pow_zero, pow_one] at s1 s2 d1 d2
  have q1 : QlinCompX ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 1 (aF θ) = aF (Rsig 1 ell θ) := by
    rw [s1, ContinuousLinearMap.comp_apply, QlinCompX_zero, ContinuousLinearMap.id_apply, hb0]
    exact hQ0 θ
  have c1 : C2CompX ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 1 (aF θ) = 0 := by
    rw [d1, C2CompX_zero, map_zero, zero_add, QlinCompX_zero, ContinuousLinearMap.id_apply, hb0]
    exact hC0 θ
  have e1 : thetaSeq ell 1 θ = Rsig 1 ell θ := by simp [thetaSeq]
  have e2 : thetaSeq ell 2 θ = Rsig ell ell (Rsig 1 ell θ) := by simp [thetaSeq]
  refine ⟨by rw [e1]; exact q1, ?_, c1, ?_⟩
  · rw [s2, ContinuousLinearMap.comp_apply, q1, hb1, e2]
    exact hQ1 _
  · rw [d2, c1, map_zero, zero_add, q1, hb1]
    exact hC1 _

#print axioms C2CompX_zero
#print axioms stag_levels_sigma3

end AdalyFormal.CoverOmega
