import NsCvO18
import NsCvO15

/-!
# CvO19 -- the level-`j` composite `Q_j` of the staggered layer on transverse-constant sigma_3 fields (lane omega)

* the staggered layer, its first blocked level and the unit-level background are `cartanOf` of explicit angle functions, with the no-wrap hypotheses
  of `QlinStepX_sigma3` (loops of every base bond have `|angle| < π`);
* `stag_QlinCompX_Z`: for `θ` of the form `FormF 1 f`, `QlinCompX ell (UbarTower ..) j (aF θ) = aF θ_j`, `θ_{j+1} = Rsig (ell^j) ell θ_j`,
  `FormF (ell^j) (fSum ell j f) θ_j`: the genuine bond constraint `Q_j` of the staggered layer on a Z-field is the sum of `ell^j` consecutive slices.
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
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq UbarTower UbarTower_succ UbarTower_zero)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

/-- angle function of the staggered layer. -/
noncomputable def stagφ (c : ℕ) (t : ℝ) : PeriodicLatticeEdge L → ℝ :=
  fun e => if (e.1 0).val = c ∧ e.2 = 1 then stagSign e.1 * t else 0

theorem stagCfg_eq (c : ℕ) (t : ℝ) : (stagCfg c t : PeriodicLinkConfiguration SU2 L) = cartanOf (stagφ c t) := by
  funext e; unfold stagCfg cartanOf stagφ; split_ifs
  · rfl
  · exact cartan_zero.symm

theorem pathAngG_stagφ (c : ℕ) (t : ℝ) (s : ℕ) (p : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite L, pathAngG s (stagφ c t) y p = pathAng c t s y p := by
  induction p with
  | nil => intro y; rfl
  | cons μ rest ih => intro y; simp only [pathAngG, pathAng, ih, stagφ]

theorem loopAngG_stagφ (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : 2 ∣ ell) (c : ℕ) (t : ℝ) (y x : PeriodicLatticeSite L) (μ : Fin 3) :
    loopAngG 1 ell (stagφ c t) y μ x = stagPhi c t μ ell y x := by
  unfold loopAngG
  simp only [pathAngG_stagφ]
  exact stag_angle_expr hN hE c t y x μ

theorem stag_hphi0 (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : 2 ∣ ell) (c : ℕ) (t : ℝ) (htπ : |t| < Real.pi) :
    ∀ cc : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf cc.1 1 ell, |loopAngG 1 ell (stagφ c t) cc.1 cc.2 x| < Real.pi := by
  intro cc x _
  rw [loopAngG_stagφ hN hE]
  exact stagPhi_abs_lt c t htπ _ _ _ _

/-- angle function of the first blocked level. -/
noncomputable def phi1 (ell c : ℕ) (t : ℝ) : PeriodicLatticeEdge L → ℝ :=
  fun e => if e.2 = 0 then Dfun c ell (L 0 + 1) (e.1 0).val * u1 (L := L) ell t (e.1 1).val (e.1 2).val else 0

theorem bg1_eq (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : 2 ∣ ell) (hell : 0 < ell) (c : ℕ) (t : ℝ) (htπ : |t| < Real.pi)
    (hc1 : ell ≤ c) (hc2 : c + ell ≤ L 0 + 1) :
    stridedBlockedGauge su2LogExp 1 ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) = cartanOf (phi1 ell c t) := by
  have hV := bg1_isUTemp hN hE hell c t htπ hc1 hc2
  funext e
  obtain ⟨z, μ⟩ := e
  obtain ⟨h0, h1, h2⟩ := hV z
  have key : μ = 0 ∨ μ = 1 ∨ μ = 2 := by fin_cases μ <;> simp
  rcases key with rfl | rfl | rfl
  · simpa [cartanOf, phi1] using h0
  · simp only [cartanOf, phi1, if_neg (show ¬ ((1 : Fin 3) = 0) by decide)]; rw [h1]; exact cartan_zero.symm
  · simp only [cartanOf, phi1, if_neg (show ¬ ((2 : Fin 3) = 0) by decide)]; rw [h2]; exact cartan_zero.symm

theorem pathAngG_phi1 (ell c : ℕ) (t : ℝ) (s : ℕ) (p : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite L, pathAngG s (phi1 ell c t) y p = uAng s (Dfun c ell (L 0 + 1)) (u1 (L := L) ell t) y p := by
  induction p with
  | nil => intro y; rfl
  | cons μ rest ih => intro y; simp only [pathAngG, uAng, ih, phi1]

theorem stag_hphi1 (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hell : 0 < ell) (c : ℕ) (t : ℝ) (htπ : |t| < Real.pi) :
    ∀ cc : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf cc.1 ell ell, |loopAngG ell ell (phi1 ell c t) cc.1 cc.2 x| < Real.pi := by
  intro cc x hx
  obtain ⟨y, μ⟩ := cc
  unfold loopAngG
  simp only [pathAngG_phi1]
  rw [uTemp_angle_expr y μ hx]
  have hb : ∀ (S p q : ℝ), |S| ≤ 1 → |p| ≤ |t| / 2 → |q| ≤ |t| / 2 → |S * (p - q)| < Real.pi := by
    intro S p q hS hp hq
    rw [abs_mul]
    have : |p - q| ≤ |t| := by
      calc |p - q| ≤ |p| + |q| := abs_sub _ _
        _ ≤ |t| := by linarith
    calc |S| * |p - q| ≤ 1 * |t| := by gcongr
      _ < Real.pi := by linarith
  have hu := u1_abs_le (L := L) hell t
  split_ifs
  · exact hb _ _ _ (sumD_abs_le c ell (L 0 + 1) (y 0).val ell) (hu _ _) (hu _ _)
  · exact hb _ _ _ (sumD_abs_le c ell (L 0 + 1) (y 0).val _) (hu _ _) (hu _ _)
  · exact hb _ _ _ (sumD_abs_le c ell (L 0 + 1) (y 0).val _) (hu _ _) (hu _ _)



/-- sum of `ell` shifted copies. -/
def fSum (ell : ℕ) : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, f => f
  | j + 1, f => fun v => ∑ n ∈ Finset.range ell, fSum ell j f (v + ell ^ j * n)

/-- the angle field after `j` raw steps. -/
noncomputable def thetaSeq (ell : ℕ) : ℕ → (PeriodicLatticeEdge L → ℝ) → (PeriodicLatticeEdge L → ℝ)
  | 0, θ => θ
  | j + 1, θ => Rsig (ell ^ j) ell (thetaSeq ell j θ)

theorem stag_regTower_gen (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : 2 ∣ ell) (hell : 0 < ell) (c : ℕ) (t : ℝ) (htπ : |t| < Real.pi)
    (hc1 : ell ≤ c) (hc2 : c + ell ≤ L 0 + 1) :
    RegTower2 ell (UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L)) 2 := by
  intro j hj
  have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl
  · simpa [UbarTower_zero] using regBg2_level0 hN hE c t htπ
  · simpa [UbarTower_succ, UbarTower_zero] using regBg2_level1 hN hE hell c t htπ hc1 hc2

end AdalyFormal.CoverOmega
