import NuD1d
import NtCvO20

/-!
# NuQ1 -- `Q_j` and `C^{(2)}_j` of the tower of the direction-0 staggered family on sigma_3 fields (lane ncwdh_ell2_20261018)

Analogue of `NsCvO19` (angle fields) and `NsCvO20` (`stag_levels_sigma3`, `stag_QlinCompX_Z`) for `stag0Cfg`.
Parity/regularity hypotheses: `2 ∣ ell`, `2 ∣ N₁`, `ell ≤ xs`, `xs + ell * ell < N₀`, `|t| < π/2`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open scoped Matrix
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2 (XS qCompX QlinCompX QlinStepX C2CompX C2StepX)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge UbarTower UbarTower_succ UbarTower_zero)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

section
variable [CfData]
variable {L : PeriodicLatticeExtent}

/-- angle function of the direction-0 staggered family. -/
noncomputable def stag0φ (xs : ℕ) (t : ℝ) : PeriodicLatticeEdge L → ℝ :=
  fun e => if (e.1 0).val = xs ∧ e.2 = 0 then stagSign e.1 * t else 0

theorem stag0Cfg_eq (xs : ℕ) (t : ℝ) :
    (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) = cartanOf (stag0φ xs t) := by
  funext e; unfold stag0Cfg cartanOf stag0φ; split_ifs
  · rfl
  · exact cartan_zero.symm

theorem pathAngG_stag0φ (xs : ℕ) (t : ℝ) (s : ℕ) (p : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite L, pathAngG s (stag0φ xs t) y p = uAng s (D0 xs) (uSt t) y p := by
  induction p with
  | nil => intro y; rfl
  | cons μ rest ih =>
    intro y
    simp only [pathAngG, uAng, ih]
    congr 1
    unfold stag0φ D0 uSt stagSign sgnNat
    by_cases hμ : μ = 0
    · by_cases h : (y 0).val = xs
      · simp [hμ, h]
      · simp [hμ, h]
    · simp [hμ]

theorem loopAngG_stag0φ (xs : ℕ) (t : ℝ) {s ell : ℕ} (y : PeriodicLatticeSite L) (μ : Fin 3)
    {x : PeriodicLatticeSite L} (hx : x ∈ stepBlockOf y s ell) :
    loopAngG s ell (stag0φ xs t) y μ x = uPhi s ell (D0 xs) (uSt t) y μ x := by
  unfold loopAngG
  simp only [pathAngG_stag0φ]
  exact uTemp_angle_expr y μ hx

theorem stag0_hphi0 {ell : ℕ} (hN0 : ell ≤ L 0 + 1) (xs : ℕ) (t : ℝ) (ht : |t| < Real.pi / 2) :
    ∀ cc : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf cc.1 1 ell, |loopAngG 1 ell (stag0φ xs t) cc.1 cc.2 x| < Real.pi := by
  intro cc x hx
  rw [loopAngG_stag0φ xs t cc.1 cc.2 hx]
  exact uPhi_abs_lt one_pos (uSt_abs_le t) (by linarith) (hD0_stride_one hN0 xs) cc.1 cc.2 hx

/-- angle function of the first blocked level. -/
noncomputable def phi1z (ell xs : ℕ) (t : ℝ) : PeriodicLatticeEdge L → ℝ :=
  fun e => if e.2 = 0 then Sw0 xs ell (L 0 + 1) (e.1 0).val * u1s (L := L) ell t (e.1 1).val (e.1 2).val else 0

theorem bg1_eq_stag0 {ell : ℕ} (hell : 0 < ell) (hN0 : ell ≤ L 0 + 1) (hN : 2 ∣ L 1 + 1) (hE : 2 ∣ ell)
    {xs : ℕ} (hxs1 : ell ≤ xs) (hxs2 : xs + ell ≤ L 0 + 1) (t : ℝ) (ht : |t| < Real.pi / 2) :
    stridedBlockedGauge su2LogExp 1 ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) = cartanOf (phi1z ell xs t) := by
  have hV := bg1_isUTemp_stag0 hell hN0 hN hE hxs1 hxs2 t ht
  funext e
  obtain ⟨z, μ⟩ := e
  obtain ⟨h0, h1, h2⟩ := hV z
  have key : μ = 0 ∨ μ = 1 ∨ μ = 2 := by fin_cases μ <;> simp
  rcases key with rfl | rfl | rfl
  · simpa [cartanOf, phi1z] using h0
  · simp only [cartanOf, phi1z, if_neg (show ¬ ((1 : Fin 3) = 0) by decide)]; rw [h1]; exact cartan_zero.symm
  · simp only [cartanOf, phi1z, if_neg (show ¬ ((2 : Fin 3) = 0) by decide)]; rw [h2]; exact cartan_zero.symm

theorem pathAngG_phi1z (ell xs : ℕ) (t : ℝ) (s : ℕ) (p : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite L, pathAngG s (phi1z ell xs t) y p = uAng s (Sw0 xs ell (L 0 + 1)) (u1s (L := L) ell t) y p := by
  induction p with
  | nil => intro y; rfl
  | cons μ rest ih => intro y; simp only [pathAngG, uAng, ih, phi1z]

theorem stag0_hphi1 {ell : ℕ} (hell : 0 < ell) (xs : ℕ) (hNN : ell * ell ≤ L 0 + 1) (t : ℝ) (ht : |t| < Real.pi / 2) :
    ∀ cc : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf cc.1 ell ell, |loopAngG ell ell (phi1z ell xs t) cc.1 cc.2 x| < Real.pi := by
  intro cc x hx
  obtain ⟨y, μ⟩ := cc
  unfold loopAngG
  simp only [pathAngG_phi1z]
  rw [uTemp_angle_expr y μ hx]
  exact uPhi_abs_lt hell (u1s_abs_le hell t) (by linarith) (hSw0_windows xs hNN) y μ hx

theorem stag0_regTower_gen {ell : ℕ} (hell : 0 < ell) (hN : 2 ∣ L 1 + 1) (hE : 2 ∣ ell) {xs : ℕ} (hxs1 : ell ≤ xs)
    (hxs2 : xs + ell ≤ L 0 + 1) (hNN : ell * ell ≤ L 0 + 1) (t : ℝ) (ht : |t| < Real.pi / 2) :
    RegTower2 ell (UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) 2 := by
  have hN0 : ell ≤ L 0 + 1 := le_trans (Nat.le_mul_self ell) hNN
  intro j hj
  have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl
  · simpa [UbarTower_zero] using regBg2_level0_stag0 hN0 xs t ht
  · simpa [UbarTower_succ, UbarTower_zero] using regBg2_level1_stag0 hell hN0 hN hE hxs1 hxs2 hNN t ht

/-- **the tower of the direction-0 staggered family on ARBITRARY sigma_3 fields**: `Q_j` is `Rsig`-iterated and `C^{(2)}_j` vanishes, `j = 1, 2`. -/
theorem stag0_levels_sigma3 (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : 2 ∣ ell) (hell : 0 < ell) {xs : ℕ} (t : ℝ)
    (ht : |t| < Real.pi / 2) (hxs1 : ell ≤ xs) (hxs2 : xs + ell * ell < L 0 + 1) (θ : PeriodicLatticeEdge L → ℝ) :
    QlinCompX ell (UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) 1 (aF θ) = aF (thetaSeq ell 1 θ) ∧
    QlinCompX ell (UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) 2 (aF θ) = aF (thetaSeq ell 2 θ) ∧
    C2CompX ell (UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) 1 (aF θ) = 0 ∧
    C2CompX ell (UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) 2 (aF θ) = 0 := by
  have hNN : ell * ell ≤ L 0 + 1 := by omega
  have hxs2' : xs + ell ≤ L 0 + 1 := by nlinarith [Nat.le_mul_self ell]
  have hN0 : ell ≤ L 0 + 1 := le_trans (Nat.le_mul_self ell) hNN
  have hreg := stag0_regTower_gen hell hN hE hxs1 hxs2' hNN t ht
  have hb0 : UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) 0 = cartanOf (stag0φ xs t) := by
    rw [UbarTower_zero]; exact stag0Cfg_eq xs t
  have hb1 : UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) 1 = cartanOf (phi1z ell xs t) := by
    simp only [UbarTower_succ, UbarTower_zero, pow_zero]
    exact bg1_eq_stag0 hell hN0 hN hE hxs1 hxs2' t ht
  have hreg0 : RegBg2 1 ell (cartanOf (stag0φ xs t) : PeriodicLinkConfiguration SU2 L) := by
    have := hreg 0 (by norm_num); rwa [hb0, pow_zero] at this
  have hreg1 : RegBg2 ell ell (cartanOf (phi1z ell xs t) : PeriodicLinkConfiguration SU2 L) := by
    have := hreg 1 (by norm_num); rwa [hb1, pow_one] at this
  have hQ0 := fun θ' => QlinStepX_sigma3 1 ell (stag0φ xs t) (stag0_hphi0 hN0 xs t ht) hreg0 θ'
  have hQ1 := fun θ' => QlinStepX_sigma3 ell ell (phi1z ell xs t) (stag0_hphi1 hell xs hNN t ht) hreg1 θ'
  have hC0 := fun θ' => C2StepX_sigma3 1 ell (stag0φ xs t) (stag0_hphi0 hN0 xs t ht) hreg0 θ'
  have hC1 := fun θ' => C2StepX_sigma3 ell ell (phi1z ell xs t) (stag0_hphi1 hell xs hNN t ht) hreg1 θ'
  have s1 := QlinCompX_succ2 ell (UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) 2 hreg 0 (by norm_num)
  have s2 := QlinCompX_succ2 ell (UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) 2 hreg 1 (by norm_num)
  have d1 := fun a => C2CompX_succ2 ell (UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) 2 hreg 0 (by norm_num) a
  have d2 := fun a => C2CompX_succ2 ell (UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) 2 hreg 1 (by norm_num) a
  simp only [zero_add, pow_zero, pow_one] at s1 s2 d1 d2
  have q1 : QlinCompX ell (UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) 1 (aF θ) = aF (Rsig 1 ell θ) := by
    rw [s1, ContinuousLinearMap.comp_apply, QlinCompX_zero, ContinuousLinearMap.id_apply, hb0]
    exact hQ0 θ
  have c1 : C2CompX ell (UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) 1 (aF θ) = 0 := by
    rw [d1, C2CompX_zero, map_zero, zero_add, QlinCompX_zero, ContinuousLinearMap.id_apply, hb0]
    exact hC0 θ
  have e1 : thetaSeq ell 1 θ = Rsig 1 ell θ := by simp [thetaSeq]
  have e2 : thetaSeq ell 2 θ = Rsig ell ell (Rsig 1 ell θ) := by simp [thetaSeq]
  refine ⟨by rw [e1]; exact q1, ?_, c1, ?_⟩
  · rw [s2, ContinuousLinearMap.comp_apply, q1, hb1, e2]
    exact hQ1 _
  · rw [d2, c1, map_zero, zero_add, q1, hb1]
    exact hC1 _

end

end AdalyFormal.NcwdhTwo
