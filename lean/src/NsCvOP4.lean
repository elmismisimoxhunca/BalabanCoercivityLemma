import NsCvOP3
import NsOdd10

/-!
# CvOP4 -- the staggered tower `bg t j` (j = 0, 1) is an analytic family of regular backgrounds (lane omega/near2/struct)

`stagCfg c t = cartanOf (stagφ c t)`, `bg1 = cartanOf (phi1 ell c t)` (CvO19), both with angles linear in `t`;
`cartan` is analytic; regularity from `stag_regTower_gen`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverOmega
open AdalyFormal.CoverNested
open AdalyFormal.Balaban.UbarTowerCov (UbarTower UbarTower_succ UbarTower_zero)

theorem cartan_coe_expr (θ : ℝ) : ((cartan θ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : M2)
    = (Real.cos θ : ℂ) • (1 : M2) + (Real.sin θ : ℂ) • (Matrix.diagonal ![Complex.I, -Complex.I] : M2) := by
  have h1 : Complex.exp ((θ : ℂ) * Complex.I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h2 : Complex.exp (-((θ : ℂ) * Complex.I)) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    have : -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  show cartanM θ = _
  unfold cartanM
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, h1, h2] <;> ring

theorem SGat_cartan {g : ℝ → ℝ} {t0 : ℝ} (hg : ContDiffAt ℝ ⊤ g t0) :
    SGat t0 (fun t => cartan (g t)) := by
  unfold SGat
  have h1 : ContDiffAt ℝ ⊤ (fun t => (Real.cos (g t) : ℂ)) t0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp t0 (Real.contDiff_cos.contDiffAt.comp t0 hg)
  have h2 : ContDiffAt ℝ ⊤ (fun t => (Real.sin (g t) : ℂ)) t0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp t0 (Real.contDiff_sin.contDiffAt.comp t0 hg)
  have : (fun t => ((cartan (g t) : Matrix.specialUnitaryGroup (Fin 2) ℂ) : M2))
      = fun t => (Real.cos (g t) : ℂ) • (1 : M2) + (Real.sin (g t) : ℂ) • (Matrix.diagonal ![Complex.I, -Complex.I] : M2) := by
    funext t; exact cartan_coe_expr (g t)
  rw [this]
  exact (h1.smul contDiffAt_const).add (h2.smul contDiffAt_const)

variable {L : PeriodicLatticeExtent} {ell : ℕ}

theorem AnaFam_cartanOf (θ : ℝ → PeriodicLatticeEdge L → ℝ) {t0 : ℝ}
    (h : ∀ e, ContDiffAt ℝ ⊤ (fun t => θ t e) t0) : AnaFam (fun t => cartanOf (θ t)) t0 :=
  fun e => SGat_cartan (h e)

theorem contDiffAt_stagφ (c : ℕ) (e : PeriodicLatticeEdge L) (t0 : ℝ) :
    ContDiffAt ℝ ⊤ (fun t => stagφ (L := L) c t e) t0 := by
  unfold stagφ
  by_cases h : (e.1 0).val = c ∧ e.2 = 1
  · simp only [if_pos h]
    exact contDiffAt_const.mul contDiffAt_id
  · simp only [if_neg h]
    exact contDiffAt_const

theorem contDiffAt_phi1 (ell c : ℕ) (e : PeriodicLatticeEdge L) (t0 : ℝ) :
    ContDiffAt ℝ ⊤ (fun t => phi1 (L := L) ell c t e) t0 := by
  unfold phi1 u1
  by_cases h : e.2 = 0
  · simp only [if_pos h]
    exact contDiffAt_const.mul ((contDiffAt_const.mul contDiffAt_id).mul contDiffAt_const |>.mul contDiffAt_const)
  · simp only [if_neg h]
    exact contDiffAt_const

theorem contDiffAt_phi1o (ell c : ℕ) (e : PeriodicLatticeEdge L) (t0 : ℝ) :
    ContDiffAt ℝ ⊤ (fun t => phi1o L c ell t e) t0 := by
  unfold phi1o fld
  by_cases h : e.2 = 0
  · simp only [if_pos h]
    exact (contDiffAt_id.mul contDiffAt_const).mul contDiffAt_const
  · simp only [if_neg h]
    by_cases h1 : e.2 = 1
    · simp only [if_pos h1]
      exact (contDiffAt_id.mul contDiffAt_const).mul contDiffAt_const
    · simp only [if_neg h1]
      exact contDiffAt_const

theorem contDiffAt_phiU (ell c : ℕ) (e : PeriodicLatticeEdge L) (t0 : ℝ) :
    ContDiffAt ℝ ⊤ (fun t => phiU (L := L) ell c t e) t0 := by
  by_cases hev : ell % 2 = 0
  · simp only [phiU, if_pos hev]
    exact contDiffAt_phi1 ell c e t0
  · simp only [phiU, if_neg hev]
    exact contDiffAt_phi1o ell c e t0

/-- level 0 is an analytic family. -/
theorem anaFam_bg0 (c : ℕ) (t0 : ℝ) :
    AnaFam (fun t => UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) 0) t0 := by
  have : (fun t => UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) 0)
      = fun t => cartanOf (stagφ c t) := by
    funext t; simp only [UbarTower_zero]; exact stagCfg_eq c t
  rw [this]
  exact AnaFam_cartanOf _ (fun e => contDiffAt_stagφ c e t0)

/-- level 1 is an analytic family near any `t0` with `|t0| < tcap ell`. -/
theorem anaFam_bg1 (hN : 2 ∣ L 1 + 1) (hE : StagPar L ell) (hell : 0 < ell) (c : ℕ) (hc1 : ell ≤ c) (hc2 : c + ell * ell < L 0 + 1)
    {t0 : ℝ} (ht0 : |t0| < tcap ell) :
    AnaFam (fun t => UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) 1) t0 := by
  intro e
  have hev : (fun t => ((UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) 1 e : SU2) : M2))
      =ᶠ[𝓝 t0] fun t => ((cartan (phiU ell c t e) : SU2) : M2) := by
    have hlt : ∀ᶠ t in 𝓝 t0, |t| < tcap ell := by
      have : IsOpen {t : ℝ | |t| < tcap ell} := isOpen_lt continuous_abs continuous_const
      exact this.mem_nhds ht0
    filter_upwards [hlt] with t ht
    have hb1 : UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) 1 = cartanOf (phiU ell c t) := by
      simp only [UbarTower_succ, UbarTower_zero, pow_zero]
      exact bg1_eq_u hN hE hell c t ht hc1 hc2
    rw [hb1]; rfl
  unfold SGat
  exact (SGat_cartan (contDiffAt_phiU ell c e t0)).congr_of_eventuallyEq hev

theorem tower_stag_ana (hN : 2 ∣ L 1 + 1) (hE : StagPar L ell) (hell : 0 < ell) (c : ℕ) (hc1 : ell ≤ c)
    (hc2 : c + ell * ell < L 0 + 1) {t0 : ℝ} (ht0 : |t0| < tcap ell) :
    (∀ j, j < 2 → AnaFam (fun t => UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) j) t0) ∧
    (∀ j, j < 2 → RegBg2 (ell ^ j) ell (UbarTower su2LogExp ell (stagCfg c t0 : PeriodicLinkConfiguration SU2 L) j)) := by
  refine ⟨fun j hj => ?_, fun j hj => stag_regTower_u hN hE hell c t0 ht0 hc1 hc2 j hj⟩
  have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl
  · exact anaFam_bg0 c t0
  · exact anaFam_bg1 hN hE hell c hc1 hc2 ht0

end AdalyFormal.CoverOmega.Struct
