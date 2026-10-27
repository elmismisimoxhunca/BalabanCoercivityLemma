import NuD1d
import NuZ1
import NtCvOS15
import NtCvOX2
import NtCvON4

/-!
# NuU1 -- analyticity of the direction-0 staggered tower, nesting and `gOf ≠ 0` at `ell = 2` (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

namespace AdalyFormal.NcwdhTwo

open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.CoverOmega.Struct
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp Tower)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower UbarTower_succ UbarTower_zero)

section
variable [CfData]
variable {L : PeriodicLatticeExtent}

theorem stag0Cfg_eq_cartanOf (xs : ℕ) (t : ℝ) :
    (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) =
      cartanOf (fun e => if (e.1 0).val = xs ∧ e.2 = 0 then stagSign e.1 * t else 0) := by
  funext e
  unfold stag0Cfg cartanOf
  beta_reduce
  split_ifs
  · rfl
  · exact cartan_zero.symm

theorem anaFam_stag0_bg0 {ell : ℕ} (xs : ℕ) (t0 : ℝ) :
    AnaFam (fun t => UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) 0) t0 := by
  have : (fun t => UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) 0)
      = fun t => cartanOf (fun e : PeriodicLatticeEdge L => if (e.1 0).val = xs ∧ e.2 = 0 then stagSign e.1 * t else 0) := by
    funext t; simp only [UbarTower_zero]; exact stag0Cfg_eq_cartanOf xs t
  rw [this]
  refine AnaFam_cartanOf _ (fun e => ?_)
  by_cases h : (e.1 0).val = xs ∧ e.2 = 0
  · simp only [if_pos h]
    exact contDiffAt_const.mul contDiffAt_id
  · simp only [if_neg h]
    exact contDiffAt_const

theorem anaFam_stag0_bg1 {ell : ℕ} (hell : 0 < ell) (hN0 : ell ≤ L 0 + 1) (hN : 2 ∣ L 1 + 1) (hE : 2 ∣ ell) (xs : ℕ)
    {t0 : ℝ} (ht0 : |t0| < Real.pi / 2) :
    AnaFam (fun t => UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) 1) t0 := by
  intro e
  have hev : (fun t => ((UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) 1 e : SU2) : M2))
      =ᶠ[𝓝 t0] fun t => ((cartan (if e.2 = 0 then Sw0 xs ell (L 0 + 1) (e.1 0).val * Ubg0 ell t e.1 else 0) : SU2) : M2) := by
    have hlt : ∀ᶠ t in 𝓝 t0, |t| < Real.pi / 2 := by
      have : IsOpen {t : ℝ | |t| < Real.pi / 2} := isOpen_lt continuous_abs continuous_const
      exact this.mem_nhds ht0
    filter_upwards [hlt] with t ht
    simp only [UbarTower_succ, UbarTower_zero, pow_zero]
    rw [bg1_stag0_all hell hN0 hN hE xs t ht e.1 e.2]
  unfold SGat
  refine (SGat_cartan (g := fun t => if e.2 = 0 then Sw0 xs ell (L 0 + 1) (e.1 0).val * Ubg0 ell t e.1 else 0) ?_).congr_of_eventuallyEq hev
  by_cases h : e.2 = 0
  · simp only [if_pos h]
    unfold Ubg0
    exact contDiffAt_const.mul ((contDiffAt_const.mul contDiffAt_id).mul contDiffAt_const)
  · simp only [if_neg h]
    exact contDiffAt_const

theorem tower_stag0_ana {ell : ℕ} {Lu : PeriodicLatticeExtent} (S : Tower (scaleUp ell 2 Lu)) (hell : 0 < ell) (hE : 2 ∣ ell) {xs : ℕ}
    (hxs1 : ell ≤ xs) (hxs2 : xs + ell ≤ scaleUp ell 2 Lu 0 + 1) (hNN : ell * ell ≤ scaleUp ell 2 Lu 0 + 1)
    {t0 : ℝ} (ht0 : |t0| < Real.pi / 2) :
    TowerOK (geomOf ell 2 S) (fun t => stag0Cfg (L := scaleUp ell 2 Lu) xs t) t0 := by
  have hdiv := scaleUp_dvd2 (Lu := Lu) hell
  have hN : 2 ∣ scaleUp ell 2 Lu 1 + 1 := dvd_trans hE (hdiv 1)
  have hN0 : ell ≤ scaleUp ell 2 Lu 0 + 1 := le_trans (Nat.le_mul_self ell) hNN
  have hreg := stag0_regTower (Lu := Lu) hell hE t0 ht0 hxs1 hxs2 hNN
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · exact anaFam_stag0_bg0 xs t0
    · exact anaFam_stag0_bg1 hell hN0 hN hE xs ht0
  · exact hreg j (by omega)

end

end AdalyFormal.NcwdhTwo
