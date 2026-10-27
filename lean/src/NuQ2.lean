import NuQ1
import NtCvO33

/-!
# NuQ2 -- `Q = QfullOf` and `C^{(2)}` of the direction-0 staggered tower on Z-fields and sigma_3 fields (lane ncwdh_ell2_20261018)

Analogue of `NtCvO32` (`Qfull_zfield`) and `NtCvO33` (`C2fullOf_sig`) for `stag0Cfg`.
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
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge UbarTower UbarTower_succ UbarTower_zero)

section
variable [CfData]

/-- the hypotheses on the lattice and the parameters used by the direction-0 staggered tower. -/
structure Z0Hyp (L : PeriodicLatticeExtent) (ell xs : ℕ) (t : ℝ) : Prop where
  hN : 2 ∣ L 1 + 1
  hE : 2 ∣ ell
  hell : 0 < ell
  hdiv : ∀ μ, ell * ell ∣ L μ + 1
  hc1 : ell ≤ xs
  hc2 : xs + ell * ell < L 0 + 1
  ht : |t| < Real.pi / 2

variable {L : PeriodicLatticeExtent} {ell xs : ℕ} {t : ℝ}

theorem Z0Hyp.regTower (Z : Z0Hyp L ell xs t) :
    RegTower2 ell (UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) 2 := by
  have hNN : ell * ell ≤ L 0 + 1 := by have := Z.hc2; omega
  have hxs2' : xs + ell ≤ L 0 + 1 := by have := Z.hc2; nlinarith [Nat.le_mul_self ell]
  exact stag0_regTower_gen Z.hell Z.hN Z.hE Z.hc1 hxs2' hNN t Z.ht

theorem stag0_QlinCompX_Z (Z : Z0Hyp L ell xs t) {f : ℕ → ℝ} {θ : PeriodicLatticeEdge L → ℝ} (hθ : FormF 1 f θ) :
    QlinCompX ell (UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) 1 (aF θ) = aF (thetaSeq ell 1 θ) ∧
    QlinCompX ell (UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) 2 (aF θ) = aF (thetaSeq ell 2 θ) ∧
    FormF ell (fSum ell 1 f) (thetaSeq ell 1 θ) ∧ FormF (ell ^ 2) (fSum ell 2 f) (thetaSeq ell 2 θ) := by
  have hell := Z.hell
  have hdiv := Z.hdiv
  obtain ⟨h1, h2, -, -⟩ := stag0_levels_sigma3 Z.hN Z.hE hell t Z.ht Z.hc1 Z.hc2 θ
  refine ⟨h1, h2, ?_, ?_⟩
  · have hdiv1 : ∀ μ, ell ∣ L μ + 1 := fun μ => dvd_trans (dvd_mul_right ell ell) (hdiv μ)
    have hdiv0 : ∀ μ, 1 * ell ∣ L μ + 1 := fun μ => by rw [one_mul]; exact hdiv1 μ
    have hF1 : FormF (1 * ell) (fun v => ∑ n ∈ Finset.range ell, f (v + 1 * n)) (Rsig 1 ell θ) :=
      formF_Rsig one_pos hell hdiv0 hθ
    show FormF ell (fun v => ∑ n ∈ Finset.range ell, f (v + ell ^ 0 * n)) (Rsig (ell ^ 0) ell θ)
    simpa [pow_zero] using hF1
  · have hdiv1 : ∀ μ, ell ∣ L μ + 1 := fun μ => dvd_trans (dvd_mul_right ell ell) (hdiv μ)
    have hdiv0 : ∀ μ, 1 * ell ∣ L μ + 1 := fun μ => by rw [one_mul]; exact hdiv1 μ
    have hF1 : FormF (1 * ell) (fun v => ∑ n ∈ Finset.range ell, f (v + 1 * n)) (Rsig 1 ell θ) :=
      formF_Rsig one_pos hell hdiv0 hθ
    have hF1' : FormF ell (fSum ell 1 f) (thetaSeq ell 1 θ) := by
      show FormF ell (fun v => ∑ n ∈ Finset.range ell, f (v + ell ^ 0 * n)) (Rsig (ell ^ 0) ell θ)
      simpa [pow_zero] using hF1
    have hdiv2 : ∀ μ, ell ^ 1 * ell ∣ L μ + 1 := fun μ => by rw [pow_one]; exact hdiv μ
    have hF2 : FormF (ell ^ 1 * ell) (fun v => ∑ n ∈ Finset.range ell, (fSum ell 1 f) (v + ell ^ 1 * n)) (Rsig (ell ^ 1) ell (thetaSeq ell 1 θ)) :=
      formF_Rsig (pow_pos hell 1) hell hdiv2 (by simpa [pow_one] using hF1')
    simpa [thetaSeq, fSum, pow_two, pow_one] using hF2

theorem QlinB_zfield0 (Z : Z0Hyp L ell xs t) (f : ℕ → ℝ) (G : TowerGeom L) (hG : G.ell = ell) :
    (QlinB G (stag0Cfg (L := L) xs t) 1 (zfield f) : BondFnL2 L) = suCoordInv (aF (thetaSeq ell 1 (thetaF f))) ∧
    (QlinB G (stag0Cfg (L := L) xs t) 2 (zfield f) : BondFnL2 L) = suCoordInv (aF (thetaSeq ell 2 (thetaF f))) := by
  obtain ⟨h1, h2, -, -⟩ := stag0_QlinCompX_Z Z (formF_thetaF f)
  have e : bgTower G (stag0Cfg (L := L) xs t : Cfg L) = UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) := by
    unfold bgTower; rw [hG]
  have hreg := Z.regTower
  rw [QlinB_apply, QlinB_apply, e, hG, QlinCompL_eq_QlinCompX2 ell _ 2 hreg 1 (by norm_num),
    QlinCompL_eq_QlinCompX2 ell _ 2 hreg 2 le_rfl, suCoord_zfield, h1, h2]
  exact ⟨rfl, rfl⟩

theorem QlinB_zfield_apply0 (Z : Z0Hyp L ell xs t) (f : ℕ → ℝ) (G : TowerGeom L) (hG : G.ell = ell) (j : ℕ) (hj : j ≤ 2)
    (b : Bond L) (hb : Crs (ell ^ j) b.1) :
    ((QlinB G (stag0Cfg (L := L) xs t) j (zfield f) : BondFnL2 L) b : SuTwo) =
      (if b.2 = 1 then dgS (fSum ell j f (b.1 0).val) else (0 : SuTwo)) := by
  have hfm := stag0_QlinCompX_Z Z (formF_thetaF (L := L) f)
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with h0 | h1 | h2
  · subst h0
    rw [QlinB_zero]
    show (zfield f : BondFnL2 L) b = _
    simp only [zfield_apply, fSum]
  · subst h1
    rw [(QlinB_zfield0 Z f G hG).1, suCoordInv_aF]
    have hcr' : Crs ell b.1 := by simpa using hb
    have := hfm.2.2.1 b.1 hcr' b.2
    show dgS (thetaSeq ell 1 (thetaF f) b) = _
    have e : thetaSeq ell 1 (thetaF f) b = if b.2 = 1 then fSum ell 1 f (b.1 0).val else 0 := this
    rw [e]
    split_ifs <;> first | rfl | exact dgS_zero
  · subst h2
    rw [(QlinB_zfield0 Z f G hG).2, suCoordInv_aF]
    have := hfm.2.2.2 b.1 hb b.2
    show dgS (thetaSeq ell 2 (thetaF f) b) = _
    have e : thetaSeq ell 2 (thetaF f) b = if b.2 = 1 then fSum ell 2 f (b.1 0).val else 0 := this
    rw [e]
    split_ifs <;> first | rfl | exact dgS_zero

/-- **`Q = QfullOf` on a Z-field** (direction-0 staggered tower). -/
theorem Qfull_zfield0 (Z : Z0Hyp L ell xs t) (f : ℕ → ℝ) (G : TowerGeom L) (hG : G.ell = ell) (hk : G.k = 2)
    (hcrs : ∀ p : BIdx G, Crs (ell ^ (p.1 : ℕ)) p.2.1.1) (p : BIdx G) :
    (QfullOf G (stag0Cfg (L := L) xs t) (zfield f) : FSp G) p =
      ((ell : ℝ) ^ (p.1 : ℕ))⁻¹ • (if p.2.1.2 = 1 then dgS (fSum ell (p.1 : ℕ) f (p.2.1.1 0).val) else (0 : SuTwo)) := by
  have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; omega
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G (stag0Cfg (L := L) xs t) p.1 (zfield f))) p.2.1 = _
  rw [hG, QlinB_zfield_apply0 Z f G hG p.1 hj p.2.1 (hcrs p)]

theorem C2rawB_sig0 (Z : Z0Hyp L ell xs t) (G : TowerGeom L) (hG : G.ell = ell) (j : ℕ) (hj : j ≤ 2)
    (A : BondFnL2 L) (hA : SigB (WithLp.ofLp A)) :
    C2rawB G (stag0Cfg (L := L) xs t) j A = 0 := by
  have hreg := Z.regTower
  have e : bgTower G (stag0Cfg (L := L) xs t : Cfg L) = UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) := by
    unfold bgTower; rw [hG]
  obtain ⟨-, -, c1, c2⟩ := stag0_levels_sigma3 Z.hN Z.hE Z.hell t Z.ht Z.hc1 Z.hc2 (thetaOf (WithLp.ofLp A))
  rw [C2rawB_eq, e, hG, C2CompL_eq_C2CompX2 ell _ 2 hreg j hj, suCoord_sig A hA]
  interval_cases j
  · rw [C2CompX_zero]; ext b; simp [suCoordInv]
  · rw [c1]; ext b; simp [suCoordInv]
  · rw [c2]; ext b; simp [suCoordInv]

theorem C2fullOf_sig0 (Z : Z0Hyp L ell xs t) (G : TowerGeom L) (hG : G.ell = ell) (hk : G.k = 2)
    (A : BondFnL2 L) (hA : SigB (WithLp.ofLp A)) :
    C2fullOf G (stag0Cfg (L := L) xs t) A = 0 := by
  refine PiLp.ext (fun p => ?_)
  have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; omega
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (C2rawB G (stag0Cfg (L := L) xs t) p.1 A)) p.2.1 = 0
  rw [C2rawB_sig0 Z G hG p.1 hj A hA]
  simp

end

end AdalyFormal.NcwdhTwo
