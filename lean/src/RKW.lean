import RKF
import ASW2
/-!
# RKW -- NON-VACUITY of `ginv_coercive_M0_kuniform` at a genuinely CURVED background (ell = 2, k = 1).

Same configuration family as ASW2 (`U8 ε = torusCfg f_ε`, one bond of angle `ε`, fine torus `8³`), with
`ε = epsB := min (10⁻¹³) (r0 / 10¹⁰)` (smaller than ASW2's `epsA` so that the k-free regularity condition `c5` holds).
`witnessKU_regime : M0RegimeR …`, `witnessKU_small : KUSmall 2 ρ`, `witnessKU_curved` (a fine plaquette with `dv > 0`),
`witnessKU_coercive` (the headline theorem applied).  `Kc_two_le : Kc 2 ≤ 4·10⁵`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
noncomputable section
namespace AdalyFormal.RegBgKU

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CurvBlock (dv)
open AdalyFormal.NonflatJet (r0 r0_pos)
open AdalyFormal.AsmM0 (rhoM0 M0RegimeR U8 fE Lu3 U8_link U8_plaq U8_nonflat Theta_num)
open AdalyFormal.CurvBlock (plaq_of_pw_one)
open AdalyFormal.Balaban.AbelianBlockingRate (torusCfg)
open AdalyFormal.StatementLane (scaleUp)

def epsB : ℝ := min (1 / 10 ^ 13) (r0 / 10 ^ 10)

theorem epsB_pos : 0 < epsB := lt_min (by norm_num) (by have := r0_pos; positivity)
theorem epsB_le1 : epsB ≤ 1 / 10 ^ 13 := min_le_left _ _
theorem epsB_le2 : epsB ≤ r0 / 10 ^ 10 := min_le_right _ _

theorem Kc_two_le : Kc 2 ≤ 400000 := by
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  unfold Kc sig lamK Emax
  norm_num
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

theorem rho_witness_le : rhoM0 2 1 (Real.sqrt 2 * epsB) (4 * Real.sqrt 2 * epsB) ≤ 230 * epsB := by
  have hε := epsB_pos
  have hs2 : Real.sqrt 2 ≤ 1.5 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hs2' : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  unfold rhoM0; push_cast
  have e1 : (2 : ℝ) ^ 1 * (Real.sqrt 2 * epsB + 3 * Real.pi * (2 ^ 1 * (4 * Real.sqrt 2 * epsB)))
      = epsB * (2 * Real.sqrt 2 + 48 * Real.pi * Real.sqrt 2) := by ring
  rw [e1]
  have : 2 * Real.sqrt 2 + 48 * Real.pi * Real.sqrt 2 ≤ 230 := by nlinarith [mul_le_mul hpi.le hs2 hs2' (by norm_num)]
  nlinarith

theorem witnessKU_regime : M0RegimeR 2 1 Lu3 (U8 epsB) 1 1 (Real.sqrt 2 * epsB) (4 * Real.sqrt 2 * epsB) := by
  have hε := epsB_pos
  have hε1 := epsB_le1
  have hs2 : Real.sqrt 2 ≤ 1.5 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hs2' : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hρ : rhoM0 2 1 (Real.sqrt 2 * epsB) (4 * Real.sqrt 2 * epsB) ≤ 3e-11 :=
    rho_witness_le.trans (by nlinarith)
  have hρ0 : 0 ≤ rhoM0 2 1 (Real.sqrt 2 * epsB) (4 * Real.sqrt 2 * epsB) := by unfold rhoM0; positivity
  refine ⟨le_refl _, one_pos, one_pos, by positivity, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; show 2 * 2 ^ 1 < (3 + 1) * 2 ^ 1 - 1 + 1; norm_num
  · intro b; exact U8_link epsB hε.le b
  · exact plaq_of_pw_one (torusCfg (fE epsB)) _ (U8_plaq epsB hε.le)
  · push_cast; nlinarith
  · nlinarith
  · refine hρ.trans ?_; push_cast; norm_num
  · exact Theta_num _ hρ0 hρ

theorem witnessKU_small : KUSmall 2 (rhoM0 2 1 (Real.sqrt 2 * epsB) (4 * Real.sqrt 2 * epsB)) := by
  set ρ := rhoM0 2 1 (Real.sqrt 2 * epsB) (4 * Real.sqrt 2 * epsB) with hρdef
  have hε := epsB_pos
  have hε1 := epsB_le1
  have hε2 := epsB_le2
  have hr0 := r0_pos
  have hpi3 := Real.pi_gt_three
  have hpi := Real.pi_lt_d2
  have hρ230 : ρ ≤ 230 * epsB := rho_witness_le
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; unfold rhoM0; positivity
  have hρs : ρ ≤ 3e-11 := hρ230.trans (by nlinarith)
  have hK := Kc_two_le
  have hK0 : 0 < Kc 2 := Kc_pos 2 le_rfl
  have hq : ρ / (3 * Real.pi) ≤ ρ / 9 := div_le_div_of_nonneg_left hρ0 (by norm_num) (by linarith)
  have hρ2 : ρ ^ 2 ≤ 3e-11 * ρ := by nlinarith
  have hinner : ρ / (3 * Real.pi) + ρ ^ 2 ≤ ρ / 8 := by nlinarith
  have hkap : kapHat 2 ρ ≤ 50001 * ρ := by
    unfold kapHat
    have := mul_le_mul hK hinner (by positivity) (by norm_num)
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have : 8 * ((2 : ℕ) : ℝ) * kapHat 2 ρ ≤ 16 * (50001 * (230 * (1 / 10 ^ 13))) := by
      push_cast; nlinarith
    refine this.trans ?_
    rw [le_div_iff₀ (by positivity)]; nlinarith
  · have h1 : Kc 2 ^ 2 ≤ 400000 ^ 2 := pow_le_pow_left₀ hK0.le hK 2
    have h2 : ρ / (3 * Real.pi) + ρ ^ 2 ≤ 3e-11 / 8 := by nlinarith
    have h3 : 0 ≤ ρ / (3 * Real.pi) + ρ ^ 2 := by positivity
    nlinarith [mul_le_mul h1 h2 h3 (by positivity)]
  · have : (8 * ((2 : ℕ) : ℝ) - 6) * kapHat 2 ρ ≤ 10 * (50001 * (230 * (r0 / 10 ^ 10))) := by
      push_cast; nlinarith
    refine lt_of_le_of_lt this ?_
    nlinarith

theorem witnessKU_curved :
    ∃ p : PeriodicLatticePlaquette (scaleUp 2 1 Lu3), 0 < dv (periodicPlaquetteHolonomy (U8 epsB) p) := by
  refine ⟨(AdalyFormal.CurvBlock.o8, ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩), ?_⟩
  exact U8_nonflat epsB epsB_pos (by have := epsB_le1; have := Real.pi_gt_three; linarith)

/-- the k-uniform headline theorem at the curved witness. -/
def witnessKU_coercive (Lam : Set (PeriodicLatticeSite Lu3))
    (x : ↥(AdalyFormal.IngredientFamilyR2.bondSupp (AdalyFormal.SliceCoerc.GF 2 1 Lu3))) :=
  ginv_coercive_M0_kuniform 2 1 Lu3 (U8 epsB) 1 1 _ _ witnessKU_regime witnessKU_small Lam x

#print axioms Kc_two_le
#print axioms witnessKU_regime
#print axioms witnessKU_small
#print axioms witnessKU_curved
#print axioms witnessKU_coercive

#print axioms rho_witness_le
#print axioms epsB_pos
end AdalyFormal.RegBgKU
