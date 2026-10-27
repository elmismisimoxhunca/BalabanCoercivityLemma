import GG3
import MR4

/-!
# GG4 -- Lie-algebra charts ↔ group-level charts (m2_glue2, 2026-10-15)

* `exp_lip`: `|exp Z' − exp Z| ≤ (1 + 4|Z|)|Z' − Z|` on `su(2)` when `|Z| + |Z' − Z| ≤ 1` (Bch2 `group_bilinear`).
* `cubeZ`: a chart field `A` (Hermitian, `U^g = exp(iηA)`) gives `Z = iηA ∈ su(2)`, `|Z| = η|A|`.
* `chartOn_of_group`: group-level bounds `|U^g e − 1| ≤ T₁ ≤ 1`, `|U^g e' − U^g e| ≤ T₂` on the chart ball, with
  `(π/2)T₁ < a'ℓ^{-i}`, `(π/2)T₂ < a'ℓ^{-2i}`, give MR2's `ChartOn ell U η a' i w r` (A := η⁻¹(−i) log U^g).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Glue2

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2Angle coe_mul coe_inv coe_one su2Exp_of_mem)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq frobSq_nonneg)
open AdalyFormal.Balaban.Bch2 (IsSu2 frobNorm_add_le frobNorm_nonneg frobNorm_smul nu group_bilinear nu_mul_nu_eq
  frobNorm_eq_sqrt_two_mul_nu nu_nonneg isSu2_su2Log su2Log_lipschitz angle_le_of_frobNorm_sub_one
  frobNorm_su2Log_le)
open AdalyFormal.Balaban.RegularityGap (frobNorm_neg frobNorm_negI_smul frobNorm_I_smul su2_exp_log_of_frobNorm_lt)
open AdalyFormal.Balaban.ClassPropagationUbar (exp_mem_special frobNorm_su2Exp_sub_one_le_uncond)
open scoped Matrix

theorem coe_su2Exp {Z : M2} (hZ : IsSu2 Z) : ((su2Exp Z : SU2) : M2) = NormedSpace.exp Z :=
  su2Exp_of_mem (exp_mem_special hZ.1 hZ.2)

theorem nu_le_frobNorm (X : M2) : nu X ≤ frobNorm X := by
  rw [frobNorm_eq_sqrt_two_mul_nu]
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have := nu_nonneg X; nlinarith

theorem exp_sub_one_le {Z : M2} (hZ : IsSu2 Z) : frobNorm (((su2Exp Z : SU2) : M2) - 1) ≤ frobNorm Z :=
  frobNorm_su2Exp_sub_one_le_uncond hZ.1 hZ.2

/-- exponential is Lipschitz near `0` on `su(2)`. -/
theorem exp_lip {Z Z' : M2} (hZ : IsSu2 Z) (hZ' : IsSu2 Z') (hsm : frobNorm Z + frobNorm (Z' - Z) ≤ 1) :
    frobNorm (((su2Exp Z' : SU2) : M2) - (su2Exp Z : M2)) ≤ (1 + 4 * frobNorm Z) * frobNorm (Z' - Z) := by
  have hD : IsSu2 (Z' - Z) := hZ'.sub hZ
  have hdom : nu Z + nu (Z' - Z) ≤ Real.pi / 2 := by
    have := nu_le_frobNorm Z; have := nu_le_frobNorm (Z' - Z)
    have := Real.pi_gt_three; linarith
  have hg := group_bilinear hZ hD hdom
  rw [show Z + (Z' - Z) = Z' by abel] at hg
  have h1 : frobNorm (((su2Exp Z : SU2) : M2) * ((su2Exp (Z' - Z) : SU2) : M2) - (su2Exp Z : M2))
      ≤ frobNorm (Z' - Z) := by
    rw [show ((su2Exp Z : SU2) : M2) * ((su2Exp (Z' - Z) : SU2) : M2) - (su2Exp Z : M2)
        = ((su2Exp Z : SU2) : M2) * (((su2Exp (Z' - Z) : SU2) : M2) - 1) by noncomm_ring,
      frobNorm_su2_mul]
    exact exp_sub_one_le hD
  have h2 := frobNorm_sub_le' ((su2Exp Z' : SU2) : M2)
    (((su2Exp Z : SU2) : M2) * ((su2Exp (Z' - Z) : SU2) : M2)) (su2Exp Z : M2)
  have h4 := frobNorm_sub_comm ((su2Exp Z' : SU2) : M2)
    (((su2Exp Z : SU2) : M2) * ((su2Exp (Z' - Z) : SU2) : M2))
  have h3 : 8 * (nu Z * nu (Z' - Z)) = 4 * (frobNorm Z * frobNorm (Z' - Z)) := by
    rw [nu_mul_nu_eq]; ring
  nlinarith

/-- the Lie-algebra element of a chart: `Z = iηA`. -/
noncomputable def chZ (η : ℝ) (A : M2) : M2 := (((η : ℂ) * Complex.I)) • A

theorem isSu2_chZ (η : ℝ) {A : M2} (hA : AdalyFormal.StatementLane.HT A) : IsSu2 (chZ η A) := by
  refine ⟨?_, ?_⟩
  · rw [chZ, Matrix.conjTranspose_smul, hA.1]
    have : star ((η : ℂ) * Complex.I) = -((η : ℂ) * Complex.I) := by
      simp [Complex.conj_ofReal]
    rw [this, neg_smul]
  · rw [chZ, Matrix.trace_smul, hA.2, smul_zero]

theorem frobNorm_chZ {η : ℝ} (hη : 0 ≤ η) (A : M2) : frobNorm (chZ η A) = η * frobNorm A := by
  rw [chZ, mul_comm, ← smul_smul, frobNorm_I_smul]
  rw [show ((η : ℂ)) • A = (η : ℝ) • A by rfl, frobNorm_smul, abs_of_nonneg hη]

theorem chZ_sub (η : ℝ) (A B : M2) : chZ η A - chZ η B = chZ η (A - B) := by
  rw [chZ, chZ, chZ, smul_sub]

/-- the chart field read off a group element: `A = η⁻¹ (−i) log G`. -/
noncomputable def chA (η : ℝ) (G : SU2) : M2 := ((η⁻¹ : ℝ) : ℂ) • ((-Complex.I) • su2Log G)

theorem chA_HT (η : ℝ) (G : SU2) : AdalyFormal.StatementLane.HT (chA η G) := by
  have hs := isSu2_su2Log G
  refine ⟨?_, ?_⟩
  · rw [chA, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, hs.1]
    simp [Complex.conj_ofReal]
  · rw [chA, Matrix.trace_smul, Matrix.trace_smul, hs.2, smul_zero, smul_zero]

theorem chA_exp {η : ℝ} (hη : η ≠ 0) (G : SU2) (hG : frobNorm ((G : M2) - 1) ≤ 1) :
    (G : M2) = NormedSpace.exp ((((η : ℂ) * Complex.I)) • chA η G) := by
  have hkey : (((η : ℂ) * Complex.I)) • chA η G = su2Log G := by
    rw [chA, smul_smul, smul_smul]
    have : (η : ℂ) * Complex.I * ((η⁻¹ : ℝ) : ℂ) * (-Complex.I) = 1 := by
      have h1 : (η : ℂ) * ((η⁻¹ : ℝ) : ℂ) = 1 := by
        rw [Complex.ofReal_inv]; exact mul_inv_cancel₀ (by exact_mod_cast hη)
      calc (η : ℂ) * Complex.I * ((η⁻¹ : ℝ) : ℂ) * (-Complex.I)
          = ((η : ℂ) * ((η⁻¹ : ℝ) : ℂ)) * (-(Complex.I * Complex.I)) := by ring
        _ = 1 := by rw [h1, Complex.I_mul_I]; ring
    rw [this, one_smul]
  rw [hkey, ← coe_su2Exp (isSu2_su2Log G)]
  have h2 : frobNorm ((G : M2) - 1) < 2 * Real.sqrt 2 := by
    have : (1 : ℝ) < Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  rw [su2_exp_log_of_frobNorm_lt G h2]

theorem frobNorm_chA {η : ℝ} (hη : 0 < η) (G : SU2) : frobNorm (chA η G) = η⁻¹ * frobNorm (su2Log G) := by
  rw [chA, show (((η⁻¹ : ℝ) : ℂ)) • ((-Complex.I) • su2Log G) = (η⁻¹ : ℝ) • ((-Complex.I) • su2Log G) by rfl,
    frobNorm_smul, frobNorm_negI_smul, abs_of_pos (inv_pos.mpr hη)]

theorem chA_sub (η : ℝ) (G G' : SU2) :
    chA η G' - chA η G = ((η⁻¹ : ℝ) : ℂ) • ((-Complex.I) • (su2Log G' - su2Log G)) := by
  rw [chA, chA, ← smul_sub, ← smul_sub]

theorem log_le {G : SU2} (hG : frobNorm ((G : M2) - 1) ≤ 2) :
    frobNorm (su2Log G) ≤ (Real.pi / 2) * frobNorm ((G : M2) - 1) :=
  frobNorm_su2Log_le (angle_le_of_frobNorm_sub_one hG)

theorem log_lip {G G' : SU2} (hG : frobNorm ((G : M2) - 1) ≤ 2) (hG' : frobNorm ((G' : M2) - 1) ≤ 2) :
    frobNorm (su2Log G' - su2Log G) ≤ (Real.pi / 2) * frobNorm ((G' : M2) - (G : M2)) :=
  su2Log_lipschitz (angle_le_of_frobNorm_sub_one hG') (angle_le_of_frobNorm_sub_one hG)

variable {L : PeriodicLatticeExtent}

/-- **group-level bounds give MR2's `ChartOn`.** -/
theorem chartOn_of_group {ell : ℕ} (hell : 0 < ell) {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2}
    {η a' T1 T2 : ℝ} (hη : 0 < η) {i : ℕ} {w : PeriodicLatticeSite L} {r : ℕ} (hT1 : T1 ≤ 1)
    (h1 : ∀ e : PeriodicLatticeEdge L, AdalyFormal.StatementLane.pdist w e.1 ≤ r →
      frobNorm (((periodicGaugeTransform g U e : SU2) : M2) - 1) ≤ T1)
    (h2 : ∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L), AdalyFormal.StatementLane.pdist w x ≤ r →
      AdalyFormal.StatementLane.pdist w (periodicLatticeShift x μ) ≤ r →
      frobNorm (((periodicGaugeTransform g U (periodicLatticeShift x μ, ν) : SU2) : M2)
        - (periodicGaugeTransform g U (x, ν) : SU2)) ≤ T2)
    (ha1 : (Real.pi / 2) * T1 < a' * ((ell : ℝ) ^ i)⁻¹)
    (ha2 : (Real.pi / 2) * T2 < a' * (((ell : ℝ) ^ i)⁻¹) ^ 2) :
    AdalyFormal.M2Route.ChartOn ell U η a' i w r := by
  have hl : (0 : ℝ) < (ell : ℝ) ^ i := by positivity
  refine ⟨g, fun e => chA η (periodicGaugeTransform g U e), fun e => chA_HT η _, ?_, ?_, ?_⟩
  · intro e he
    exact chA_exp hη.ne' _ ((h1 e he).trans hT1)
  · intro e he
    have hb := h1 e he
    rw [frobNorm_chA hη]
    have hlog := log_le (hb.trans (hT1.trans (by norm_num)))
    have : η⁻¹ * frobNorm (su2Log (periodicGaugeTransform g U e)) ≤ η⁻¹ * ((Real.pi / 2) * T1) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hη.le)
      have := Real.pi_pos
      calc frobNorm (su2Log (periodicGaugeTransform g U e))
          ≤ (Real.pi / 2) * frobNorm (((periodicGaugeTransform g U e : SU2) : M2) - 1) := hlog
        _ ≤ (Real.pi / 2) * T1 := by gcongr
    refine this.trans_lt ?_
    rw [pow_one, mul_inv, show a' * (((ell : ℝ) ^ i)⁻¹ * η⁻¹) = η⁻¹ * (a' * ((ell : ℝ) ^ i)⁻¹) by ring]
    exact mul_lt_mul_of_pos_left ha1 (inv_pos.mpr hη)
  · intro μ ν x hx hx'
    have hb0 := h1 (x, ν) hx
    have hb1 := h1 (periodicLatticeShift x μ, ν) hx'
    have hd := h2 μ ν x hx hx'
    have hlip := log_lip (hb0.trans (hT1.trans (by norm_num))) (hb1.trans (hT1.trans (by norm_num)))
    rw [chA_sub, show ((η⁻¹ : ℝ)) • (((η⁻¹ : ℝ) : ℂ) • ((-Complex.I) • (su2Log (periodicGaugeTransform g U
        (periodicLatticeShift x μ, ν)) - su2Log (periodicGaugeTransform g U (x, ν)))))
        = (η⁻¹ * η⁻¹ : ℝ) • ((-Complex.I) • (su2Log (periodicGaugeTransform g U
        (periodicLatticeShift x μ, ν)) - su2Log (periodicGaugeTransform g U (x, ν)))) by
          rw [mul_smul]; rfl,
      frobNorm_smul, frobNorm_negI_smul, abs_of_pos (by positivity)]
    have : η⁻¹ * η⁻¹ * frobNorm (su2Log (periodicGaugeTransform g U (periodicLatticeShift x μ, ν))
        - su2Log (periodicGaugeTransform g U (x, ν))) ≤ η⁻¹ * η⁻¹ * ((Real.pi / 2) * T2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := Real.pi_pos
      exact hlip.trans (by gcongr)
    refine this.trans_lt ?_
    rw [mul_inv, show a' * (((ell : ℝ) ^ i)⁻¹ * η⁻¹) ^ 2 = η⁻¹ * η⁻¹ * (a' * (((ell : ℝ) ^ i)⁻¹) ^ 2) by ring]
    exact mul_lt_mul_of_pos_left ha2 (by positivity)

end AdalyFormal.M2Glue2
