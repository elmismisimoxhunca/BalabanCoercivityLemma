import GG1

/-!
# GG2 -- Cayley interpolation in SU(2) (m2_glue2, 2026-10-15)

* `cayR Y = (1 + |Y|²/2)⁻¹ (1 + Y)` is `(1 − Y)⁻¹` on `su(2)` (`one_sub_mul_cayR`, `cayR_mul_one_sub`), with the resolvent
  identity `cayR_resolvent` and `|cayR Y| ≤ 3/2`.
* `cay Y = 2 cayR Y − 1 ∈ SU(2)` (`cayM_mem`), `cay 0 = 1`.
* `icay h = (1 + cos θ_h)⁻¹ Yof h ∈ su(2)`, `cay (icay h) = h` (`cay_icay`), `icay h = 1 − 2 S h` with
  `S h = (2(1+cos θ))⁻¹ (hᴴ + 1) = (1 + h)⁻¹` (`icay_eq`, `S_resolvent`), `|S h| ≤ 1`, `|icay h| ≤ |h − 1|` when
  `|h − 1| ≤ 2`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2Glue2

open Matrix
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2Angle coe_mul coe_inv coe_one)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq frobSq_nonneg)
open AdalyFormal.Balaban.Bch2 (IsSu2 frobNorm_add_le frobNorm_nonneg frobSq_smul isSu2_Yof nu nu_sq nu_Yof
  su2_decomp frobSq_su2_sub_one frobNorm_smul)
open AdalyFormal.Balaban.RegularityGap (Yof real_smul_eq su2_trace_eq frobNorm_neg)
open AdalyFormal.Balaban.ClassPropagationUbar (alg_sq comb_det comb_frobSq)
open scoped Matrix

/-! ## §1 the resolvent `cayR` -/

noncomputable def cayR (Y : M2) : M2 := ((1 + frobSq Y / 2)⁻¹ : ℝ) • ((1 : M2) + Y)

theorem sq_real {Y : M2} (hY : IsSu2 Y) : Y * Y = (-(frobSq Y / 2)) • (1 : M2) := by
  rw [alg_sq hY.1 hY.2, real_smul_eq]

theorem one_sub_mul_one_add {Y : M2} (hY : IsSu2 Y) :
    ((1 : M2) - Y) * ((1 : M2) + Y) = (1 + frobSq Y / 2) • (1 : M2) := by
  have e : ((1 : M2) - Y) * ((1 : M2) + Y) = 1 - Y * Y := by noncomm_ring
  rw [e, sq_real hY, sub_eq_add_neg, ← neg_smul, neg_neg, add_smul, one_smul]

theorem one_add_mul_one_sub {Y : M2} (hY : IsSu2 Y) :
    ((1 : M2) + Y) * ((1 : M2) - Y) = (1 + frobSq Y / 2) • (1 : M2) := by
  have e : ((1 : M2) + Y) * ((1 : M2) - Y) = 1 - Y * Y := by noncomm_ring
  rw [e, sq_real hY, sub_eq_add_neg, ← neg_smul, neg_neg, add_smul, one_smul]

theorem one_add_q_pos (Y : M2) : 0 < 1 + frobSq Y / 2 := by
  have := frobSq_nonneg Y; linarith

theorem one_sub_mul_cayR {Y : M2} (hY : IsSu2 Y) : ((1 : M2) - Y) * cayR Y = 1 := by
  rw [cayR, Matrix.mul_smul, one_sub_mul_one_add hY, smul_smul, inv_mul_cancel₀ (one_add_q_pos Y).ne',
    one_smul]

theorem cayR_mul_one_sub {Y : M2} (hY : IsSu2 Y) : cayR Y * ((1 : M2) - Y) = 1 := by
  rw [cayR, Matrix.smul_mul, one_add_mul_one_sub hY, smul_smul, inv_mul_cancel₀ (one_add_q_pos Y).ne',
    one_smul]

/-- resolvent identity `R(Y) − R(Y') = R(Y) (Y − Y') R(Y')`. -/
theorem cayR_resolvent {Y Y' : M2} (hY : IsSu2 Y) (hY' : IsSu2 Y') :
    cayR Y - cayR Y' = cayR Y * (Y - Y') * cayR Y' := by
  have e : cayR Y * (Y - Y') * cayR Y'
      = cayR Y * (((1 : M2) - Y') * cayR Y') - (cayR Y * ((1 : M2) - Y)) * cayR Y' := by noncomm_ring
  rw [e, one_sub_mul_cayR hY', cayR_mul_one_sub hY, Matrix.mul_one, Matrix.one_mul]

theorem frobSq_cayR {Y : M2} (hY : IsSu2 Y) : frobSq (cayR Y) = 2 / (1 + frobSq Y / 2) := by
  rw [cayR, frobSq_smul]
  have h := comb_frobSq hY.1 hY.2 1 1
  rw [one_smul, one_smul] at h
  rw [h]
  have hp := one_add_q_pos Y
  field_simp

theorem frobNorm_cayR_le {Y : M2} (hY : IsSu2 Y) : frobNorm (cayR Y) ≤ 3 / 2 := by
  have h : frobSq (cayR Y) ≤ (3 / 2) ^ 2 := by
    rw [frobSq_cayR hY]
    have hp := one_add_q_pos Y
    have hq := frobSq_nonneg Y
    rw [div_le_iff₀ hp]; nlinarith
  unfold frobNorm
  calc Real.sqrt (frobSq (cayR Y)) ≤ Real.sqrt ((3 / 2) ^ 2) := Real.sqrt_le_sqrt h
    _ = 3 / 2 := Real.sqrt_sq (by norm_num)

/-! ## §2 `cay` -/

noncomputable def cayM (Y : M2) : M2 := (2 : ℝ) • cayR Y - 1

theorem aux_c (q : ℝ) (hq : 0 ≤ q) : (1 - q) / (1 + q) = 2 * (1 + q)⁻¹ - 1 := by
  have : (1 + q) ≠ 0 := by linarith
  field_simp; ring

theorem aux_one (q : ℝ) (hq : 0 ≤ q) : ((1 - q) / (1 + q)) ^ 2 + (2 / (1 + q)) ^ 2 * q = 1 := by
  have : (1 + q) ≠ 0 := by linarith
  field_simp; ring

theorem cayM_eq {Y : M2} : cayM Y
    = ((1 - frobSq Y / 2) / (1 + frobSq Y / 2)) • (1 : M2) + (2 / (1 + frobSq Y / 2)) • Y := by
  rw [cayM, cayR, smul_smul, smul_add]
  have e1 : (1 - frobSq Y / 2) / (1 + frobSq Y / 2) = 2 * (1 + frobSq Y / 2)⁻¹ - 1 :=
    aux_c _ (by have := frobSq_nonneg Y; linarith)
  rw [e1, sub_smul, one_smul, show 2 / (1 + frobSq Y / 2) = 2 * (1 + frobSq Y / 2)⁻¹ by ring]
  abel

theorem cayM_mem {Y : M2} (hY : IsSu2 Y) : cayM Y ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  set c : ℝ := (1 - frobSq Y / 2) / (1 + frobSq Y / 2) with hc
  set d : ℝ := 2 / (1 + frobSq Y / 2) with hd
  have hp := one_add_q_pos Y
  have hone : c ^ 2 + d ^ 2 * (frobSq Y / 2) = 1 := by
    rw [hc, hd]; exact aux_one _ (by have := frobSq_nonneg Y; linarith)
  rw [cayM_eq]
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    have hct : (c • (1 : M2) + d • Y)ᴴ = c • (1 : M2) - d • Y := by
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one, hY.1, star_trivial, star_trivial, smul_neg, sub_eq_add_neg]
    rw [hct]
    have e : (c • (1 : M2) + d • Y) * (c • (1 : M2) - d • Y) = (c ^ 2) • (1 : M2) - (d ^ 2) • (Y * Y) := by
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one]
      module
    rw [e, sq_real hY, smul_smul, ← sub_smul]
    rw [show c ^ 2 - d ^ 2 * -(frobSq Y / 2) = 1 by linarith, one_smul]
  · rw [comb_det hY.1 hY.2, hone]; simp

open Classical in
noncomputable def cay (Y : M2) : SU2 := if h : IsSu2 Y then ⟨cayM Y, cayM_mem h⟩ else 1

theorem coe_cay {Y : M2} (hY : IsSu2 Y) : ((cay Y : SU2) : M2) = (2 : ℝ) • cayR Y - 1 := by
  classical
  simp only [cay, dif_pos hY]; rfl

theorem isSu2_zero : IsSu2 (0 : M2) := ⟨by simp, by simp⟩

theorem cay_zero : cay 0 = 1 := by
  have h0 : cayR 0 = 1 := by simp [cayR, frobSq]
  apply Subtype.ext
  rw [coe_cay isSu2_zero, h0, coe_one, two_smul]; abel

theorem cay_sub {Y Y' : M2} (hY : IsSu2 Y) (hY' : IsSu2 Y') :
    ((cay Y : SU2) : M2) - ((cay Y' : SU2) : M2) = (2 : ℝ) • (cayR Y - cayR Y') := by
  rw [coe_cay hY, coe_cay hY', smul_sub]; abel

theorem frobNorm_cay_sub_le {Y Y' : M2} (hY : IsSu2 Y) (hY' : IsSu2 Y') :
    frobNorm (((cay Y : SU2) : M2) - ((cay Y' : SU2) : M2)) ≤ (9 / 2) * frobNorm (Y - Y') := by
  rw [cay_sub hY hY', frobNorm_smul, cayR_resolvent hY hY']
  have := frobNorm_mul3_le (cayR Y) (Y - Y') (cayR Y')
  have a := frobNorm_cayR_le hY; have b := frobNorm_cayR_le hY'
  have := frobNorm_nonneg (cayR Y); have := frobNorm_nonneg (cayR Y')
  have := frobNorm_nonneg (Y - Y')
  rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have : frobNorm (cayR Y) * frobNorm (Y - Y') * frobNorm (cayR Y')
      ≤ (3/2) * frobNorm (Y - Y') * (3/2) := by gcongr
  linarith

theorem frobNorm_cay_sub_one_le {Y : M2} (hY : IsSu2 Y) :
    frobNorm (((cay Y : SU2) : M2) - 1) ≤ (9 / 2) * frobNorm Y := by
  have := frobNorm_cay_sub_le hY isSu2_zero
  rwa [cay_zero, sub_zero] at this

/-- second differences of `cay`. -/
theorem frobNorm_cay_second_le (Y : Fin 4 → M2) (hY : ∀ i, IsSu2 (Y i)) :
    frobNorm (((cay (Y 3) : SU2) : M2) - (cay (Y 2) : SU2) - (((cay (Y 1) : SU2) : M2) - (cay (Y 0) : SU2)))
      ≤ (9 / 2) * frobNorm (Y 3 - Y 2 - (Y 1 - Y 0))
        + (27 / 4) * (frobNorm (Y 3 - Y 1) + frobNorm (Y 2 - Y 0)) * frobNorm (Y 1 - Y 0) := by
  have e : ((cay (Y 3) : SU2) : M2) - (cay (Y 2) : SU2) - (((cay (Y 1) : SU2) : M2) - (cay (Y 0) : SU2))
      = (2 : ℝ) • (cayR (Y 3) - cayR (Y 2) - (cayR (Y 1) - cayR (Y 0))) := by
    rw [coe_cay (hY 3), coe_cay (hY 2), coe_cay (hY 1), coe_cay (hY 0)]
    simp only [smul_sub]; abel
  rw [e, frobNorm_smul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hr := resolvent_second_diff (fun i => cayR (Y i)) (fun i => -Y i)
    (fun i j => by
      rw [cayR_resolvent (hY i) (hY j)]
      congr 2; abel)
    (by norm_num : (0:ℝ) ≤ 3 / 2) (fun i => frobNorm_cayR_le (hY i))
  have e1 : -Y 3 - -Y 2 - (-Y 1 - -Y 0) = -(Y 3 - Y 2 - (Y 1 - Y 0)) := by abel
  have e2 : -Y 3 - -Y 1 = -(Y 3 - Y 1) := by abel
  have e3 : -Y 2 - -Y 0 = -(Y 2 - Y 0) := by abel
  have e4 : -Y 1 - -Y 0 = -(Y 1 - Y 0) := by abel
  rw [e1, e2, e3, e4, frobNorm_neg, frobNorm_neg, frobNorm_neg, frobNorm_neg] at hr
  nlinarith [hr]

/-! ## §3 inverse Cayley -/

/-- `cos θ_h = Re tr h / 2`. -/
noncomputable def acos2 (h : SU2) : ℝ := Real.cos (su2Angle h)

noncomputable def icay (h : SU2) : M2 := ((1 + acos2 h)⁻¹ : ℝ) • Yof h

theorem isSu2_icay (h : SU2) : IsSu2 (icay h) := (isSu2_Yof h).smul _

theorem frobSq_Yof (h : SU2) : frobSq (Yof h) = 2 * (1 - acos2 h ^ 2) := by
  have h1 := nu_sq (Yof h)
  rw [nu_Yof] at h1
  have h2 := Real.sin_sq_add_cos_sq (su2Angle h)
  rw [acos2]; nlinarith

theorem acos2_nonneg {h : SU2} (hh : frobNorm ((h : M2) - 1) ≤ 2) : 0 ≤ acos2 h := by
  have h1 := frobSq_su2_sub_one h
  have h2 : frobSq ((h : M2) - 1) ≤ 4 := by
    have := frobNorm_nonneg ((h : M2) - 1)
    have e : frobSq ((h : M2) - 1) = frobNorm ((h : M2) - 1) ^ 2 := by
      unfold frobNorm; rw [Real.sq_sqrt (frobSq_nonneg _)]
    rw [e]; nlinarith
  rw [acos2]; linarith

theorem acos2_le_one (h : SU2) : acos2 h ≤ 1 := Real.cos_le_one _

theorem cay_icay {h : SU2} (hh : frobNorm ((h : M2) - 1) ≤ 2) : cay (icay h) = h := by
  apply Subtype.ext
  have ha := acos2_nonneg hh
  have hq : frobSq (icay h) / 2 = (1 - acos2 h) / (1 + acos2 h) := by
    rw [icay, frobSq_smul, frobSq_Yof]
    field_simp; ring
  rw [coe_cay (isSu2_icay h), cayR, hq]
  have e1 : (1 + (1 - acos2 h) / (1 + acos2 h))⁻¹ = (1 + acos2 h) / 2 := by
    field_simp; ring
  rw [e1, icay]
  simp only [smul_add, smul_smul]
  have hp : (1 + acos2 h) ≠ 0 := by linarith
  have k1 : (2 : ℝ) * ((1 + acos2 h) / 2) = 1 + acos2 h := by ring
  have k2 : (2 : ℝ) * ((1 + acos2 h) / 2 * (1 + acos2 h)⁻¹) = 1 := by field_simp
  rw [k1, k2]
  conv_rhs => rw [su2_decomp h]
  rw [acos2]
  module

/-- `S h = (2(1 + cos θ))⁻¹ (hᴴ + 1)`, which is `(1 + h)⁻¹`. -/
noncomputable def Sres (h : SU2) : M2 := ((2 * (1 + acos2 h))⁻¹ : ℝ) • ((h : M2)ᴴ + 1)

theorem add_star_su2 (h : SU2) : (h : M2) + (h : M2)ᴴ = (2 * acos2 h) • (1 : M2) := by
  rw [AdalyFormal.Balaban.RegularityGap.su2_add_conjTranspose, su2_trace_eq, real_smul_eq, acos2]

theorem one_add_mul_S {h : SU2} (ha : 0 ≤ acos2 h) : ((1 : M2) + h) * Sres h = 1 := by
  rw [Sres, Matrix.mul_smul]
  have e : ((1 : M2) + h) * ((h : M2)ᴴ + 1) = (2 : ℝ) • (1 : M2) + ((h : M2) + (h : M2)ᴴ) := by
    have u := su2_mul_star h
    have e' : ((1 : M2) + h) * ((h : M2)ᴴ + 1) = 1 + (h : M2) * (h : M2)ᴴ + ((h : M2) + (h : M2)ᴴ) := by
      noncomm_ring
    rw [e', u, two_smul]
  rw [e, add_star_su2, ← add_smul, smul_smul]
  rw [show (2 * (1 + acos2 h))⁻¹ * (2 + 2 * acos2 h) = 1 by field_simp, one_smul]

theorem S_mul_one_add {h : SU2} (ha : 0 ≤ acos2 h) : Sres h * ((1 : M2) + h) = 1 := by
  rw [Sres, Matrix.smul_mul]
  have e : ((h : M2)ᴴ + 1) * ((1 : M2) + h) = (2 : ℝ) • (1 : M2) + ((h : M2) + (h : M2)ᴴ) := by
    have u := su2_star_mul h
    have e' : ((h : M2)ᴴ + 1) * ((1 : M2) + h) = 1 + (h : M2)ᴴ * (h : M2) + ((h : M2) + (h : M2)ᴴ) := by
      noncomm_ring
    rw [e', u, two_smul]
  rw [e, add_star_su2, ← add_smul, smul_smul]
  rw [show (2 * (1 + acos2 h))⁻¹ * (2 + 2 * acos2 h) = 1 by field_simp, one_smul]

theorem S_resolvent {h h' : SU2} (ha : 0 ≤ acos2 h) (ha' : 0 ≤ acos2 h') :
    Sres h - Sres h' = Sres h * ((h' : M2) - h) * Sres h' := by
  have e : Sres h * ((h' : M2) - h) * Sres h'
      = Sres h * (((1 : M2) + h') * Sres h') - (Sres h * ((1 : M2) + h)) * Sres h' := by noncomm_ring
  rw [e, one_add_mul_S ha', S_mul_one_add ha, Matrix.mul_one, Matrix.one_mul]

theorem frobNorm_S_le {h : SU2} (ha : 0 ≤ acos2 h) : frobNorm (Sres h) ≤ 1 := by
  have hYs := isSu2_Yof h
  have hdec : (h : M2)ᴴ + 1 = (1 + acos2 h) • (1 : M2) + (-1 : ℝ) • Yof h := by
    have e : (h : M2)ᴴ = acos2 h • (1 : M2) - Yof h := by
      have := add_star_su2 h
      rw [su2_decomp h] at this ⊢
      rw [acos2] at this ⊢
      have hc : ((Real.cos (su2Angle h)) • (1 : M2) + Yof h)ᴴ = Real.cos (su2Angle h) • (1 : M2) - Yof h := by
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hYs.1, star_trivial,
          sub_eq_add_neg]
      exact hc
    rw [e, add_smul, one_smul, neg_one_smul]; abel
  have hf : frobSq ((h : M2)ᴴ + 1) = 4 * (1 + acos2 h) := by
    rw [hdec, comb_frobSq hYs.1 hYs.2, frobSq_Yof]; ring
  have hs : frobSq (Sres h) ≤ 1 := by
    rw [Sres, frobSq_smul, hf]
    have hp : 0 < 1 + acos2 h := by linarith
    rw [inv_pow, ← div_eq_inv_mul, div_le_one (by positivity)]
    nlinarith
  unfold frobNorm
  calc Real.sqrt (frobSq (Sres h)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hs
    _ = 1 := Real.sqrt_one

theorem icay_eq {h : SU2} (ha : 0 ≤ acos2 h) : icay h = 1 - (2 : ℝ) • Sres h := by
  have hYs := isSu2_Yof h
  have e : (h : M2)ᴴ = acos2 h • (1 : M2) - Yof h := by
    have hc : ((Real.cos (su2Angle h)) • (1 : M2) + Yof h)ᴴ = Real.cos (su2Angle h) • (1 : M2) - Yof h := by
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hYs.1, star_trivial,
        sub_eq_add_neg]
    conv_lhs => rw [su2_decomp h]
    exact hc
  rw [icay, Sres, e, smul_smul]
  have hp : (1 + acos2 h) ≠ 0 := by linarith
  rw [show (2 : ℝ) * (2 * (1 + acos2 h))⁻¹ = (1 + acos2 h)⁻¹ by field_simp]
  rw [show acos2 h • (1 : M2) - Yof h + 1 = (1 + acos2 h) • (1 : M2) - Yof h by rw [add_smul, one_smul]; abel]
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hp, one_smul]; abel

theorem icay_sub {h h' : SU2} (ha : 0 ≤ acos2 h) (ha' : 0 ≤ acos2 h') :
    icay h - icay h' = (-2 : ℝ) • (Sres h - Sres h') := by
  rw [icay_eq ha, icay_eq ha', smul_sub]; module

theorem frobNorm_icay_sub_le {h h' : SU2} (ha : 0 ≤ acos2 h) (ha' : 0 ≤ acos2 h') :
    frobNorm (icay h - icay h') ≤ 2 * frobNorm ((h : M2) - h') := by
  rw [icay_sub ha ha', frobNorm_smul, S_resolvent ha ha']
  have := frobNorm_mul3_le (Sres h) ((h' : M2) - h) (Sres h')
  have a := frobNorm_S_le ha; have b := frobNorm_S_le ha'
  have := frobNorm_nonneg (Sres h); have := frobNorm_nonneg (Sres h')
  have := frobNorm_nonneg ((h' : M2) - h)
  rw [frobNorm_sub_comm (h' : M2) h] at *
  have : frobNorm (Sres h) * frobNorm ((h : M2) - h') * frobNorm (Sres h') ≤ 1 * frobNorm ((h : M2) - h') * 1 := by
    gcongr
  norm_num at *; linarith

theorem frobNorm_icay_le {h : SU2} (hh : frobNorm ((h : M2) - 1) ≤ 2) :
    frobNorm (icay h) ≤ frobNorm ((h : M2) - 1) := by
  have ha := acos2_nonneg hh
  have e1 : frobSq (icay h) ≤ frobSq ((h : M2) - 1) := by
    rw [icay, frobSq_smul, frobSq_Yof, frobSq_su2_sub_one, ← acos2]
    have hp : 0 < 1 + acos2 h := by linarith
    have hle := acos2_le_one h
    rw [inv_pow]
    rw [show ((1 + acos2 h) ^ 2)⁻¹ * (2 * (1 - acos2 h ^ 2)) = 2 * (1 - acos2 h) / (1 + acos2 h) by
      field_simp; ring]
    rw [div_le_iff₀ hp]; nlinarith
  unfold frobNorm; exact Real.sqrt_le_sqrt e1

theorem frobNorm_icay_second_le (h : Fin 4 → SU2) (ha : ∀ i, 0 ≤ acos2 (h i)) :
    frobNorm (icay (h 3) - icay (h 2) - (icay (h 1) - icay (h 0)))
      ≤ 2 * frobNorm (((h 3 : SU2) : M2) - h 2 - ((h 1 : M2) - h 0))
        + 2 * (frobNorm (((h 3 : SU2) : M2) - h 1) + frobNorm (((h 2 : SU2) : M2) - h 0))
          * frobNorm (((h 1 : SU2) : M2) - h 0) := by
  have e : icay (h 3) - icay (h 2) - (icay (h 1) - icay (h 0))
      = (-2 : ℝ) • (Sres (h 3) - Sres (h 2) - (Sres (h 1) - Sres (h 0))) := by
    rw [icay_eq (ha 3), icay_eq (ha 2), icay_eq (ha 1), icay_eq (ha 0)]; module
  rw [e, frobNorm_smul]
  have hr := resolvent_second_diff (fun i => Sres (h i)) (fun i => ((h i : SU2) : M2))
    (fun i j => S_resolvent (ha i) (ha j)) (by norm_num : (0:ℝ) ≤ 1) (fun i => frobNorm_S_le (ha i))
  simp only [one_pow, one_mul] at hr
  rw [show |(-2 : ℝ)| = 2 by norm_num]
  nlinarith [hr]

end AdalyFormal.M2Glue2
