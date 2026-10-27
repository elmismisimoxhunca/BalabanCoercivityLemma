import DLR54

/-!
# DL55 -- products of four `𝔰𝔲(2)` exponentials to second order; the `π Im` part of a plaquette holonomy

* `Exp2 P S T c σ` : `P = 1 + S + T + R`, `‖S‖ ≤ σ`, `‖T‖ ≤ σ²/2`, `‖R‖ ≤ cσ³`.  `exp2_mul` : right multiplication by `exp H`
  (`σ + ‖H‖ ≤ 1`) gives `Exp2 (P e^H) (S + H) (T + SH + ½H²) (c + 2) (σ + ‖H‖)` (uses `‖R e^H‖ = ‖R‖`, `e^H` unitary).
* `T4`, `S4` : the explicit second-order data of `e^{H₁}e^{H₂}e^{H₃}e^{H₄}`; `exp4` : `Exp2 .. S4 T4 8 (Σ‖Hᵢ‖)`.
* `Kc H₁..H₄ = Σ_{i<j} [Hᵢ,Hⱼ]`; `T4_skew` : `T4 − T4ᴴ = Kc` (all `Hᵢ` anti-Hermitian).
* **`plaq_expand`** : `π Im (e^{H₁}e^{H₂}e^{H₃}e^{H₄}) = (1/(2i))(2S4) + (1/(2i)) Kc + Rp`, `‖Rp‖ ≤ 16σ³`
  (`Im M = (1/(2i))(M − Mᴴ)`, `π` = traceless part; `S4`, `Kc` traceless).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped Matrix
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

structure Exp2 (P S T : Mt) (c σ : ℝ) : Prop where
  rem : frobNorm (P - 1 - S - T) ≤ c * σ ^ 3
  hS : frobNorm S ≤ σ
  hT : frobNorm T ≤ σ ^ 2 / 2
  hσ : 0 ≤ σ
  hc : 0 ≤ c

theorem exp2_one : Exp2 1 0 0 0 0 :=
  ⟨by simp [fN_zero], by simp [fN_zero], by simp [fN_zero], le_rfl, le_rfl⟩

theorem exp2_mul {P S T : Mt} {c σ : ℝ} (h : Exp2 P S T c σ) (H : Mt) (hH : AHT H)
    (h1 : σ + frobNorm H ≤ 1) :
    Exp2 (P * NormedSpace.exp H) (S + H) (T + S * H + (1 / 2 : ℝ) • (H * H)) (c + 2) (σ + frobNorm H) := by
  have hF0 := frobNorm_nonneg H
  have hσ := h.hσ
  have hF1 : frobNorm H ≤ 1 := by linarith
  set F := frobNorm H with hFdef
  set R := P - 1 - S - T with hR
  set E := NormedSpace.exp H - 1 - H - (1 / 2 : ℝ) • (H * H) with hE
  set Q := NormedSpace.exp H - 1 - H with hQ
  have hEb : frobNorm E ≤ F ^ 3 / 4 := exp_expand H hH hF1
  have hHH : frobNorm (H * H) ≤ F ^ 2 := by rw [sq]; exact fN_mul H H
  have hQb : frobNorm Q ≤ F ^ 2 / 2 + F ^ 3 / 4 := by
    have e : Q = (1 / 2 : ℝ) • (H * H) + E := by rw [hE]; abel
    rw [e]
    refine (fN_add _ _).trans ?_
    rw [fN_rsmul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hHQ : frobNorm (NormedSpace.exp H - 1) ≤ 2 * F := exp_sub_one_le H hH hF1
  have hU : NormedSpace.exp H * (NormedSpace.exp H)ᴴ = 1 := exp_unitary H hH
  have hRe : frobNorm (R * NormedSpace.exp H) = frobNorm R := fN_mul_unitary R _ hU
  have key : P * NormedSpace.exp H - 1 - (S + H) - (T + S * H + (1 / 2 : ℝ) • (H * H))
      = E + S * Q + T * (NormedSpace.exp H - 1) + R * NormedSpace.exp H := by
    rw [hE, hQ, hR]
    noncomm_ring
  have hsQ : frobNorm (S * Q) ≤ σ * (F ^ 2 / 2 + F ^ 3 / 4) :=
    (fN_mul S Q).trans (mul_le_mul h.hS hQb (frobNorm_nonneg _) hσ)
  have hTQ : frobNorm (T * (NormedSpace.exp H - 1)) ≤ σ ^ 2 / 2 * (2 * F) :=
    (fN_mul _ _).trans (mul_le_mul h.hT hHQ (frobNorm_nonneg _) (by positivity))
  refine ⟨?_, ?_, ?_, by positivity, by linarith [h.hc]⟩
  · rw [key]
    refine (fN_add _ _).trans ?_
    refine (add_le_add (fN_add _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add (fN_add _ _) le_rfl) le_rfl).trans ?_
    rw [hRe]
    have hRb := h.rem
    have hs1 : σ + F ≤ 1 := h1
    -- every monomial of degree ≥ 3 is ≤ (σ+F)³
    have m1 : F ^ 3 ≤ (σ + F) ^ 3 := pow_le_pow_left₀ hF0 (by linarith) 3
    have m3 : σ ^ 3 ≤ (σ + F) ^ 3 := pow_le_pow_left₀ hσ (by linarith) 3
    have m2 : σ * F ^ 2 ≤ (σ + F) ^ 3 := by nlinarith [mul_nonneg hσ hF0, mul_nonneg (mul_nonneg hσ hF0) hF0]
    have m4 : σ ^ 2 * F ≤ (σ + F) ^ 3 := by nlinarith [mul_nonneg hσ hF0, mul_nonneg (mul_nonneg hσ hσ) hF0]
    have m5 : σ * F ^ 3 ≤ (σ + F) ^ 3 := by
      have : σ * F ^ 3 ≤ σ * F ^ 2 := by
        have : F ^ 3 ≤ F ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left this hσ
      linarith
    have hc0 := h.hc
    nlinarith [mul_le_mul_of_nonneg_left m3 hc0]
  · exact (fN_add _ _).trans (by linarith [h.hS])
  · refine (fN_add _ _).trans ?_
    refine (add_le_add (fN_add _ _) le_rfl).trans ?_
    rw [fN_rsmul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hSH : frobNorm (S * H) ≤ σ * F := (fN_mul S H).trans (mul_le_mul_of_nonneg_right h.hS hF0)
    have := h.hT
    nlinarith

/-- the second-order data of four factors -/
noncomputable def S4 (H1 H2 H3 H4 : Mt) : Mt := H1 + H2 + H3 + H4

noncomputable def T4 (H1 H2 H3 H4 : Mt) : Mt :=
  (1 / 2 : ℝ) • (H1 * H1) + (1 / 2 : ℝ) • (H2 * H2) + (1 / 2 : ℝ) • (H3 * H3) + (1 / 2 : ℝ) • (H4 * H4)
    + H1 * H2 + H1 * H3 + H1 * H4 + H2 * H3 + H2 * H4 + H3 * H4

theorem exp4 (H1 H2 H3 H4 : Mt) (h1 : AHT H1) (h2 : AHT H2) (h3 : AHT H3) (h4 : AHT H4)
    (hs : frobNorm H1 + frobNorm H2 + frobNorm H3 + frobNorm H4 ≤ 1) :
    Exp2 (NormedSpace.exp H1 * NormedSpace.exp H2 * NormedSpace.exp H3 * NormedSpace.exp H4)
      (S4 H1 H2 H3 H4) (T4 H1 H2 H3 H4) 8
      (frobNorm H1 + frobNorm H2 + frobNorm H3 + frobNorm H4) := by
  have f1 := frobNorm_nonneg H1
  have f2 := frobNorm_nonneg H2
  have f3 := frobNorm_nonneg H3
  have f4 := frobNorm_nonneg H4
  have a := exp2_mul exp2_one H1 h1 (by linarith)
  have b := exp2_mul a H2 h2 (by linarith)
  have c := exp2_mul b H3 h3 (by linarith)
  have d := exp2_mul c H4 h4 (by linarith)
  have eP : 1 * NormedSpace.exp H1 * NormedSpace.exp H2 * NormedSpace.exp H3 * NormedSpace.exp H4
      = NormedSpace.exp H1 * NormedSpace.exp H2 * NormedSpace.exp H3 * NormedSpace.exp H4 := by rw [one_mul]
  have eS : 0 + H1 + H2 + H3 + H4 = S4 H1 H2 H3 H4 := by unfold S4; abel
  have eT : 0 + 0 * H1 + (1 / 2 : ℝ) • (H1 * H1) + (0 + H1) * H2 + (1 / 2 : ℝ) • (H2 * H2)
      + (0 + H1 + H2) * H3 + (1 / 2 : ℝ) • (H3 * H3) + (0 + H1 + H2 + H3) * H4 + (1 / 2 : ℝ) • (H4 * H4)
      = T4 H1 H2 H3 H4 := by unfold T4; noncomm_ring
  have eσ : 0 + frobNorm H1 + frobNorm H2 + frobNorm H3 + frobNorm H4
      = frobNorm H1 + frobNorm H2 + frobNorm H3 + frobNorm H4 := by ring
  have ec : (0 : ℝ) + 2 + 2 + 2 + 2 = 8 := by norm_num
  rw [eP, eS, eT, eσ, ec] at d
  exact d

/-- the commutator data -/
noncomputable def Kc (H1 H2 H3 H4 : Mt) : Mt :=
  (H1 * H2 - H2 * H1) + (H1 * H3 - H3 * H1) + (H1 * H4 - H4 * H1) + (H2 * H3 - H3 * H2)
    + (H2 * H4 - H4 * H2) + (H3 * H4 - H4 * H3)

theorem T4_skew (H1 H2 H3 H4 : Mt) (h1 : AHT H1) (h2 : AHT H2) (h3 : AHT H3) (h4 : AHT H4) :
    T4 H1 H2 H3 H4 - (T4 H1 H2 H3 H4)ᴴ = Kc H1 H2 H3 H4 := by
  unfold T4 Kc
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, h1.ah, h2.ah, h3.ah,
    h4.ah, star_trivial]
  have e : ∀ (X Y : Mt), (-X) * (-Y) = X * Y := fun X Y => by noncomm_ring
  simp only [e]
  noncomm_ring

theorem trace_comm (X Y : Mt) : Matrix.trace (X * Y - Y * X) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

theorem Kc_trace (H1 H2 H3 H4 : Mt) : Matrix.trace (Kc H1 H2 H3 H4) = 0 := by
  unfold Kc
  simp only [Matrix.trace_add, trace_comm, add_zero]

/-- the imaginary part `Im M = (1/(2i))(M − Mᴴ)` -/
noncomputable def imP (M : Mt) : Mt := (1 / (2 * Complex.I) : ℂ) • (M - Mᴴ)

theorem fN_imP_le (M : Mt) : frobNorm (imP M) ≤ frobNorm M := by
  unfold imP
  rw [fN_csmul]
  have h : ‖(1 / (2 * Complex.I) : ℂ)‖ = 1 / 2 := by simp
  rw [h]
  have := fN_sub M Mᴴ
  rw [fN_conjT] at this
  linarith [frobNorm_nonneg M]

/-- **the plaquette expansion** -/
theorem plaq_expand (H1 H2 H3 H4 : Mt) (h1 : AHT H1) (h2 : AHT H2) (h3 : AHT H3) (h4 : AHT H4)
    (hs : frobNorm H1 + frobNorm H2 + frobNorm H3 + frobNorm H4 ≤ 1) :
    ∃ Rp : Mt, AdalyFormal.Balaban.SourceJ.piProj
        (imP (NormedSpace.exp H1 * NormedSpace.exp H2 * NormedSpace.exp H3 * NormedSpace.exp H4))
      = (1 / (2 * Complex.I) : ℂ) • ((2 : ℂ) • S4 H1 H2 H3 H4)
        + (1 / (2 * Complex.I) : ℂ) • Kc H1 H2 H3 H4 + Rp
      ∧ frobNorm Rp ≤ 16 * (frobNorm H1 + frobNorm H2 + frobNorm H3 + frobNorm H4) ^ 3 := by
  have hE := exp4 H1 H2 H3 H4 h1 h2 h3 h4 hs
  set P := NormedSpace.exp H1 * NormedSpace.exp H2 * NormedSpace.exp H3 * NormedSpace.exp H4 with hP
  set R := P - 1 - S4 H1 H2 H3 H4 - T4 H1 H2 H3 H4 with hR
  have hSah : (S4 H1 H2 H3 H4)ᴴ = -S4 H1 H2 H3 H4 := by
    unfold S4; simp only [Matrix.conjTranspose_add, h1.ah, h2.ah, h3.ah, h4.ah]; abel
  have hPd : P - Pᴴ = (2 : ℂ) • S4 H1 H2 H3 H4 + Kc H1 H2 H3 H4 + (R - Rᴴ) := by
    have eP : P = 1 + S4 H1 H2 H3 H4 + T4 H1 H2 H3 H4 + R := by rw [hR]; abel
    have hK := T4_skew H1 H2 H3 H4 h1 h2 h3 h4
    rw [eP]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hSah]
    rw [← hK, two_smul]
    abel
  have hmain_tr : Matrix.trace ((1 / (2 * Complex.I) : ℂ) • ((2 : ℂ) • S4 H1 H2 H3 H4)
      + (1 / (2 * Complex.I) : ℂ) • Kc H1 H2 H3 H4) = 0 := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Kc_trace]
    unfold S4
    simp only [Matrix.trace_add, h1.tr, h2.tr, h3.tr, h4.tr]
    simp
  refine ⟨AdalyFormal.Balaban.SourceJ.piProj ((1 / (2 * Complex.I) : ℂ) • (R - Rᴴ)), ?_, ?_⟩
  · unfold imP
    rw [hPd, smul_add, smul_add]
    -- π is linear and fixes traceless matrices
    unfold AdalyFormal.Balaban.SourceJ.piProj
    rw [Matrix.trace_add, hmain_tr, zero_add]
    abel
  · refine (fN_piProj _).trans ?_
    have hr : frobNorm ((1 / (2 * Complex.I) : ℂ) • (R - Rᴴ)) ≤ frobNorm R := fN_imP_le R
    have hR8 := hE.rem
    rw [← hR] at hR8
    linarith

#print axioms exp2_mul
#print axioms exp4
#print axioms T4_skew
#print axioms Kc_trace
#print axioms fN_imP_le
#print axioms plaq_expand

end AdalyFormal.DLayer
