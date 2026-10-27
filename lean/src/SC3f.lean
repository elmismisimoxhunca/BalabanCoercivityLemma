import SC3e

/-!
# SC3f -- the abstract cell theorem, NON-trivial twist (rank-one K-structure + margin argument).
Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped ComplexInnerProductSpace
open AdalyFormal.FlatCoercivity
open Finset

namespace AdalyFormal.ScaledCoercivity

section Main2
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {sd : SymData V}

theorem expand_form (x y : V) (c : ℂ) :
    ⟪x - c • y, sd.Lap (x - c • y)⟫ =
      ⟪x, sd.Lap x⟫ - c * ⟪x, sd.Lap y⟫ - (starRingEnd ℂ) c * ⟪y, sd.Lap x⟫
        + (starRingEnd ℂ) c * c * ⟪y, sd.Lap y⟫ := by
  rw [sd.Lap_sub, sd.Lap_smul]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  ring

/-- Euclidean vector of the three `Qm` values -/
noncomputable def Qv (sd : SymData V) (y : Fin 3 → V) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun μ => sd.Qm μ (y μ))

theorem norm_Qv_sq (y : Fin 3 → V) : ‖Qv sd y‖ ^ 2 = g2b sd y := by
  unfold Qv g2b
  rw [EuclideanSpace.norm_sq_eq]

theorem Qv_decomp (v wt : Fin 3 → V) (c : ℂ) (w : Fin 3 → V) (hw : ∀ μ, w μ = v μ + c • wt μ) :
    Qv sd w = Qv sd v + c • Qv sd wt := by
  ext μ
  simp only [Qv, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hw μ, Qm_add, Qm_smul]

theorem cell_abstract_nontrivial (md : ModeData sd) (κ A q0 β : ℝ) (hκ : 0 < κ) (hA : 0 < A)
    (hq0 : 0 ≤ q0) (hl0 : 0 < md.l0) (hq : ∀ μ, q0 ≤ ‖sd.Qm μ md.e0‖)
    (hAq : ∀ μ x, ‖sd.Qm μ x‖ ≤ A * ‖x‖) (hβ : β ≤ ‖⟪md.e0, sd.eps⟫‖ ^ 2) (hβ0 : 0 ≤ β)
    (μ0 : Fin 3) (hμ0 : sd.ph μ0 ≠ 1) (w : Fin 3 → V) (S : ℝ) (hS0 : 0 ≤ S)
    (hS : ∀ u, ⟪sd.eps, u⟫ = 0 → ‖⟪sd.Dstar w, sd.Lap u⟫‖ ^ 2 ≤ S * ‖sd.Lap u‖ ^ 2) :
    mu0c κ ((∑ μ, ‖sd.ph μ - 1‖ ^ 2) * β / md.l0 ^ 2) (A ^ 2 * (1 / md.l0 + 1 / md.G))
        / (1 + mu0c κ ((∑ μ, ‖sd.ph μ - 1‖ ^ 2) * β / md.l0 ^ 2) (A ^ 2 * (1 / md.l0 + 1 / md.G)))
        * lamN κ md.G A q0 * ∑ μ, ‖w μ‖ ^ 2 ≤ g1b sd w + κ * g2b sd w + S := by
  classical
  set ζ2 : ℝ := ∑ μ, ‖sd.ph μ - 1‖ ^ 2 with hζ2
  have hζ2nn : 0 ≤ ζ2 := Finset.sum_nonneg (fun _ _ => by positivity)
  set G2 : ℝ := ζ2 * β / md.l0 ^ 2 with hG2
  set S2 : ℝ := A ^ 2 * (1 / md.l0 + 1 / md.G) with hS2
  have hS2nn : 0 ≤ S2 := by
    have := md.G_pos
    positivity
  -- g = Lap⁻¹ eps, φ = Lap⁻¹ g
  obtain ⟨g, hg⟩ := sd.Lap_surj μ0 hμ0 sd.eps
  have hg0 : g ≠ 0 := by
    intro h; rw [h, Lap_zero] at hg; exact sd.eps_ne hg.symm
  obtain ⟨φ, hφ⟩ := sd.Lap_surj μ0 hμ0 g
  set ng : ℝ := ‖g‖ with hng_def
  have hng : 0 < ng := norm_pos_iff.mpr hg0
  have hgg : ⟪g, g⟫ = ((ng ^ 2 : ℝ) : ℂ) := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hepsφ : ⟪sd.eps, φ⟫ = ((ng ^ 2 : ℝ) : ℂ) := by
    rw [← hg, sd.Lap_selfadj, hφ, hgg]
  set cinv : ℂ := (((1 : ℝ) / ng : ℝ) : ℂ) with hcinv
  have hcinv_conj : (starRingEnd ℂ) cinv = cinv := by rw [hcinv]; exact Complex.conj_ofReal _
  set wt : Fin 3 → V := fun μ => cinv • sd.D μ φ with hwt
  set tt : ℂ := cinv * ⟪g, sd.Dstar w⟫ with htt
  -- F1
  have hLapwt : ∀ μ, sd.Lap (wt μ) = cinv • sd.D μ g := by
    intro μ
    simp only [hwt]
    rw [sd.Lap_smul, Lap_D, hφ]
  -- F2
  have hP1 : ∀ y : Fin 3 → V, ∑ μ, ⟪wt μ, sd.Lap (y μ)⟫ = cinv * ⟪g, sd.Dstar y⟫ := by
    intro y
    unfold SymData.Dstar
    rw [inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [← sd.Lap_selfadj, hLapwt, inner_smul_left, hcinv_conj, sd.inner_D]
  -- F3
  have hDwt : sd.Dstar wt = cinv • g := by
    unfold SymData.Dstar
    simp only [hwt, sd.Ds_smul]
    rw [← Finset.smul_sum]
    congr 1
  have hwt1 : ∑ μ, ⟪wt μ, sd.Lap (wt μ)⟫ = 1 := by
    rw [hP1, hDwt, inner_smul_right, hgg, hcinv]
    have : ((1 / ng : ℝ) : ℂ) * (((1 / ng : ℝ) : ℂ) * ((ng ^ 2 : ℝ) : ℂ)) = 1 := by
      have : (ng : ℂ) ≠ 0 := by exact_mod_cast hng.ne'
      push_cast
      field_simp
    exact this
  -- F4: Eb v
  set v : Fin 3 → V := fun μ => w μ - tt • wt μ with hv
  have hEbv : Eb sd v = Eb sd w - ‖tt‖ ^ 2 := by
    have hB : ∀ y : Fin 3 → V, ((Eb sd y : ℝ) : ℂ) = ∑ μ, ⟪y μ, sd.Lap (y μ)⟫ := by
      intro y; unfold Eb; push_cast
      exact Finset.sum_congr rfl (fun μ _ => Ef_eq sd (y μ))
    have hc : ((Eb sd v : ℝ) : ℂ) = ((Eb sd w - ‖tt‖ ^ 2 : ℝ) : ℂ) := by
      rw [hB v]
      have e1 : ∀ μ, ⟪v μ, sd.Lap (v μ)⟫ = ⟪w μ, sd.Lap (w μ)⟫ - tt * ⟪w μ, sd.Lap (wt μ)⟫
          - (starRingEnd ℂ) tt * ⟪wt μ, sd.Lap (w μ)⟫
          + (starRingEnd ℂ) tt * tt * ⟪wt μ, sd.Lap (wt μ)⟫ := fun μ => expand_form (w μ) (wt μ) tt
      simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have e2 : ∑ μ, ⟪w μ, sd.Lap (wt μ)⟫ = (starRingEnd ℂ) tt := by
        have : ∀ μ, ⟪w μ, sd.Lap (wt μ)⟫ = (starRingEnd ℂ) ⟪wt μ, sd.Lap (w μ)⟫ := by
          intro μ
          rw [← inner_conj_symm, sd.Lap_selfadj]
        simp only [this, ← map_sum]
        rw [hP1 w]
      rw [e2, hP1 w, hwt1, ← hB w]
      have hcc : (starRingEnd ℂ) tt * tt = ((‖tt‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' tt
      have h1 : tt * (starRingEnd ℂ) tt = ((‖tt‖ : ℝ) : ℂ) ^ 2 := by rw [mul_comm]; exact hcc
      have hh : cinv * ⟪g, sd.Dstar w⟫ = tt := rfl
      rw [hh]
      push_cast
      rw [h1, hcc]
      ring
    exact_mod_cast hc
  -- F5: Qv
  have hQ : Qv sd w = Qv sd v + tt • Qv sd wt :=
    Qv_decomp v wt tt w (fun μ => by simp [hv])
  -- F6
  have hP2 : ‖Qv sd wt‖ ^ 2 = ζ2 * ng ^ 2 := by
    rw [norm_Qv_sq]
    unfold g2b
    rw [hζ2, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    have : sd.Qm μ (wt μ) = cinv * ((sd.ph μ - 1) * ((ng ^ 2 : ℝ) : ℂ)) := by
      simp only [hwt]
      rw [Qm_smul, sd.Qm_D, hepsφ]
    rw [this, norm_mul, norm_mul, hcinv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    field_simp
  -- F7
  have hng2 : β ≤ md.l0 ^ 2 * ng ^ 2 := by
    have h1 : ⟪md.e0, sd.eps⟫ = (md.l0 : ℂ) * ⟪md.e0, g⟫ := by
      rw [← hg, ← sd.Lap_selfadj, md.lap_e0, inner_smul_left, Complex.conj_ofReal]
    have h2 : ‖⟪md.e0, g⟫‖ ≤ ‖md.e0‖ * ‖g‖ := norm_inner_le_norm _ _
    rw [md.norm_e0, one_mul] at h2
    have h3 : ‖⟪md.e0, sd.eps⟫‖ = md.l0 * ‖⟪md.e0, g⟫‖ := by
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg md.l0_nonneg]
    have h4 : ‖⟪md.e0, sd.eps⟫‖ ≤ md.l0 * ng := by
      rw [h3]; exact mul_le_mul_of_nonneg_left h2 md.l0_nonneg
    have h5 : ‖⟪md.e0, sd.eps⟫‖ ^ 2 ≤ (md.l0 * ng) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h4 2
    calc β ≤ ‖⟪md.e0, sd.eps⟫‖ ^ 2 := hβ
      _ ≤ (md.l0 * ng) ^ 2 := h5
      _ = md.l0 ^ 2 * ng ^ 2 := by ring
  have hPG : G2 ≤ ‖Qv sd wt‖ ^ 2 := by
    rw [hP2, hG2]
    have hl2 : 0 < md.l0 ^ 2 := by positivity
    rw [div_le_iff₀ hl2]
    have h9 := mul_le_mul_of_nonneg_left hng2 hζ2nn
    calc ζ2 * β ≤ ζ2 * (md.l0 ^ 2 * ng ^ 2) := h9
      _ = ζ2 * ng ^ 2 * md.l0 ^ 2 := by ring
  -- K bound
  have hK := S_ge_nontrivial sd g hg hg0 μ0 hμ0 w S hS0 hS
  have hT : ‖sd.Dstar w‖ ^ 2 - ‖tt‖ ^ 2 ≤ S := by
    have : ‖tt‖ ^ 2 = ‖⟪g, sd.Dstar w⟫‖ ^ 2 / ng ^ 2 := by
      rw [htt, norm_mul, hcinv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow,
        one_div, inv_pow]
      field_simp
    rw [this]; exact hK
  -- margin
  set T : ℝ := ‖tt‖ ^ 2 with hTdef
  have hS2b : g2b sd v ≤ S2 * Eb sd v := by
    have := S2_bound md hl0 A hA.le hAq v
    rw [hS2]; exact this
  have hEbv_nn : 0 ≤ Eb sd v := Eb_nonneg sd v
  set r : ℝ := Real.sqrt (Eb sd v) with hr
  have hr2 : r ^ 2 = Eb sd v := Real.sq_sqrt hEbv_nn
  set R : ℝ := ‖Qv sd v‖ with hR
  have hR2 : R ^ 2 = g2b sd v := norm_Qv_sq v
  have hRb : R ≤ Real.sqrt S2 * r := by
    have : R ≤ Real.sqrt (S2 * Eb sd v) := by
      apply Real.le_sqrt_of_sq_le
      rw [hR2]; exact hS2b
    rwa [Real.sqrt_mul hS2nn] at this
  set P : ℝ := ‖Qv sd wt‖ with hP
  set Q : ℝ := ‖Qv sd w‖ with hQdef
  have hQ2 : Q ^ 2 = g2b sd w := norm_Qv_sq w
  have htri : ‖tt‖ * P - R ≤ Q := by
    have h1 : ‖tt • Qv sd wt‖ ≤ ‖Qv sd w‖ + ‖Qv sd v‖ := by
      have : tt • Qv sd wt = Qv sd w - Qv sd v := by rw [hQ]; abel
      rw [this]; exact norm_sub_le _ _
    rw [norm_smul] at h1
    linarith
  have hsqrtκ : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hsqrtS2 : Real.sqrt S2 ^ 2 = S2 := Real.sq_sqrt hS2nn
  have hmq := margin_quad (α := Real.sqrt κ * P) (β := Real.sqrt κ * Real.sqrt S2) (r := r)
    (s := ‖tt‖) (q := Real.sqrt κ * Q) (by positivity) (norm_nonneg _) (by positivity)
    (Real.sqrt_nonneg _) (by positivity) (by
      have h1 : ‖tt‖ * P - Real.sqrt S2 * r ≤ Q := by linarith
      linarith [mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg κ)])
  have hFl : κ * P ^ 2 * T ≤ (1 + κ * S2) * (Eb sd v + κ * g2b sd w) := by
    have e1 : (Real.sqrt κ * P) ^ 2 * ‖tt‖ ^ 2 = κ * P ^ 2 * T := by rw [mul_pow, hsqrtκ]
    have e2 : (1 + (Real.sqrt κ * Real.sqrt S2) ^ 2) = 1 + κ * S2 := by rw [mul_pow, hsqrtκ, hsqrtS2]
    have e3 : r ^ 2 + (Real.sqrt κ * Q) ^ 2 = Eb sd v + κ * g2b sd w := by
      rw [mul_pow, hsqrtκ, hQ2, hr2]
    rw [e1, e2, e3] at hmq
    exact hmq
  set Fl : ℝ := Eb sd v + κ * g2b sd w with hFldef
  have hμT : mu0c κ G2 S2 * T ≤ Fl := by
    unfold mu0c
    have hpos : 0 < 1 + κ * S2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    have h1 : κ * G2 * T ≤ κ * P ^ 2 * T := by
      have := mul_le_mul_of_nonneg_left hPG hκ.le
      exact mul_le_mul_of_nonneg_right this (by positivity)
    linarith [hFl, h1, mul_comm Fl (1 + κ * S2)]
  have hFl_eq : Fl = (Eb sd w + κ * g2b sd w) - T := by
    rw [hFldef, hEbv]; ring
  have hFl_le : Fl ≤ g1b sd w + κ * g2b sd w + S := by
    have := weitz_b sd w
    rw [hFldef, hEbv]
    linarith
  have hN := N_coercive md κ A q0 hκ.le hA hq0 hq hAq w
  have hμ0nn : 0 ≤ mu0c κ G2 S2 := by
    unfold mu0c
    have : 0 ≤ G2 := by
      rw [hG2]; positivity
    positivity
  have hcomb := elem_combine (F := Fl) (N := Eb sd w + κ * g2b sd w) (T := T)
    (X := ∑ μ, ‖w μ‖ ^ 2) (lN := lamN κ md.G A q0) (μ0 := mu0c κ G2 S2) hFl_eq
    (by unfold lamN; exact hN) hμT hμ0nn
  have hpos : 0 < 1 + mu0c κ G2 S2 := by linarith
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hpos]
  calc mu0c κ G2 S2 * lamN κ md.G A q0 * ∑ μ, ‖w μ‖ ^ 2 ≤ (1 + mu0c κ G2 S2) * Fl := hcomb
    _ ≤ (1 + mu0c κ G2 S2) * (g1b sd w + κ * g2b sd w + S) := mul_le_mul_of_nonneg_left hFl_le hpos.le
    _ = _ := by ring

end Main2

#print axioms cell_abstract_nontrivial

end AdalyFormal.ScaledCoercivity
