import GW3

/-!
# W4N1 -- `W4Num` is satisfiable: real-analysis part (lane m1_w4num_20261014)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1W4Num

open AdalyFormal.M1GaugeW4
open AdalyFormal.M1IMS
open Filter

/-- `dDnum`, `dQnum` tend to `0` as `W → ∞`; so they are `≤ δ` from some `W₀` on (independent of everything else). -/
theorem dD_dQ_small (ell : ℕ) (a δ : ℝ) (hδ : 0 < δ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → dDnum ell W ≤ δ ∧ dQnum ell W a ≤ δ := by
  have hD : Tendsto (fun W : ℕ => dDnum ell W) atTop (nhds 0) := by
    have h0 : Tendsto (fun W : ℕ => 2 * (ell : ℝ) ^ 2 * Real.log ell / (W : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h2 := ((Real.continuous_exp.tendsto 0).comp h0).sub_const 1
    have h3 := h2.const_mul (Real.sqrt 3)
    simpa [dDnum] using h3
  have hQ : Tendsto (fun W : ℕ => dQnum ell W a) atTop (nhds 0) := by
    have h0 : Tendsto (fun W : ℕ => 3 * (ell : ℝ) * Real.log ell / (W : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h2 := ((Real.continuous_exp.tendsto 0).comp h0).sub_const 1
    have h3 := h2.const_mul (Real.sqrt a)
    simpa [dQnum] using h3
  have e1 := hD.eventually (ge_mem_nhds hδ)
  have e2 := hQ.eventually (ge_mem_nhds hδ)
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.1 (e1.and e2)
  exact ⟨W₀, hW₀⟩

theorem dD_nonneg (ell W : ℕ) : 0 ≤ dDnum ell W := by
  unfold dDnum
  have : (1 : ℝ) ≤ Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) := by
    apply Real.one_le_exp
    have := Real.log_natCast_nonneg ell
    positivity
  have := Real.sqrt_nonneg 3
  nlinarith

theorem dQ_nonneg (ell W : ℕ) (a : ℝ) : 0 ≤ dQnum ell W a := by
  unfold dQnum
  have : (1 : ℝ) ≤ Real.exp (3 * (ell : ℝ) * Real.log ell / W) := by
    apply Real.one_le_exp
    have := Real.log_natCast_nonneg ell
    positivity
  have := Real.sqrt_nonneg a
  nlinarith

/-- the `epsX` expression is `≤ (x + y) K` uniformly for `cs ∈ [c0, 1]`. -/
theorem epsX_le (x y q c c0 : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hq : 1 ≤ q)
    (hc0 : 0 < c0) (hcc : c0 ≤ c) (hc1 : c ≤ 1) :
    (4 / c) * y + (4 / c) * x * (q / Real.sqrt c)
      + (Real.sqrt (48 / c) * x + (8 / c) * x ^ 2 + (4 / c) * 1 * (2 * q * y + y ^ 2)) * (q / c)
    ≤ (x + y) * (4 / c0 + (1 / c0) ^ 2 * q * (23 + 8 * q)) := by
  have hc : 0 < c := lt_of_lt_of_le hc0 hcc
  have hq0 : 0 < q := by linarith
  set B : ℝ := 1 / c0 with hB
  have hB0 : 0 < B := by positivity
  have hu : 1 / c ≤ B := one_div_le_one_div_of_le hc0 hcc
  have hu0 : 0 < 1 / c := by positivity
  have hcs : c ≤ Real.sqrt c := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hsq0 : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hv : 1 / Real.sqrt c ≤ 1 / c := one_div_le_one_div_of_le hc hcs
  have hv0 : 0 < 1 / Real.sqrt c := by positivity
  have h1c : 1 ≤ 1 / c := (one_le_div hc).2 hc1
  have h48 : Real.sqrt (48 / c) ≤ 7 * (1 / c) := by
    rw [Real.sqrt_le_left (by positivity), div_le_iff₀ hc]
    have : (7 * (1 / c)) ^ 2 * c = 49 * (1 / c) := by field_simp; norm_num
    rw [this]
    nlinarith
  have hs0 : 0 ≤ Real.sqrt (48 / c) := Real.sqrt_nonneg _
  have hvB : 1 / Real.sqrt c ≤ B := le_trans hv hu
  have hxx : x ^ 2 ≤ x := by nlinarith
  have hyy : y ^ 2 ≤ y := by nlinarith
  have e1 : 4 / c = 4 * (1 / c) := by ring
  have e3 : q / c = q * (1 / c) := by ring
  have e2 : q / Real.sqrt c = q * (1 / Real.sqrt c) := by ring
  have e4 : 8 / c = 8 * (1 / c) := by ring
  rw [e1, e2, e3, e4]
  have f1 : 4 * (1 / c) * y ≤ 4 * B * y := by gcongr
  have f2 : 4 * (1 / c) * x * (q * (1 / Real.sqrt c)) ≤ 4 * B * x * (q * B) := by gcongr
  have a1 : Real.sqrt (48 / c) * x ≤ 7 * B * x := mul_le_mul_of_nonneg_right (by linarith) hx
  have a2 : 8 * (1 / c) * x ^ 2 ≤ 8 * B * x := by
    calc 8 * (1 / c) * x ^ 2 ≤ 8 * B * x ^ 2 := by gcongr
      _ ≤ 8 * B * x := mul_le_mul_of_nonneg_left hxx (by positivity)
  have a3 : 4 * (1 / c) * 1 * (2 * q * y + y ^ 2) ≤ 4 * B * 1 * (2 * q * y + y) :=
    mul_le_mul (by gcongr) (by linarith) (by positivity) (by positivity)
  have hP : Real.sqrt (48 / c) * x + 8 * (1 / c) * x ^ 2 + 4 * (1 / c) * 1 * (2 * q * y + y ^ 2)
      ≤ 7 * B * x + 8 * B * x + 4 * B * 1 * (2 * q * y + y) := by linarith
  have f3 := mul_le_mul hP (show q * (1 / c) ≤ q * B by gcongr)
    (by positivity) (by positivity)
  have g1 : 0 ≤ B * x := by positivity
  have g2 : 0 ≤ B ^ 2 * q * x := by positivity
  have g3 : 0 ≤ B ^ 2 * q * y := by positivity
  have hB4 : 4 / c0 = 4 * B := by rw [hB]; ring
  rw [hB4]
  nlinarith [f1, f2, f3, g1, g2, g3]

/-- the `ρ`-threshold constant of the `η` condition. -/
noncomputable def Keta (ell : ℕ) (c0 : ℝ) : ℝ := (960 * (ell : ℝ) ^ 10 + 45000 * (ell : ℝ) ^ 6) * (1 / c0) ^ 2

theorem etaC_lt (ell W : ℕ) (hell : 1 ≤ ell) (cs ρ c0 : ℝ) (hc0 : 0 < c0) (hcs : c0 ≤ cs) (hcs1 : cs ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / (4 * Keta ell c0)) (hdD : dDnum ell W ≤ 1) :
    etaC ell W cs ρ (1 / 4) < 1 := by
  have hL : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hcspos : 0 < cs := lt_of_lt_of_le hc0 hcs
  set B : ℝ := 1 / c0 with hB
  set L : ℝ := (ell : ℝ) with hLdef
  have hB1 : 1 ≤ B := by
    rw [hB]; exact (one_le_div hc0).2 (le_trans hcs hcs1)
  have hB0 : 0 < B := by linarith
  have hKeta : 1 ≤ Keta ell c0 := by
    unfold Keta
    rw [← hLdef, ← hB]
    have : 1 ≤ L ^ 10 := one_le_pow₀ hL
    have : 1 ≤ L ^ 6 := one_le_pow₀ hL
    have : 1 ≤ B ^ 2 := one_le_pow₀ hB1
    nlinarith [mul_pos (by positivity : (0:ℝ) < L ^ 10) (by positivity : (0:ℝ) < B ^ 2)]
  have hρ1 : ρ ≤ 1 := by
    have : 1 / (4 * Keta ell c0) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith
  have hρK : 4 * ρ * Keta ell c0 ≤ 1 := by
    have := (le_div_iff₀ (by linarith : (0:ℝ) < 4 * Keta ell c0)).1 hρ
    linarith
  have hu : 1 / cs ≤ B := one_div_le_one_div_of_le hc0 hcs
  have hu0 : 0 < 1 / cs := by positivity
  have hA : (4 * L / cs) ^ 2 ≤ 16 * L ^ 2 * B ^ 2 := by
    have : (4 * L / cs) ^ 2 = 16 * L ^ 2 * (1 / cs) ^ 2 := by field_simp; norm_num
    rw [this]
    have : (1 / cs) ^ 2 ≤ B ^ 2 := by gcongr
    nlinarith [sq_nonneg L]
  have hS : Real.sqrt (12 / cs) ≤ 4 * B := by
    rw [Real.sqrt_le_left (by positivity)]
    have : 12 / cs = 12 * (1 / cs) := by ring
    rw [this]
    nlinarith
  have h3 : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hdD0 := dD_nonneg ell W
  have hD3 : dDnum ell W * (4 / cs) ≤ 8 * B := by
    have e : 4 / cs = 4 * (1 / cs) := by ring
    rw [e]
    have := mul_le_mul hdD (show 4 * (1 / cs) ≤ 4 * B by linarith) (by positivity) (by norm_num)
    linarith
  have hBr : L * (Real.sqrt (12 / cs) + dDnum ell W * (4 / cs)) ≤ L * (12 * B) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
  have hBr0 : 0 ≤ L * (Real.sqrt (12 / cs) + dDnum ell W * (4 / cs)) := by
    have := Real.sqrt_nonneg (12 / cs)
    have := Real.sqrt_nonneg 3
    positivity
  have hBr2 : (L * (Real.sqrt (12 / cs) + dDnum ell W * (4 / cs))) ^ 2 ≤ 144 * L ^ 2 * B ^ 2 := by
    have := pow_le_pow_left₀ hBr0 hBr 2
    nlinarith
  have hν : 17 / Real.sqrt 2 ≤ 13 := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by norm_num))]
    have : (17 : ℝ) / 13 ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  have hν0 : 0 ≤ 17 / Real.sqrt 2 := by positivity
  have hνb : 17 / Real.sqrt 2 * 12 * (ρ * L ^ 4) ≤ 156 * (ρ * L ^ 4) := by
    have : 0 ≤ ρ * L ^ 4 := by positivity
    nlinarith
  have hT3 : 2 * (17 / Real.sqrt 2 * 12 * (ρ * L ^ 4)) *
      (L * (Real.sqrt (12 / cs) + dDnum ell W * (4 / cs))) ^ 2
      ≤ 2 * (156 * (ρ * L ^ 4)) * (144 * L ^ 2 * B ^ 2) := by
    apply mul_le_mul (by linarith) hBr2 (by positivity) (by positivity)
  have hT2 : (1 + 1 / (1 / 4 : ℝ)) * (12 * ρ ^ 2 * L ^ 8 * (4 * L / cs) ^ 2)
      ≤ 5 * (12 * ρ * L ^ 8 * (16 * L ^ 2 * B ^ 2)) := by
    have e : (1 + 1 / (1 / 4 : ℝ)) = 5 := by norm_num
    rw [e]
    have hρρ : ρ ^ 2 ≤ ρ := by nlinarith
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul _ hA (by positivity) (by positivity)
    have : 0 ≤ L ^ 8 := by positivity
    nlinarith
  unfold etaC nuC
  rw [← hLdef]
  have hfin : 4 * ρ * ((960 * L ^ 10 + 45000 * L ^ 6) * B ^ 2) ≤ 1 := by
    unfold Keta at hρK; rw [← hLdef, ← hB] at hρK; exact hρK
  have p1 : 0 ≤ ρ * L ^ 10 * B ^ 2 := by positivity
  have p2 : 0 ≤ ρ * L ^ 6 * B ^ 2 := by positivity
  unfold dDnum at hT3
  rw [← hLdef] at hT3
  nlinarith [hT2, hT3, hfin, p1, p2]

theorem cs_bounds (a ρ : ℝ) (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 24) :
    1 / (2 * max 6 (16 / (3 * a))) ≤ csOf a ρ ∧ csOf a ρ ≤ 1 := by
  have hm : 6 ≤ max 6 (16 / (3 * a)) := le_max_left _ _
  have hm0 : 0 < max 6 (16 / (3 * a)) := by linarith
  have h2 : ρ ^ 2 ≤ 1 / 576 := by nlinarith
  unfold csOf
  constructor
  · rw [show 1 / (2 * max 6 (16 / (3 * a))) = (1 / 2) / max 6 (16 / (3 * a)) by field_simp]
    apply div_le_div_of_nonneg_right _ hm0.le
    nlinarith
  · rw [div_le_one hm0]
    nlinarith [sq_nonneg ρ]

/-- the numerical threshold constants (depend on `ell`, `a` only). -/
noncomputable def c0Of (a : ℝ) : ℝ := 1 / (2 * max 6 (16 / (3 * a)))
noncomputable def Gof (ell : ℕ) (a : ℝ) : ℝ :=
  Real.sqrt (max a 1) * (9 / 4 + 4705 / a) *
    (4 / c0Of a + (1 / c0Of a) ^ 2 * Real.sqrt (max a 1) * (23 + 8 * Real.sqrt (max a 1)))
noncomputable def deltaOf (ell : ℕ) (a : ℝ) : ℝ := min 1 (min (c0Of a / 48) (1 / (16 * Gof ell a)))
noncomputable def rho0Of (ell : ℕ) (a : ℝ) : ℝ := min (1 / 24) (1 / (4 * Keta ell (c0Of a)))

theorem c0Of_pos (a : ℝ) (ha : 0 < a) : 0 < c0Of a := by
  unfold c0Of
  have : 6 ≤ max 6 (16 / (3 * a)) := le_max_left _ _
  have : 0 < max 6 (16 / (3 * a)) := by linarith
  positivity

theorem Gof_pos (ell : ℕ) (a : ℝ) (ha : 0 < a) : 0 < Gof ell a := by
  unfold Gof
  have := c0Of_pos a ha
  have : 1 ≤ Real.sqrt (max a 1) := by
    rw [Real.one_le_sqrt]; exact le_max_right _ _
  positivity

theorem deltaOf_pos (ell : ℕ) (a : ℝ) (ha : 0 < a) : 0 < deltaOf ell a := by
  unfold deltaOf
  have := c0Of_pos a ha
  have := Gof_pos ell a ha
  apply lt_min one_pos
  apply lt_min (by positivity) (by positivity)

theorem Keta_pos (ell : ℕ) (hell : 1 ≤ ell) (a : ℝ) (ha : 0 < a) : 0 < Keta ell (c0Of a) := by
  unfold Keta
  have := c0Of_pos a ha
  have hL : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  positivity

theorem rho0Of_pos (ell : ℕ) (hell : 1 ≤ ell) (a : ℝ) (ha : 0 < a) : 0 < rho0Of ell a := by
  unfold rho0Of
  have := Keta_pos ell hell a ha
  apply lt_min (by norm_num) (by positivity)

/-- **the four fields of `W4Num`, as inequalities in `ρ = ρ_T`, `ρh = ρ_h`** for `W` large and `ρ, ρh ≤ ρ₀`. -/
theorem w4Num_real (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ ρ ρh : ℝ, 0 ≤ ρ → ρ ≤ rho0Of ell a → 0 ≤ ρh → ρh ≤ rho0Of ell a →
      24 * (dDnum ell W ^ 2 + 1 * dQnum ell W a ^ 2) ≤ csOf a ρ ∧
      4 * dDnum ell W ^ 2 ≤ csOf a ρ ∧
      Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a) * epsXnum ell W a ρ < (1 - 12 * ρ) ^ 2 ∧
      etaC ell W (csOf a ρ) ρh (1 / 4) < 1 := by
  obtain ⟨W₀, hW₀⟩ := dD_dQ_small ell a (deltaOf ell a) (deltaOf_pos ell a ha)
  refine ⟨W₀, fun W hW ρ ρh hρ0 hρ hρh0 hρh => ?_⟩
  obtain ⟨hdD, hdQ⟩ := hW₀ W hW
  have hc0 := c0Of_pos a ha
  have hG := Gof_pos ell a ha
  have hδ0 := deltaOf_pos ell a ha
  have hδ1 : deltaOf ell a ≤ 1 := min_le_left _ _
  have hδ2 : deltaOf ell a ≤ c0Of a / 48 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ3 : deltaOf ell a ≤ 1 / (16 * Gof ell a) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hρ24 : ρ ≤ 1 / 24 := le_trans hρ (min_le_left _ _)
  obtain ⟨hcs0, hcs1⟩ := cs_bounds a ρ ha hρ0 hρ24
  have hx0 := dD_nonneg ell W
  have hy0 := dQ_nonneg ell W a
  have hx1 : dDnum ell W ≤ 1 := le_trans hdD hδ1
  have hy1 : dQnum ell W a ≤ 1 := le_trans hdQ hδ1
  have hcs0' : c0Of a ≤ csOf a ρ := hcs0
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · have hq : 1 ≤ Real.sqrt (max a 1) := by
      rw [Real.one_le_sqrt]; exact le_max_right _ _
    have hE := epsX_le (dDnum ell W) (dQnum ell W a) (Real.sqrt (max a 1)) (csOf a ρ) (c0Of a) hx0 hx1 hy0 hy1 hq hc0 hcs0' hcs1
    have hE' : epsXnum ell W a ρ ≤ (dDnum ell W + dQnum ell W a) * (4 / c0Of a + (1 / c0Of a) ^ 2 * Real.sqrt (max a 1) * (23 + 8 * Real.sqrt (max a 1))) := by
      unfold epsXnum; exact hE
    set K := 4 / c0Of a + (1 / c0Of a) ^ 2 * Real.sqrt (max a 1) * (23 + 8 * Real.sqrt (max a 1)) with hK
    have hK0 : 0 < K := by positivity
    set q := Real.sqrt (max a 1) with hqdef
    have hq0 : 0 < q := by linarith
    have hGdef : Gof ell a = q * (9 / 4 + 4705 / a) * K := rfl
    have hfac : (1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a ≤ 9 / 4 + 4705 / a := by
      have h1 : (1 + 12 * ρ) ^ 2 ≤ 9 / 4 := by nlinarith
      have h2 : (512 * ρ ^ 2 + 4704) / a ≤ 4705 / a := by
        apply div_le_div_of_nonneg_right _ ha.le
        nlinarith
      linarith
    have hxy : dDnum ell W + dQnum ell W a ≤ 2 * deltaOf ell a := by linarith
    have h1 : epsXnum ell W a ρ ≤ 2 * deltaOf ell a * K :=
      le_trans hE' (mul_le_mul_of_nonneg_right hxy hK0.le)
    have hf0 : 0 ≤ (1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a := by positivity
    have h2 : q * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a) * epsXnum ell W a ρ
        ≤ q * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a) * (2 * deltaOf ell a * K) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : q * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a) * (2 * deltaOf ell a * K)
        ≤ q * (9 / 4 + 4705 / a) * (2 * deltaOf ell a * K) := by gcongr
    have h4 : q * (9 / 4 + 4705 / a) * (2 * deltaOf ell a * K) = 2 * (Gof ell a * deltaOf ell a) := by
      rw [hGdef]; ring
    have h5 : deltaOf ell a * (16 * Gof ell a) ≤ 1 := (le_div_iff₀ (by positivity)).1 hδ3
    have h6 : 1 / 4 ≤ (1 - 12 * ρ) ^ 2 := by nlinarith
    nlinarith [h2, h3, h4, h5, h6]
  · exact etaC_lt ell W (by omega) (csOf a ρ) ρh (c0Of a) hc0 hcs0' hcs1 hρh0 (le_trans hρh (min_le_right _ _)) hx1

end AdalyFormal.M1W4Num
