import MA14

/-!
# MA15 -- real numerics for the M1 assembly (lane m1_assembly_20261014)

* `gam1_ge`: explicit positive lower bound `Gamma / (4 (T+1))`, `T = 4/(1-eps1)`, for `gam1` under four smallness inequalities.
* `Etf`: the sandwich constant of `chart_config` as a function of `s = 12 M alpha0`; `small_window`: a threshold `s0` below which
  `Etf <= 1`, `dCof (kapM1 s) <= 1/2` and `(Etf a + 128 dC^2) cBm^2 <= Gamma/4`.
* `KG_small`: `KG ell M 1 5 -> 0` as `M -> infinity`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.M1Assembly

open Filter Topology
open AdalyFormal.M1Num (rhoH Ssr)
open AdalyFormal.M1IMS (nuC)
open AdalyFormal.TowerLoc (delStar)
open AdalyFormal.M1DK (kapM1 kapM1_nonneg qM1)

theorem gam1_ge (Γ a ε' εJ ε1 Et dC cB cBm : ℝ) (hΓ : 0 < Γ) (ha : 0 ≤ a) (hε1 : 0 < ε1) (hε1' : ε1 < 1)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' ≤ 1 / 2) (hεJ : 0 ≤ εJ) (hEt0 : 0 ≤ Et) (hEt1 : Et ≤ 1) (hdC : 0 ≤ dC)
    (hcB0 : 0 ≤ cB) (hcB : cB ≤ cBm)
    (hC2 : (Et * a + 128 * dC ^ 2) * cBm ^ 2 ≤ Γ / 4)
    (hC4 : (ε' * a + 2 * εJ) * cBm ^ 2 ≤ Γ / (8 * (4 / (1 - ε1) + 1))) :
    Γ / (4 * (4 / (1 - ε1) + 1)) ≤ gam1 Γ a ε' εJ ε1 Et dC cB := by
  have hd1 : 0 < 1 - ε1 := by linarith
  set T : ℝ := 4 / (1 - ε1) with hT
  have hT4 : 4 ≤ T := by rw [hT, le_div_iff₀ hd1]; linarith
  have hT1 : 0 < T + 1 := by linarith
  have hcB2 : cB ^ 2 ≤ cBm ^ 2 := pow_le_pow_left₀ hcB0 hcB 2
  have hc0 : 0 ≤ Et * a + 128 * dC ^ 2 := by positivity
  have hA : (Et * a + 128 * dC ^ 2) * cB ^ 2 ≤ Γ / 4 :=
    le_trans (mul_le_mul_of_nonneg_left hcB2 hc0) hC2
  have hnum : 3 * Γ / 4 ≤ Γ - (Et * a + 128 * dC ^ 2) * cB ^ 2 := by linarith
  have hnum0 : 0 ≤ Γ - (Et * a + 128 * dC ^ 2) * cB ^ 2 := by linarith
  have hden : 0 < T + Et := by linarith
  have h1 : (1 - ε') * (Γ - (Et * a + 128 * dC ^ 2) * cB ^ 2) / (T + Et) ≥ 3 * Γ / (8 * (T + 1)) := by
    rw [ge_iff_le, div_le_div_iff₀ (by positivity) hden]
    have e1 : (1 / 2 : ℝ) * (3 * Γ / 4) ≤ (1 - ε') * (Γ - (Et * a + 128 * dC ^ 2) * cB ^ 2) :=
      mul_le_mul (by linarith) hnum (by positivity) (by linarith)
    nlinarith [mul_nonneg hΓ.le hEt0]
  have hs5 : (ε' * a + 2 * εJ) * cB ^ 2 ≤ Γ / (8 * (T + 1)) :=
    le_trans (mul_le_mul_of_nonneg_left hcB2 (by positivity)) hC4
  unfold gam1
  have e2 : Γ / (4 * (T + 1)) = 3 * Γ / (8 * (T + 1)) - Γ / (8 * (T + 1)) := by field_simp; ring
  rw [e2]
  linarith

/-- the sandwich constant of `chart_config`, as a function of `s = 12 M alpha0`. -/
noncomputable def Etf (ell : ℕ) (ε1 cw s : ℝ) : ℝ :=
  (8 * ((17 / Real.sqrt 2) * 12 * (rhoH s * (ell : ℝ) ^ 4)) / (1 - ε1) + 4 * (32 * rhoH s ^ 2)
      + 128 * (3 * delStar ell (Ssr ell s) ^ 2)) / cw

theorem Etf_nonneg (ell : ℕ) (ε1 cw s : ℝ) (hε1 : ε1 < 1) (hcw : 0 < cw) (hs : 0 ≤ s) : 0 ≤ Etf ell ε1 cw s := by
  unfold Etf
  have h1 : 0 < 1 - ε1 := by linarith
  have h2 : 0 ≤ rhoH s := by unfold AdalyFormal.M1Num.rhoH; have := Real.pi_pos; positivity
  positivity

theorem Etf_tendsto (ell : ℕ) (ε1 cw : ℝ) :
    Tendsto (fun s => Etf ell ε1 cw s) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun s => Etf ell ε1 cw s) := by
    unfold Etf AdalyFormal.M1Num.Ssr AdalyFormal.TowerLoc.delStar AdalyFormal.M1Num.rhoH
    fun_prop
  have h := hc.tendsto 0
  have h0 : rhoH 0 = 0 := by simp [AdalyFormal.M1Num.rhoH]
  have hS0 : Ssr ell 0 = 0 := by simp [AdalyFormal.M1Num.Ssr, h0]
  have e : Etf ell ε1 cw 0 = 0 := by
    unfold Etf
    rw [h0, hS0]
    simp [AdalyFormal.TowerLoc.delStar]
  rwa [e] at h

theorem dC_tendsto (ell : ℕ) : Tendsto (fun s => dCof ell (kapM1 s)) (𝓝 0) (𝓝 0) := by
  have tk : Tendsto kapM1 (𝓝 0) (𝓝 0) := by
    have hc : Continuous kapM1 := by unfold kapM1 qM1; fun_prop
    have h := hc.tendsto 0
    rwa [show kapM1 0 = 0 by simp [kapM1, qM1]] at h
  have te := AdalyFormal.DLayer.te2rho tk ell
  have h1 : Tendsto (fun s => 384 * ((ell : ℝ) * kapM1 s) ^ 2 + 480 * (EstimatesLayer.E1E3.e2Majorant
      (AdalyFormal.NonflatJet.rhoOf ell (kapM1 s))) ^ 2) (𝓝 0) (𝓝 (384 * ((ell : ℝ) * 0) ^ 2 + 480 * 0 ^ 2)) :=
    (((tk.const_mul (ell : ℝ)).pow 2).const_mul 384).add ((te.pow 2).const_mul 480)
  have h2 := (h1.sqrt).const_mul ((ell : ℝ) ^ 3)
  unfold dCof
  simpa using h2

theorem small_window (ell : ℕ) (a ε1 cw Γ cBm : ℝ) (hε1 : ε1 < 1) (hcw : 0 < cw) (hΓ : 0 < Γ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 ≤ s → s ≤ s₀ →
      Etf ell ε1 cw s ≤ 1 ∧ dCof ell (kapM1 s) ≤ 1 / 2 ∧
      (Etf ell ε1 cw s * a + 128 * dCof ell (kapM1 s) ^ 2) * cBm ^ 2 ≤ Γ / 4 := by
  have tE := Etf_tendsto ell ε1 cw
  have tD := dC_tendsto ell
  have e1 : ∀ᶠ s in 𝓝 (0 : ℝ), Etf ell ε1 cw s < 1 := tE.eventually (gt_mem_nhds one_pos)
  have e2 : ∀ᶠ s in 𝓝 (0 : ℝ), dCof ell (kapM1 s) < 1 / 2 := tD.eventually (gt_mem_nhds (by norm_num))
  have t3 : Tendsto (fun s => (Etf ell ε1 cw s * a + 128 * dCof ell (kapM1 s) ^ 2) * cBm ^ 2) (𝓝 0)
      (𝓝 ((0 * a + 128 * 0 ^ 2) * cBm ^ 2)) :=
    (((tE.mul_const a).add ((tD.pow 2).const_mul 128)).mul_const (cBm ^ 2))
  have e3 : ∀ᶠ s in 𝓝 (0 : ℝ), (Etf ell ε1 cw s * a + 128 * dCof ell (kapM1 s) ^ 2) * cBm ^ 2 < Γ / 4 :=
    t3.eventually (gt_mem_nhds (by simp; linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (e1.and (e2.and e3))
  refine ⟨ε / 2, by positivity, fun s hs0 hs => ?_⟩
  have hd : dist s 0 < ε := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hs0]; linarith
  obtain ⟨a1, a2, a3⟩ := hball hd
  exact ⟨a1.le, a2.le, a3.le⟩

/-- `KG ell M 1 5 → 0` as `M → ∞`. -/
theorem KG_small (ell : ℕ) (δ : ℝ) (hδ : 0 < δ) : ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M →
    AdalyFormal.M1IMS.KG ell M 1 5 < δ := by
  have h : Tendsto (fun M : ℕ => AdalyFormal.M1IMS.KG ell M 1 5) atTop (𝓝 0) := by
    unfold AdalyFormal.M1IMS.KG
    have h1 : Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun M : ℕ => (ell : ℝ) ^ 2 / ((((5 : ℕ) : ℝ) - 4) * ((1 : ℕ) : ℝ) * (M : ℝ))) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := (ell : ℝ) ^ 2)).div_atTop h1
      norm_num
      exact this
    have h3 := ((h2.pow 2).const_mul (4 * ((6 * (3 * (2 * 5 + 1)) ^ 3 : ℕ) : ℝ)))
    simpa using h3
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp (h.eventually (gt_mem_nhds hδ))
  exact ⟨M₁, hM₁⟩

end AdalyFormal.M1Assembly

#print axioms AdalyFormal.M1Assembly.gam1_ge
#print axioms AdalyFormal.M1Assembly.Etf_tendsto
#print axioms AdalyFormal.M1Assembly.dC_tendsto
#print axioms AdalyFormal.M1Assembly.small_window
#print axioms AdalyFormal.M1Assembly.KG_small
