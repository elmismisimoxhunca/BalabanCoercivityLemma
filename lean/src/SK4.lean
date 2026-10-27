import SK3

/-!
# SK4 -- numerics of the M2 unit chain (lane m2_skeleton_20261015)

* `Etc` : the sandwich constant of `chart_core_class` as a function of `s = 12 M α₁` (analogue of MA15 `Etf`, with the unit-floor coefficient of `δ*²`).
* `Etc_window` : `Etc ≤ 1` and `Etc · a ≤ Γ/4` for small `s`.
* `cU_lower` : `cU ℓ Mc κ(s) 1 1 ≥ 1/(108 ℓ⁵)` for `s` small and `Mc` large.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace AdalyFormal.M2Skel

open Filter Topology
open AdalyFormal.M1Num (rhoH Ssr)
open AdalyFormal.TowerLoc (delStar rho1 SstarM)
open AdalyFormal.M1DK (kapM1 kapM1_nonneg)
open AdalyFormal.NonflatJet (rhoOf)

/-- the sandwich constant of `chart_core_class` at `ε = ε' = 1` (unit floor), as a function of `s = 12 M α₁`. -/
noncomputable def Etc (ell : ℕ) (ε1 cw s : ℝ) : ℝ :=
  (8 * ((17 / Real.sqrt 2) * 12 * (rhoH s * (ell : ℝ) ^ 4)) / (1 - ε1)
    + 4 * ((2 * (2 * 64 * rhoH s ^ 2 + 2 * 62208 * delStar ell (Ssr ell s) ^ 2)) / (2 * 2 * 2))) / cw

theorem Etc_nonneg (ell : ℕ) (ε1 cw s : ℝ) (hε1 : ε1 < 1) (hcw : 0 < cw) (hs : 0 ≤ s) : 0 ≤ Etc ell ε1 cw s := by
  unfold Etc
  have h1 : 0 < 1 - ε1 := by linarith
  have h2 : 0 ≤ rhoH s := by unfold AdalyFormal.M1Num.rhoH; have := Real.pi_pos; positivity
  positivity

theorem Etc_tendsto (ell : ℕ) (ε1 cw : ℝ) : Tendsto (fun s => Etc ell ε1 cw s) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun s => Etc ell ε1 cw s) := by
    unfold Etc AdalyFormal.M1Num.Ssr AdalyFormal.TowerLoc.delStar AdalyFormal.M1Num.rhoH
    fun_prop
  have h := hc.tendsto 0
  have h0 : rhoH 0 = 0 := by simp [AdalyFormal.M1Num.rhoH]
  have hS0 : Ssr ell 0 = 0 := by simp [AdalyFormal.M1Num.Ssr, h0]
  have e : Etc ell ε1 cw 0 = 0 := by
    unfold Etc
    rw [h0, hS0]
    simp [AdalyFormal.TowerLoc.delStar]
  rwa [e] at h

theorem Etc_window (ell : ℕ) (a ε1 cw Γ : ℝ) (hε1 : ε1 < 1) (hcw : 0 < cw) (hΓ : 0 < Γ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 ≤ s → s ≤ s₀ → Etc ell ε1 cw s ≤ 1 ∧ Etc ell ε1 cw s * a ≤ Γ / 4 := by
  have tE := Etc_tendsto ell ε1 cw
  have e1 : ∀ᶠ s in 𝓝 (0 : ℝ), Etc ell ε1 cw s < 1 := tE.eventually (gt_mem_nhds one_pos)
  have t3 : Tendsto (fun s => Etc ell ε1 cw s * a) (𝓝 0) (𝓝 (0 * a)) := tE.mul_const a
  have e3 : ∀ᶠ s in 𝓝 (0 : ℝ), Etc ell ε1 cw s * a < Γ / 4 := t3.eventually (gt_mem_nhds (by simp; linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (e1.and e3)
  refine ⟨ε / 2, by positivity, fun s hs0 hs => ?_⟩
  have hd : dist s 0 < ε := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hs0]; linarith
  obtain ⟨a1, a3⟩ := hball hd
  exact ⟨a1.le, a3.le⟩

theorem cu_window (ell : ℕ) (hell : 0 < ell) : ∃ s₁ : ℝ, 0 < s₁ ∧ ∀ s : ℝ, 0 ≤ s → s ≤ s₁ →
    rhoOf ell (kapM1 s) ≤ 1 / 10 ∧ (384 * 930 ^ 2 * (ell : ℝ) ^ 3 + 384) * kapM1 s ^ 2 ≤ 1 / (216 * (ell : ℝ) ^ 5) := by
  have tk : Tendsto kapM1 (𝓝 0) (𝓝 0) := by
    have hc : Continuous kapM1 := by unfold kapM1 AdalyFormal.M1DK.qM1; fun_prop
    have h := hc.tendsto 0
    rwa [show kapM1 0 = 0 by simp [kapM1, AdalyFormal.M1DK.qM1]] at h
  have tr : Tendsto (fun s => rhoOf ell (kapM1 s)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun s => rhoOf ell (kapM1 s)) := by
      unfold rhoOf kapM1 AdalyFormal.M1DK.qM1; fun_prop
    have h := hc.tendsto 0
    rwa [show rhoOf ell (kapM1 0) = 0 by simp [rhoOf, kapM1, AdalyFormal.M1DK.qM1]] at h
  have tq : Tendsto (fun s => (384 * 930 ^ 2 * (ell : ℝ) ^ 3 + 384) * kapM1 s ^ 2) (𝓝 0) (𝓝 ((384 * 930 ^ 2 * (ell : ℝ) ^ 3 + 384) * 0 ^ 2)) :=
    (tk.pow 2).const_mul _
  have hp : (0 : ℝ) < 1 / (216 * (ell : ℝ) ^ 5) := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  have e1 : ∀ᶠ s in 𝓝 (0 : ℝ), rhoOf ell (kapM1 s) < 1 / 10 := tr.eventually (gt_mem_nhds (by norm_num))
  have e2 : ∀ᶠ s in 𝓝 (0 : ℝ), (384 * 930 ^ 2 * (ell : ℝ) ^ 3 + 384) * kapM1 s ^ 2 < 1 / (216 * (ell : ℝ) ^ 5) :=
    tq.eventually (gt_mem_nhds (by simpa using hp))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (e1.and e2)
  refine ⟨ε / 2, by positivity, fun s hs0 hs => ?_⟩
  have hd : dist s 0 < ε := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hs0]; linarith
  obtain ⟨a1, a2⟩ := hball hd
  exact ⟨a1.le, a2.le⟩

theorem Mc_window (ell : ℕ) (hell : 0 < ell) : ∃ Mc₀ : ℕ, 0 < Mc₀ ∧ ∀ Mc : ℕ, Mc₀ ≤ Mc →
    16 * Real.pi ^ 2 / (Mc : ℝ) ^ 2 ≤ 1 / (216 * (ell : ℝ) ^ 5) := by
  have hl : (0 : ℝ) < ell := by exact_mod_cast hell
  refine ⟨⌈16 * Real.pi ^ 2 * (216 * (ell : ℝ) ^ 5)⌉₊ + 1, by omega, fun Mc hMc => ?_⟩
  have h1 : 16 * Real.pi ^ 2 * (216 * (ell : ℝ) ^ 5) ≤ (Mc : ℝ) := by
    have := Nat.le_ceil (16 * Real.pi ^ 2 * (216 * (ell : ℝ) ^ 5))
    have h2 : ((⌈16 * Real.pi ^ 2 * (216 * (ell : ℝ) ^ 5)⌉₊ + 1 : ℕ) : ℝ) ≤ (Mc : ℝ) := by exact_mod_cast hMc
    push_cast at h2
    linarith
  have hMc1 : (1 : ℝ) ≤ (Mc : ℝ) := by
    have : 1 ≤ Mc := by omega
    exact_mod_cast this
  have hMc0 : (0 : ℝ) < Mc := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Real.pi_pos]

theorem cU_lower {ell Mc : ℕ} (hell : 0 < ell) {s : ℝ} (hs0 : 0 ≤ s) {s₁ : ℝ}
    (hw : ∀ s : ℝ, 0 ≤ s → s ≤ s₁ → rhoOf ell (kapM1 s) ≤ 1 / 10 ∧
      (384 * 930 ^ 2 * (ell : ℝ) ^ 3 + 384) * kapM1 s ^ 2 ≤ 1 / (216 * (ell : ℝ) ^ 5))
    (hs : s ≤ s₁) (hMc : 0 < Mc) (hMw : 16 * Real.pi ^ 2 / (Mc : ℝ) ^ 2 ≤ 1 / (216 * (ell : ℝ) ^ 5)) :
    (1 / 108) * (1 / (ell : ℝ) ^ 5) ≤ AdalyFormal.M2Unit.cU ell Mc (kapM1 s) 1 1 := by
  obtain ⟨h1, h2⟩ := hw s hs0 hs
  refine AdalyFormal.M2Unit.cU_ge hell hMc (kapM1_nonneg hs0) one_pos h1 ?_
  have hl : (0 : ℝ) < ell := by exact_mod_cast hell
  have e : (1 : ℝ) / 108 * (1 / (ell : ℝ) ^ 5) = 1 / (216 * (ell : ℝ) ^ 5) + 1 / (216 * (ell : ℝ) ^ 5) := by
    field_simp; ring
  rw [e]
  have e2 : (8 + 4 * (1 + 1 / (1 : ℝ))) * Real.pi ^ 2 / (Mc : ℝ) ^ 2 = 16 * Real.pi ^ 2 / (Mc : ℝ) ^ 2 := by norm_num
  have e3 : 384 * 930 ^ 2 * (ell : ℝ) ^ 3 * kapM1 s ^ 2 + (8 + 4 * (1 + 1 / (1 : ℝ))) * Real.pi ^ 2 / (Mc : ℝ) ^ 2
      + 64 * (1 + 1 / (1 : ℝ)) * kapM1 s ^ 2 + (1 + 1) * (1 + 1 / (1 : ℝ)) * 64 * kapM1 s ^ 2
      = (384 * 930 ^ 2 * (ell : ℝ) ^ 3 + 384) * kapM1 s ^ 2 + 16 * Real.pi ^ 2 / (Mc : ℝ) ^ 2 := by
    rw [e2]; ring
  rw [e3]
  linarith

end AdalyFormal.M2Skel

#print axioms AdalyFormal.M2Skel.Etc_window
#print axioms AdalyFormal.M2Skel.cu_window
#print axioms AdalyFormal.M2Skel.Mc_window
#print axioms AdalyFormal.M2Skel.cU_lower
