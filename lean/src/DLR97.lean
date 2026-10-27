import DLR96

/-!
# DL97 -- STAGE B and the general M0 inner claim: **`M0Core ℓ M _ a` for EVERY `ℓ ≥ 2`, `M`, `a > 0`**, hence **MC2's `M0Target`**

* `stageB ℓ a` : there are a slope `θ₁ > 0`, a threshold `β₀ > 0` and a constant `γm > 0` such that for every amplitude scale
  `0 ≤ β < β₀` (`ᾱ = (4π+4)β`, `ρ = (1+3π)ᾱ`): the regime smallness (`hcb`, `216ρ² < 1`, `ρ ≤ 1/(1000ℓ³)`, `ThetaM0 < min a 1/1000`,
  `KUSmall`, `UnitSmall`), `4β ≤ 1`, and an inhabitant of the numerics package `M0ClassNum ℓ a 1 ρ β θ₁` whose conclusion constant
  is `≥ γm` (`γm = (1/54)ℓ⁻⁵/8`).  Proof: STAGE A (DL95) fixes `θ₁`; the limits of DL96 at `β → 0` give the rest.
* **`M0Core_general ℓ M a`** : MC2's M0 inner claim, no D-layer hypothesis, every `ℓ ≥ 2`, every `M`, every `a > 0`.
* **`M0Target_unconditional`** : MC2's `M0Target` (the M0 corollary the m0_corollary lane derived FROM the frozen r7 headline,
  conditional there on the D-layer), proved outright.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000

namespace AdalyFormal.DLayer

open Filter Topology
open AdalyFormal.AsmM0 (KhatM0 ThetaM0 Mc phiC)
open AdalyFormal.BondComposite (rr)
open AdalyFormal.RegBgKU (kapHat Kc KUSmall)
open AdalyFormal.NonflatJet (rhoOf r0)
open EstimatesLayer.E1E3 (e2Majorant)
open AdalyFormal.M0Finish (dCM0 cBM0 EbarM0 gam0Form UnitSmall)
open AdalyFormal.StatementLane (scaleUp TorusOK)
open AdalyFormal.StatementLaneG (InstIneq lamBlockSum_univ)
open AdalyFormal.IngredientFamilyR2 (fullTower)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M0Corollary (GlobalRegular2)

theorem abs_lt_of_tendsto_zero {X : Type*} {L : Filter X} {f : X → ℝ} (h : Tendsto f L (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in L, |f x| < ε := by
  have := h.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)
  filter_upwards [this] with x hx
  simpa [Metric.mem_ball, Real.dist_eq] using hx

/-- **STAGE B** -/
theorem stageB (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ θ₁ > 0, ∃ β₀ > 0, ∃ γm > 0, ∀ β : ℝ, 0 ≤ β → β < β₀ →
      4000000 * (ell : ℝ) ^ 2 * ((4 * Real.pi + 4) * β) ≤ 1 ∧
      216 * ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * β)) ^ 2 < 1 ∧
      (1 + 3 * Real.pi) * ((4 * Real.pi + 4) * β) ≤ 1 / (1000 * (ell : ℝ) ^ 3) ∧
      ThetaM0 ell a 1 ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * β)) < min a 1 / 1000 ∧
      KUSmall ell ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * β)) ∧
      UnitSmall ell ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * β)) ∧
      4 * β ≤ 1 ∧
      ∃ Num : M0ClassNum ell a 1 ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * β)) β θ₁,
        γm ≤ gam0M0f ell a 1 ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * β)) (eps2free Num) (epsJfree Num)
          (dCM0 ell ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * β)))
          (cBM0 ell ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * β))) := by
  have hell1 : 1 ≤ ell := by omega
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpi := Real.pi_pos
  obtain ⟨ε, hε, hA⟩ := stageA ell hell a 1 ha one_pos
  set θ₁ : ℝ := ε / 2 with hθ₁def
  have hθ₁ : 0 < θ₁ := by positivity
  have hθ1 : |θ₁| < ε := by rw [abs_of_pos hθ₁]; linarith
  have hz : |(0 : ℝ)| < ε := by simpa using hε
  -- STAGE A at the limit point (θ₁, 0, 0, 0)
  obtain ⟨-, -, A3, -, -, -, -, A8, -, -, A11⟩ := hA θ₁ 0 0 0 hθ1 hz hz hz
  have hG : cGS ell a 0 θ₁ ≠ 0 := A3.ne'
  have hD : 1 / bNS a 0 (δS ell 0) - GLv.EN ell a 0 θ₁ (νS 0) (δνS 0 θ₁) (1 / KhatM0 ell a 1 0) ≠ 0 :=
    (sub_pos.mpr A8).ne'
  have hD1 : 1 / bN1f ell a 1 0 θ₁ 0 - GLv.EN ell a 0 θ₁ (νS 0 + 0) (δνS 0 θ₁ + 0) (cg1f ell a 1 0 θ₁ 0) ≠ 0 :=
    (sub_pos.mpr A11).ne'
  -- the filter: β → 0, ρ = (1+3π)(4π+4)β
  have hβ : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0) := tendsto_id
  have hρ : Tendsto (fun x : ℝ => (1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x)) (𝓝 0) (𝓝 0) := by
    have := (tendsto_const_nhds (x := (1 + 3 * Real.pi))).mul ((tendsto_const_nhds (x := 4 * Real.pi + 4)).mul hβ)
    simpa using this
  have hK := tKhat hρ ell hell1 a 1 ha
  have hK0 := KhatM0_zero_pos ell a 1 ha one_pos
  have hν := tnuf hρ hβ ell hell a 1 θ₁ ha one_pos hG hD
  have hδ := tdeltaf hρ hβ ell hell a 1 θ₁ ha one_pos hG hD
  have hk := tkapHat hρ ell
  -- the conclusion constant
  set γ : ℝ := (1 / 54) * (1 / (ell : ℝ) ^ 5) with hγdef
  have hγ0 : 0 < γ := by positivity
  have hgam : Tendsto (fun x : ℝ => gam0M0f ell a 1 ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x))
      (nuf ell a 1 ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x)) x θ₁ * KhatM0 ell a 1 ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x)))
      (KDfree ell * CH1f ell a 1 ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x)) θ₁
          (nuf ell a 1 ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x)) x θ₁)
          (deltaf ell a 1 ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x)) x θ₁) * JSfree x)
      (dCM0 ell ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x))) (cBM0 ell ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x))))
      (𝓝 0) (𝓝 (gam0Form γ a (0 * KhatM0 ell a 1 0) (KDfree ell * CH1f ell a 1 0 θ₁ 0 0 * 0) 0 0
        (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)))) := by
    unfold gam0M0f
    exact tgam0Form (hν.mul hK) ((tendsto_const_nhds.mul (tCH1f hρ hν hδ ell hell a 1 θ₁ ha one_pos hG hD1)).mul (tJS hβ))
      (tEbar hρ ell hell1 a 1 ha) (tdCM0 hρ ell) (tcBM0 hρ ell) (by norm_num)
  have hgam0 : gam0Form γ a (0 * KhatM0 ell a 1 0) (KDfree ell * CH1f ell a 1 0 θ₁ 0 0 * 0) 0 0
      (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) = γ / 4 := by
    unfold gam0Form; ring
  rw [hgam0] at hgam
  -- the eventual conditions
  have E1 := abs_lt_of_tendsto_zero hρ hε
  have E2 := abs_lt_of_tendsto_zero hν hε
  have E3 := abs_lt_of_tendsto_zero hδ hε
  have E4 : ∀ᶠ x in 𝓝 (0 : ℝ), 1536 * (ell : ℝ) ^ 2 * e2Majorant (rhoOf ell ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x)))
      < 1 - 1 / (ell : ℝ) := by
    have h := (tendsto_const_nhds (x := 1536 * (ell : ℝ) ^ 2)).mul (te2rho hρ ell)
    rw [mul_zero] at h
    refine h.eventually_lt tendsto_const_nhds ?_
    have : 1 / (ell : ℝ) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  have E5 : ∀ᶠ x in 𝓝 (0 : ℝ), 192 * (8 * (ell : ℝ) * kapHat ell ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x))
      + 8 * e2Majorant (rhoOf ell (kapHat ell ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x))))) < 1 / (2 * (ell : ℝ) ^ 3) := by
    have h := (tendsto_const_nhds (x := (192 : ℝ))).mul (((tendsto_const_nhds (x := 8 * (ell : ℝ))).mul hk).add
      ((tendsto_const_nhds (x := (8 : ℝ))).mul (te2rho hk ell)))
    simp only [mul_zero, add_zero] at h
    exact h.eventually_lt tendsto_const_nhds (by positivity)
  have E6 : ∀ᶠ x in 𝓝 (0 : ℝ), nuf ell a 1 ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x)) x θ₁
      * KhatM0 ell a 1 ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x)) < 1 := by
    have h := hν.mul hK
    rw [zero_mul] at h
    exact h.eventually_lt tendsto_const_nhds (by norm_num)
  have E7 := (tendsto_const_nhds (x := γ / 8)).eventually_lt hgam (by linarith)
  have E8 : ∀ᶠ x in 𝓝 (0 : ℝ), 8 * (ell : ℝ) * kapHat ell ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x))
      < 1 / (8 * Real.pi) := by
    have h := (tendsto_const_nhds (x := 8 * (ell : ℝ))).mul hk; rw [mul_zero] at h
    exact h.eventually_lt tendsto_const_nhds (by positivity)
  have E9 : ∀ᶠ x in 𝓝 (0 : ℝ), AdalyFormal.RegBgKU.Kc ell ^ 2 * ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x) / (3 * Real.pi)
      + ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x)) ^ 2) < 1 := by
    have h := (tendsto_const_nhds (x := AdalyFormal.RegBgKU.Kc ell ^ 2)).mul ((hρ.div_const (3 * Real.pi)).add (hρ.pow 2))
    simp only [zero_div, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h
    exact h.eventually_lt tendsto_const_nhds (by norm_num)
  have E10 : ∀ᶠ x in 𝓝 (0 : ℝ), (8 * (ell : ℝ) - 6) * kapHat ell ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x)) < r0 := by
    have h := (tendsto_const_nhds (x := 8 * (ell : ℝ) - 6)).mul hk; rw [mul_zero] at h
    exact h.eventually_lt tendsto_const_nhds AdalyFormal.NonflatJet.r0_pos
  have E11 : ∀ᶠ x in 𝓝 (0 : ℝ), kapHat ell ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x)) < 1 / (1000 * (ell : ℝ) ^ 4) :=
    hk.eventually_lt tendsto_const_nhds (by positivity)
  have E12 : ∀ᶠ x in 𝓝 (0 : ℝ), Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ)
      * kapHat ell ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x))) < r0 := by
    have h := (tendsto_const_nhds (x := Real.pi / 2)).mul
      ((tendsto_const_nhds (x := (SmallnessBridge.Assemble.loopFactorBound ell : ℝ))).mul hk)
    rw [mul_zero, mul_zero] at h
    exact h.eventually_lt tendsto_const_nhds AdalyFormal.NonflatJet.r0_pos
  have E13 := (tdCM0 hρ ell).eventually_lt (tendsto_const_nhds (x := (1 : ℝ))) (by norm_num)
  have E14 : ∀ᶠ x in 𝓝 (0 : ℝ), 4000000 * (ell : ℝ) ^ 2 * ((4 * Real.pi + 4) * x) < 1 := by
    have h := (tendsto_const_nhds (x := 4000000 * (ell : ℝ) ^ 2)).mul ((tendsto_const_nhds (x := 4 * Real.pi + 4)).mul hβ)
    rw [mul_zero, mul_zero] at h
    exact h.eventually_lt tendsto_const_nhds (by norm_num)
  have E15 : ∀ᶠ x in 𝓝 (0 : ℝ), 216 * ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x)) ^ 2 < 1 := by
    have h := (tendsto_const_nhds (x := (216 : ℝ))).mul (hρ.pow 2)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h
    exact h.eventually_lt tendsto_const_nhds (by norm_num)
  have E16 : ∀ᶠ x in 𝓝 (0 : ℝ), (1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x) < 1 / (1000 * (ell : ℝ) ^ 3) :=
    hρ.eventually_lt tendsto_const_nhds (by positivity)
  have E17 : ∀ᶠ x in 𝓝 (0 : ℝ), ThetaM0 ell a 1 ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * x)) < min a 1 / 1000 := by
    have h := tTheta hρ ell hell1 a 1
    rw [Theta_zero] at h
    exact h.eventually_lt tendsto_const_nhds (by have := lt_min ha one_pos; positivity)
  have E18 : ∀ᶠ x in 𝓝 (0 : ℝ), 4 * x < 1 := by
    have h := (tendsto_const_nhds (x := (4 : ℝ))).mul hβ; rw [mul_zero] at h
    exact h.eventually_lt tendsto_const_nhds (by norm_num)
  have hall := E1.and (E2.and (E3.and (E4.and (E5.and (E6.and (E7.and (E8.and (E9.and (E10.and (E11.and (E12.and
    (E13.and (E14.and (E15.and (E16.and (E17.and E18))))))))))))))))
  obtain ⟨β₀, hβ₀, hP⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨θ₁, hθ₁, β₀, hβ₀, γ / 8, by positivity, fun β hβ0 hβ1 => ?_⟩
  have hdist : dist β 0 < β₀ := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hβ0]; exact hβ1
  obtain ⟨P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16, P17, P18⟩ := hP hdist
  set ρ : ℝ := (1 + 3 * Real.pi) * ((4 * Real.pi + 4) * β) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  -- the G chain
  obtain ⟨A1, A2, A3', A4, A5, A6, A7, A8', -, -, -⟩ := hA θ₁ ρ 0 0 hθ1 P1 hz hz
  have hc : CondM0 ell a ρ θ₁ := ⟨hell, ha, hρ0, A4, A5, hθ₁.le, A1.le, A2.le, A3'⟩
  have hEG : 4 * EGM0 ell a ρ θ₁ hc ≤ 1 / KhatM0 ell a 1 ρ := by rw [EGM0_GL]; exact A7.le
  have hN : ENfree ell a 1 ρ θ₁ hc A6 hEG < 1 / bNS a ρ (δS ell ρ) := by rw [ENfree_GL]; exact A8'
  have hK2c := P4
  have hνψ : 0 ≤ nuPsi ell a 1 ρ β θ₁ hc A6 hEG := by
    unfold nuPsi
    have h1 := CHfree_nonneg ell a 1 ρ θ₁ hθ₁ hc A6 hEG hN
    have h2 := JSfree_nonneg β hβ0
    have h3 := K2free_nonneg ell ρ hell hρ0 hK2c
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) h3
  have hδψ : 0 ≤ deltaPsi ell a 1 ρ β θ₁ hc A6 hEG := by
    unfold deltaPsi
    have h5 : 1 ≤ Real.exp (5 * θ₁) := Real.one_le_exp (by positivity)
    exact mul_nonneg (mul_nonneg hνψ (by norm_num)) (mul_nonneg (by linarith) (by linarith))
  -- the G₁ chain
  have hνε : |nuPsi ell a 1 ρ β θ₁ hc A6 hEG| < ε := by rw [nuPsi_nuf]; exact P2
  have hδε : |deltaPsi ell a 1 ρ β θ₁ hc A6 hEG| < ε := by rw [deltaPsi_deltaf]; exact P3
  obtain ⟨-, -, -, -, -, -, -, -, B9, B10, B11⟩ := hA θ₁ ρ _ _ hθ1 P1 hνε hδε
  have hcg1 : 0 < cg1 ell a 1 ρ θ₁ hc (nuPsi ell a 1 ρ β θ₁ hc A6 hEG) := by rw [cg1_GL]; exact B9
  have hEG1 : 4 * EGM1 ell a ρ θ₁ hc (nuPsi ell a 1 ρ β θ₁ hc A6 hEG) (deltaPsi ell a 1 ρ β θ₁ hc A6 hEG) hνψ hδψ
      ≤ cg1 ell a 1 ρ θ₁ hc (nuPsi ell a 1 ρ β θ₁ hc A6 hEG) := by
    rw [EGM1_GL, cg1_GL]; exact B10.le
  have hN1 : EN1free ell a 1 ρ θ₁ hc (nuPsi ell a 1 ρ β θ₁ hc A6 hEG) (deltaPsi ell a 1 ρ β θ₁ hc A6 hEG) hνψ hδψ A6 hcg1
      hEG1 < 1 / bN1 ell a 1 ρ θ₁ hc (nuPsi ell a 1 ρ β θ₁ hc A6 hEG) := by
    rw [EN1free_GL, cg1_GL, bN1_GL]; exact B11
  have hε' : 2 * CHfree ell a 1 ρ θ₁ hc A6 hEG * JSfree β * K2free ell ρ * KhatM0 ell a 1 ρ < 1 := P6
  let Num : M0ClassNum ell a 1 ρ β θ₁ :=
    ⟨hθ₁, hβ0, hc, A6, hEG, hN, hK2c, P5.le, hνψ, hδψ, hcg1, hEG1, hN1, hε'⟩
  refine ⟨P14.le, P15, P16.le, P17, ⟨P8.le, P9.le, P10⟩, ⟨P11.le, P12, P13⟩, P18.le, Num, ?_⟩
  exact P7.le

/-- **the M0 inner claim, every `ℓ ≥ 2`, every `M`, every `a > 0`, no D-layer hypothesis** -/
theorem M0Core_general (ell M : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    AdalyFormal.M0Corollary.M0Core ell M (by omega) a := by
  obtain ⟨θ₁, hθ₁, β₀, hβ₀, γm, hγm, hB⟩ := stageB ell hell a ha
  refine ⟨β₀ / 2, by positivity, γm, hγm, ?_⟩
  intro k _ Lu hT α₀ hα₀ hsm U hU
  have hM : 0 < M := Nat.pos_of_dvd_of_pos (hT.2.2 0) (Nat.succ_pos _)
  have hcast : ((12 : ℕ) : ℝ) * M * α₀ = (12 : ℝ) * M * α₀ := by norm_num
  have hβ0 : 0 ≤ ((12 : ℕ) : ℝ) * M * α₀ := by rw [hcast]; positivity
  have hβ1 : ((12 : ℕ) : ℝ) * M * α₀ < β₀ := by rw [hcast]; linarith
  obtain ⟨hcb, h216, h1000, hsU, H, HU, h4, Num, hγ⟩ := hB (((12 : ℕ) : ℝ) * M * α₀) hβ0 hβ1
  have key := instIneq_globalRegular2_unconditional ell M k hell Lu hT U a 1 α₀
    ((4 * Real.pi + 4) * (((12 : ℕ) : ℝ) * M * α₀)) (by rw [hcast]) ha one_pos hα₀ (by rw [← hcast]; exact h4) Set.univ
    (lamBlockSum_univ ell (by omega)) hU hcb h216 h1000 hsU H HU θ₁ Num
  exact instIneq_mono hγ key

/-- **MC2's `M0Target`, unconditionally** (r7 objects) -/
theorem M0Target_unconditional : AdalyFormal.M0Corollary.M0Target := by
  intro ell hell a ha
  exact ⟨1, le_rfl, fun m _ => M0Core_general ell (ell ^ m) hell a ha⟩

#print axioms stageB
#print axioms M0Core_general
#print axioms M0Target_unconditional

end AdalyFormal.DLayer
