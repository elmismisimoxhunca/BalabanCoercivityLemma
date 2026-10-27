import DLR94

/-!
# DL95 -- STAGE A: the `θ`-small Combes–Thomas conditions of the `G` and `G₁` chains hold near the degenerate point, every `ℓ ≥ 2`, `a, t > 0`

* `tGLv_*` : continuity of the `GLv` constants along `θ → θ₀`, `ρ → 0` (any `θ₀` with `cGS ℓ a 0 θ₀ ≠ 0`).
* `FF_*_zero`, `GLv_*_zero` : at `δD = δQ = δC = κ = δK = ν = δν = δB = 0` the error constants vanish (`EG = dW = δCW = dT = 0`,
  `EN = 0`).
* **`stageA ℓ a t`** : `∃ ε > 0` such that for all `|θ|, |ρ|, |νψ|, |δψ| < ε` the eleven conditions hold: the three `CondM0` smallness
  conditions (`hS1`, `hS2`, `cGS > 0`), `216ρ² < 1`, `162ρ < 1`, `K̂ > 0`, `4·EG < 1/K̂`, `EN < 1/bNS` (the `G` chain), `cg1 > 0`,
  `4·EG₁ < cg1`, `EN₁ < 1/bN1` (the `G₁` chain with perturbation `(νψ, δψ)`), all in their `GLv` form (= the model constants by `rfl`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open Filter Topology
open AdalyFormal.AsmM0 (KhatM0 ThetaM0 Mc phiC)

section lim
variable {X : Type*} {L : Filter X} {θ ρ : X → ℝ} {θ₀ : ℝ}

theorem tGLv_nW (hθ : Tendsto θ L (𝓝 θ₀)) (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a)
    (hG0 : cGS ell a 0 θ₀ ≠ 0) :
    Tendsto (fun x => GLv.nW ell a (ρ x) (θ x)) L (𝓝 (GLv.nW ell a 0 θ₀)) := by
  unfold GLv.nW
  exact FFlim.tnW (tcS hρ a) (cS_zero_pos a) (tδDS hθ) (tδQS hθ a) tendsto_const_nhds tendsto_const_nhds
    (tcGS hθ hρ ell hell a ha) hG0

theorem tGLv_dW (hθ : Tendsto θ L (𝓝 θ₀)) (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a)
    (hG0 : cGS ell a 0 θ₀ ≠ 0) :
    Tendsto (fun x => GLv.dW ell a (ρ x) (θ x)) L (𝓝 (GLv.dW ell a 0 θ₀)) := by
  unfold GLv.dW
  exact FFlim.tdW (tcS hρ a) (cS_zero_pos a) (tδDS hθ) (tδQS hθ a) tendsto_const_nhds tendsto_const_nhds
    (tcGS hθ hρ ell hell a ha) hG0

theorem tGLv_dT (hθ : Tendsto θ L (𝓝 θ₀)) (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a)
    (hG0 : cGS ell a 0 θ₀ ≠ 0) :
    Tendsto (fun x => GLv.dT ell a (ρ x) (θ x)) L (𝓝 (GLv.dT ell a 0 θ₀)) := by
  unfold GLv.dT
  exact FFlim.tdT (tcS hρ a) (cS_zero_pos a) (tδDS hθ) (tδQS hθ a) tendsto_const_nhds tendsto_const_nhds
    (tcGS hθ hρ ell hell a ha) hG0

theorem tGLv_δCW (hθ : Tendsto θ L (𝓝 θ₀)) (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a)
    (hG0 : cGS ell a 0 θ₀ ≠ 0) :
    Tendsto (fun x => GLv.δCW ell a (ρ x) (θ x)) L (𝓝 (GLv.δCW ell a 0 θ₀)) := by
  unfold GLv.δCW
  exact FFlim.tδCW (tcS hρ a) (cS_zero_pos a) (tδDS hθ) (tδQS hθ a) tendsto_const_nhds tendsto_const_nhds
    (tcGS hθ hρ ell hell a ha) hG0 (tδCS hθ) (tκS hρ) (tδKS hθ hρ)

theorem tGLv_EG (hθ : Tendsto θ L (𝓝 θ₀)) (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a)
    (hG0 : cGS ell a 0 θ₀ ≠ 0) {ν δν : X → ℝ} {ν₀ δν₀ : ℝ} (hν : Tendsto ν L (𝓝 ν₀)) (hδν : Tendsto δν L (𝓝 δν₀)) :
    Tendsto (fun x => GLv.EG ell a (ρ x) (θ x) (ν x) (δν x)) L (𝓝 (GLv.EG ell a 0 θ₀ ν₀ δν₀)) := by
  unfold GLv.EG
  exact FFlim.tEG (tcS hρ a) (cS_zero_pos a) (tδDS hθ) (tδQS hθ a) tendsto_const_nhds tendsto_const_nhds
    (tcGS hθ hρ ell hell a ha) hG0 (tδCS hθ) (tκS hρ) (tδKS hθ hρ) hν hδν (tδBS hθ hρ ell a) tendsto_const_nhds

theorem tGLv_EN (hθ : Tendsto θ L (𝓝 θ₀)) (hρ : Tendsto ρ L (𝓝 0)) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a)
    (hG0 : cGS ell a 0 θ₀ ≠ 0) {ν δν cg : X → ℝ} {ν₀ δν₀ cg₀ : ℝ} (hν : Tendsto ν L (𝓝 ν₀))
    (hδν : Tendsto δν L (𝓝 δν₀)) (hcg : Tendsto cg L (𝓝 cg₀)) (hcg₀ : cg₀ ≠ 0) :
    Tendsto (fun x => GLv.EN ell a (ρ x) (θ x) (ν x) (δν x) (cg x)) L (𝓝 (GLv.EN ell a 0 θ₀ ν₀ δν₀ cg₀)) := by
  unfold GLv.EN
  exact FFlimN.tEN (tGLv_EG hθ hρ ell hell a ha hG0 hν hδν) (tGLv_nW hθ hρ ell hell a ha hG0)
    (tGLv_dW hθ hρ ell hell a ha hG0) (tGLv_δCW hθ hρ ell hell a ha hG0) (tGLv_dT hθ hρ ell hell a ha hG0) hν hδν
    (tδBS hθ hρ ell a) tendsto_const_nhds hcg hcg₀ (tqBS hρ ell a)

end lim

/-! ## the error constants vanish at the degenerate point -/

theorem FF_dT_zero (c q cG : ℝ) : FF.dT c 0 0 1 q cG = 0 := by
  simp [FF.dT, FF.epsX, FF.K0, FF.dGi, FF.dGam, FF.dF, FF.epsDX, FF.K1]

theorem FF_dW_zero (c q cG : ℝ) : FF.dW c 0 0 1 q cG = 0 := by
  simp [FF.dW, FF.dDZ, FF.epsX, FF.K0, FF.K1, FF.dGi, FF.dGam, FF.dF, FF.epsDX]

theorem FF_δCW_zero (c q cG : ℝ) : FF.δCW c 0 0 1 q cG 0 0 0 = 0 := by
  simp [FF.δCW]

theorem FF_EG_zero (c q cG M : ℝ) : FF.EG c 0 0 1 q cG 0 0 0 0 0 0 M = 0 := by
  simp only [FF.EG, FF.EA2, FF_dW_zero, FF_δCW_zero, FF_dT_zero]
  ring

theorem FF_EN_zero (nW M cg qb : ℝ) : FF.EN 0 nW 0 0 0 0 0 0 M cg qb = 0 := by
  simp only [FF.EN, FF.KD]
  ring

theorem GLv_EG_zero (ell : ℕ) (a : ℝ) : GLv.EG ell a 0 0 0 0 = 0 := by
  unfold GLv.EG
  rw [δDS_zero, δQS_zero, δCS_zero, κS_zero, δKS_zero, δBS_zero]
  exact FF_EG_zero _ _ _ _

theorem GLv_EN_zero (ell : ℕ) (a cg : ℝ) : GLv.EN ell a 0 0 0 0 cg = 0 := by
  unfold GLv.EN
  rw [GLv_EG_zero]
  have h1 : GLv.dW ell a 0 0 = 0 := by unfold GLv.dW; rw [δDS_zero, δQS_zero]; exact FF_dW_zero _ _ _
  have h2 : GLv.δCW ell a 0 0 = 0 := by
    unfold GLv.δCW; rw [δDS_zero, δQS_zero, δCS_zero, κS_zero, δKS_zero]; exact FF_δCW_zero _ _ _
  have h3 : GLv.dT ell a 0 0 = 0 := by unfold GLv.dT; rw [δDS_zero, δQS_zero]; exact FF_dT_zero _ _ _
  rw [h1, h2, h3, δBS_zero]
  exact FF_EN_zero _ _ _ _

theorem dist4_lt (θ ρ ν δ ε : ℝ) (h1 : |θ| < ε) (h2 : |ρ| < ε) (h3 : |ν| < ε) (h4 : |δ| < ε) :
    dist ((θ, ρ, ν, δ) : ℝ × ℝ × ℝ × ℝ) 0 < ε := by
  simp only [Prod.dist_eq, Real.dist_eq, Prod.fst_zero, Prod.snd_zero, sub_zero]
  exact max_lt h1 (max_lt h2 (max_lt h3 h4))

/-- **STAGE A** -/
theorem stageA (ell : ℕ) (hell : 2 ≤ ell) (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    ∃ ε > 0, ∀ θ ρ νψ δψ : ℝ, |θ| < ε → |ρ| < ε → |νψ| < ε → |δψ| < ε →
      24 * (δDS θ ^ 2 + 1 * δQS a θ ^ 2) < cS a ρ ∧ 4 * δDS θ ^ 2 < cS a ρ ∧ 0 < cGS ell a ρ θ ∧
      216 * ρ ^ 2 < 1 ∧ 162 * ρ < 1 ∧ 0 < KhatM0 ell a t ρ ∧
      4 * GLv.EG ell a ρ θ (νS ρ) (δνS ρ θ) < 1 / KhatM0 ell a t ρ ∧
      GLv.EN ell a ρ θ (νS ρ) (δνS ρ θ) (1 / KhatM0 ell a t ρ) < 1 / bNS a ρ (δS ell ρ) ∧
      0 < 1 / KhatM0 ell a t ρ - νψ * GLv.nW ell a ρ θ ^ 2 ∧
      4 * GLv.EG ell a ρ θ (νS ρ + νψ) (δνS ρ θ + δψ) < 1 / KhatM0 ell a t ρ - νψ * GLv.nW ell a ρ θ ^ 2 ∧
      GLv.EN ell a ρ θ (νS ρ + νψ) (δνS ρ θ + δψ) (1 / KhatM0 ell a t ρ - νψ * GLv.nW ell a ρ θ ^ 2)
        < 1 / (bNS a ρ (δS ell ρ) * (1 + νψ * GLv.nW ell a ρ θ ^ 2 * KhatM0 ell a t ρ)) := by
  have hell1 : 1 ≤ ell := by omega
  -- the filter and the coordinates
  let X := ℝ × ℝ × ℝ × ℝ
  have hθ : Tendsto (fun x : X => x.1) (𝓝 0) (𝓝 0) := continuous_fst.tendsto' _ _ rfl
  have hρ : Tendsto (fun x : X => x.2.1) (𝓝 0) (𝓝 0) := (continuous_fst.comp continuous_snd).tendsto' _ _ rfl
  have hν : Tendsto (fun x : X => x.2.2.1) (𝓝 0) (𝓝 0) :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto' _ _ rfl
  have hδ : Tendsto (fun x : X => x.2.2.2) (𝓝 0) (𝓝 0) :=
    (continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto' _ _ rfl
  have hG0 : cGS ell a 0 0 ≠ 0 := (cGS_zero_pos ell hell a ha).ne'
  have hK := tKhat hρ ell hell1 a t ha
  have hK0 := KhatM0_zero_pos ell a t ha ht
  have hiK : Tendsto (fun x : X => 1 / KhatM0 ell a t x.2.1) (𝓝 0) (𝓝 (1 / KhatM0 ell a t 0)) := tcdiv 1 hK hK0.ne'
  have hiK0 : 0 < 1 / KhatM0 ell a t 0 := by positivity
  have hb := tbNS hρ ell a ha
  have hb0 := bNS_zero_pos ell a
  have hnW := tGLv_nW hθ hρ ell hell a ha hG0
  have hcg1 : Tendsto (fun x : X => 1 / KhatM0 ell a t x.2.1 - x.2.2.1 * GLv.nW ell a x.2.1 x.1 ^ 2) (𝓝 0)
      (𝓝 (1 / KhatM0 ell a t 0 - 0 * GLv.nW ell a 0 0 ^ 2)) := hiK.sub (hν.mul (hnW.pow 2))
  have hcg10 : 1 / KhatM0 ell a t 0 - 0 * GLv.nW ell a 0 0 ^ 2 = 1 / KhatM0 ell a t 0 := by ring
  rw [hcg10] at hcg1
  have hbN1 : Tendsto (fun x : X => bNS a x.2.1 (δS ell x.2.1) * (1 + x.2.2.1 * GLv.nW ell a x.2.1 x.1 ^ 2
      * KhatM0 ell a t x.2.1)) (𝓝 0) (𝓝 (bNS a 0 (δS ell 0) * (1 + 0 * GLv.nW ell a 0 0 ^ 2 * KhatM0 ell a t 0))) :=
    hb.mul (tendsto_const_nhds.add ((hν.mul (hnW.pow 2)).mul hK))
  have hbN10 : bNS a 0 (δS ell 0) * (1 + 0 * GLv.nW ell a 0 0 ^ 2 * KhatM0 ell a t 0) = bNS a 0 (δS ell 0) := by ring
  rw [hbN10] at hbN1
  -- the eleven limits
  have l1 : Tendsto (fun x : X => 24 * (δDS x.1 ^ 2 + 1 * δQS a x.1 ^ 2)) (𝓝 0) (𝓝 (24 * (δDS 0 ^ 2 + 1 * δQS a 0 ^ 2))) :=
    tendsto_const_nhds.mul (((tδDS hθ).pow 2).add (tendsto_const_nhds.mul ((tδQS hθ a).pow 2)))
  have l2 : Tendsto (fun x : X => 4 * δDS x.1 ^ 2) (𝓝 0) (𝓝 (4 * δDS 0 ^ 2)) := tendsto_const_nhds.mul ((tδDS hθ).pow 2)
  have lc := tcS hρ a
  have lG := tcGS hθ hρ ell hell a ha
  have l216 : Tendsto (fun x : X => 216 * x.2.1 ^ 2) (𝓝 0) (𝓝 (216 * 0 ^ 2)) := tendsto_const_nhds.mul (hρ.pow 2)
  have l162 : Tendsto (fun x : X => 162 * x.2.1) (𝓝 0) (𝓝 (162 * 0)) := tendsto_const_nhds.mul hρ
  have lEG : Tendsto (fun x : X => 4 * GLv.EG ell a x.2.1 x.1 (νS x.2.1) (δνS x.2.1 x.1)) (𝓝 0)
      (𝓝 (4 * GLv.EG ell a 0 0 (νS 0) (δνS 0 0))) :=
    tendsto_const_nhds.mul (tGLv_EG hθ hρ ell hell a ha hG0 (tνS hρ) (tδνS hθ hρ))
  have lEN : Tendsto (fun x : X => GLv.EN ell a x.2.1 x.1 (νS x.2.1) (δνS x.2.1 x.1) (1 / KhatM0 ell a t x.2.1)) (𝓝 0)
      (𝓝 (GLv.EN ell a 0 0 (νS 0) (δνS 0 0) (1 / KhatM0 ell a t 0))) :=
    tGLv_EN hθ hρ ell hell a ha hG0 (tνS hρ) (tδνS hθ hρ) hiK hiK0.ne'
  have lb : Tendsto (fun x : X => 1 / bNS a x.2.1 (δS ell x.2.1)) (𝓝 0) (𝓝 (1 / bNS a 0 (δS ell 0))) := tcdiv 1 hb hb0.ne'
  have lEG1 : Tendsto (fun x : X => 4 * GLv.EG ell a x.2.1 x.1 (νS x.2.1 + x.2.2.1) (δνS x.2.1 x.1 + x.2.2.2)) (𝓝 0)
      (𝓝 (4 * GLv.EG ell a 0 0 (νS 0 + 0) (δνS 0 0 + 0))) :=
    tendsto_const_nhds.mul (tGLv_EG hθ hρ ell hell a ha hG0 ((tνS hρ).add hν) ((tδνS hθ hρ).add hδ))
  have lEN1 : Tendsto (fun x : X => GLv.EN ell a x.2.1 x.1 (νS x.2.1 + x.2.2.1) (δνS x.2.1 x.1 + x.2.2.2)
      (1 / KhatM0 ell a t x.2.1 - x.2.2.1 * GLv.nW ell a x.2.1 x.1 ^ 2)) (𝓝 0)
      (𝓝 (GLv.EN ell a 0 0 (νS 0 + 0) (δνS 0 0 + 0) (1 / KhatM0 ell a t 0))) :=
    tGLv_EN hθ hρ ell hell a ha hG0 ((tνS hρ).add hν) ((tδνS hθ hρ).add hδ) hcg1 hiK0.ne'
  have lb1 : Tendsto (fun x : X => 1 / (bNS a x.2.1 (δS ell x.2.1) * (1 + x.2.2.1 * GLv.nW ell a x.2.1 x.1 ^ 2
      * KhatM0 ell a t x.2.1))) (𝓝 0) (𝓝 (1 / bNS a 0 (δS ell 0))) := tcdiv 1 hbN1 hb0.ne'
  -- the values at the degenerate point
  rw [δDS_zero, δQS_zero] at l1
  rw [δDS_zero] at l2
  rw [νS_zero, δνS_zero, GLv_EG_zero] at lEG
  rw [νS_zero, δνS_zero, GLv_EN_zero] at lEN
  rw [νS_zero, δνS_zero, add_zero, GLv_EG_zero] at lEG1
  rw [νS_zero, δνS_zero, add_zero, GLv_EN_zero] at lEN1
  have hc0 := cS_zero_pos a
  have hcG0 := cGS_zero_pos ell hell a ha
  have e1 := l1.eventually_lt lc (by norm_num; exact hc0)
  have e2 := l2.eventually_lt lc (by norm_num; exact hc0)
  have e3 := (tendsto_const_nhds (x := (0 : ℝ))).eventually_lt lG hcG0
  have e4 := l216.eventually_lt (tendsto_const_nhds (x := (1 : ℝ))) (by norm_num)
  have e5 := l162.eventually_lt (tendsto_const_nhds (x := (1 : ℝ))) (by norm_num)
  have e6 := (tendsto_const_nhds (x := (0 : ℝ))).eventually_lt hK hK0
  have e7 := lEG.eventually_lt hiK (by norm_num; exact hK0)
  have e8 := lEN.eventually_lt lb (by positivity)
  have e9 := (tendsto_const_nhds (x := (0 : ℝ))).eventually_lt hcg1 hiK0
  have e10 := lEG1.eventually_lt hcg1 (by norm_num; exact hK0)
  have e11 := lEN1.eventually_lt lb1 (by positivity)
  have hall := e1.and (e2.and (e3.and (e4.and (e5.and (e6.and (e7.and (e8.and (e9.and (e10.and e11)))))))))
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.mp hall
  exact ⟨ε, hε, fun θ' ρ' ν' δ' h1 h2 h3 h4 => hP (dist4_lt θ' ρ' ν' δ' ε h1 h2 h3 h4)⟩

#print axioms FF_EG_zero
#print axioms FF_EN_zero
#print axioms stageA

end AdalyFormal.DLayer
