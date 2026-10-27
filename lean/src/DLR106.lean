import DLR104

/-!
# DL106 -- the numerics package in a TWO-parameter window, every `ℓ ≥ 2`, `a > 0`, `t > 0` (STAGE B2)

(There is no r7 module DL105: the name DLR105 is the r8-only environment-identity module; the r8 copy of this file is DLR106.)

`instIneq_M0_class_unconditional` (DL84) takes the k-free numerics package `M0ClassNum ℓ a t ρ β θ` as a hypothesis; it was
inhabited for ALL small `(ρ, β)` only at `ℓ = 2, a = t = 1` (DL88), and for general `(ℓ, a)` only along the class scaling
`ρ = (1+3π)(4π+4)β` with `t = 1` (DL97 `stageB`).  The consumers MF7/MF11 (DL103) also need `eps2op·K̂ < 1`.
* `eps2op_CHf` : `eps2op` with the proof-free `CHf` (`rfl`).
* **`stageB2 ℓ a t`** : there are `θ₁ > 0`, `ε₀ > 0`, `γm > 0` such that for EVERY `0 ≤ ρ < ε₀` and EVERY `0 ≤ β < ε₀`
  (independent): `KUSmall ℓ ρ`, `UnitSmall ℓ ρ`, and an inhabitant `Num : M0ClassNum ℓ a t ρ β θ₁` with
  `γm ≤ gam0M0f … (eps2free Num) …` (DL84's constant), `eps2op Num · K̂ < 1`, and `γm ≤ gam0M0 … (eps2op Num) …` (MF7's
  constant).  Proof: STAGE A (DL95) fixes `θ₁`; the continuity lemmas of DL93–DL96 along `𝓝 (0 : ℝ × ℝ)` give the rest
  (`eps2op·K̂ = 2 nW² CHf JSfree(β) K2free K̂ → 0` as `β → 0`).  The package-free theorems built on it are in DL107.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000

namespace AdalyFormal.DLayer

open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.AsmM0 (KhatM0 ThetaM0 M0RegimeR rhoM0)
open AdalyFormal.RegBgKU (kapHat KUSmall)
open AdalyFormal.BondComposite (rr)
open AdalyFormal.NonflatJet (rhoOf r0)
open EstimatesLayer.E1E3 (e2Majorant)
open AdalyFormal.M0Finish (dCM0 cBM0 EbarM0 gam0Form gam0M0 UnitSmall PU)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane2 (PerCubeRegular2 Ufield OnLambdaT)
open AdalyFormal.StatementLaneG (InstIneq LamBlockSum gparams)
open AdalyFormal.IngredientFamilyR2 (fullTower Cfg)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.CurvBlock (dv)
open AdalyFormal.M0Corollary (GlobalRegular2)

/-- `eps2op` written with the proof-free `CHf` (a definitional rearrangement, no content) -/
theorem eps2op_CHf {ell : ℕ} {a t ρ β θ : ℝ} (Num : M0ClassNum ell a t ρ β θ) :
    eps2op Num = 2 * GLv.nW ell a ρ θ ^ 2 * CHf ell a t ρ θ * JSfree β * K2free ell ρ := rfl

/-- **STAGE B2**: the package, both conclusion constants and `eps2op·K̂ < 1` on a two-parameter window, any `t > 0` -/
theorem stageB2 (ell : ℕ) (hell : 2 ≤ ell) (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    ∃ θ₁ > 0, ∃ ε₀ > 0, ∃ γm > 0, ∀ ρ β : ℝ, 0 ≤ ρ → ρ < ε₀ → 0 ≤ β → β < ε₀ →
      KUSmall ell ρ ∧ UnitSmall ell ρ ∧
      ∃ Num : M0ClassNum ell a t ρ β θ₁,
        γm ≤ gam0M0f ell a t ρ (eps2free Num) (epsJfree Num) (dCM0 ell ρ) (cBM0 ell ρ) ∧
        eps2op Num * KhatM0 ell a t ρ < 1 ∧
        γm ≤ gam0M0 ell a t ρ (eps2op Num) (epsJfree Num) (dCM0 ell ρ) (cBM0 ell ρ) := by
  have hell1 : 1 ≤ ell := by omega
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpi := Real.pi_pos
  obtain ⟨ε, hε, hA⟩ := stageA ell hell a t ha ht
  set θ₁ : ℝ := ε / 2 with hθ₁def
  have hθ₁ : 0 < θ₁ := by positivity
  have hθ1 : |θ₁| < ε := by rw [abs_of_pos hθ₁]; linarith
  have hz : |(0 : ℝ)| < ε := by simpa using hε
  obtain ⟨-, -, A3, -, -, -, -, A8, -, -, A11⟩ := hA θ₁ 0 0 0 hθ1 hz hz hz
  have hG : cGS ell a 0 θ₁ ≠ 0 := A3.ne'
  have hD : 1 / bNS a 0 (δS ell 0) - GLv.EN ell a 0 θ₁ (νS 0) (δνS 0 θ₁) (1 / KhatM0 ell a t 0) ≠ 0 :=
    (sub_pos.mpr A8).ne'
  have hD1 : 1 / bN1f ell a t 0 θ₁ 0 - GLv.EN ell a 0 θ₁ (νS 0 + 0) (δνS 0 θ₁ + 0) (cg1f ell a t 0 θ₁ 0) ≠ 0 :=
    (sub_pos.mpr A11).ne'
  -- the filter: (ρ, β) → (0, 0) independently
  have hρ : Tendsto (fun x : ℝ × ℝ => x.1) (𝓝 0) (𝓝 0) := continuous_fst.tendsto' _ _ rfl
  have hβ : Tendsto (fun x : ℝ × ℝ => x.2) (𝓝 0) (𝓝 0) := continuous_snd.tendsto' _ _ rfl
  have hK := tKhat hρ ell hell1 a t ha
  have hK0 := KhatM0_zero_pos ell a t ha ht
  have hν := tnuf hρ hβ ell hell a t θ₁ ha ht hG hD
  have hδ := tdeltaf hρ hβ ell hell a t θ₁ ha ht hG hD
  have hk := tkapHat hρ ell
  have hW := tGLv_nW (tendsto_const_nhds (x := θ₁)) hρ ell hell a ha hG
  have hCH := tCHf hρ ell hell a t θ₁ ha ht hG hD
  have hK2 := tK2free hρ ell hell
  set γ : ℝ := (1 / 54) * (1 / (ell : ℝ) ^ 5) with hγdef
  have hγ0 : 0 < γ := by positivity
  have hεJ := (tendsto_const_nhds (x := KDfree ell)).mul (tCH1f hρ hν hδ ell hell a t θ₁ ha ht hG hD1) |>.mul (tJS hβ)
  -- DL84's constant (form route)
  have hgam : Tendsto (fun x : ℝ × ℝ => gam0M0f ell a t x.1 (nuf ell a t x.1 x.2 θ₁ * KhatM0 ell a t x.1)
      (KDfree ell * CH1f ell a t x.1 θ₁ (nuf ell a t x.1 x.2 θ₁) (deltaf ell a t x.1 x.2 θ₁) * JSfree x.2)
      (dCM0 ell x.1) (cBM0 ell x.1))
      (𝓝 0) (𝓝 (gam0Form γ a (0 * KhatM0 ell a t 0) (KDfree ell * CH1f ell a t 0 θ₁ 0 0 * 0) 0 0
        (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)))) := by
    unfold gam0M0f
    exact tgam0Form (hν.mul hK) hεJ (tEbar hρ ell hell1 a t ha) (tdCM0 hρ ell) (tcBM0 hρ ell) (by norm_num)
  have hgam0 : gam0Form γ a (0 * KhatM0 ell a t 0) (KDfree ell * CH1f ell a t 0 θ₁ 0 0 * 0) 0 0
      (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) = γ / 4 := by
    unfold gam0Form; ring
  rw [hgam0] at hgam
  -- the operator-norm smallness and MF7's constant (operator route)
  have hop : Tendsto (fun x : ℝ × ℝ => 2 * GLv.nW ell a x.1 θ₁ ^ 2 * CHf ell a t x.1 θ₁ * JSfree x.2 * K2free ell x.1
      * KhatM0 ell a t x.1) (𝓝 0)
      (𝓝 (2 * GLv.nW ell a 0 θ₁ ^ 2 * CHf ell a t 0 θ₁ * 0
        * (K2s ell * Real.exp (2 * (3600 * (ell : ℝ) * 0) / rr ell) * ell / (1 - 1 / (ell : ℝ))) * KhatM0 ell a t 0)) :=
    ((((tendsto_const_nhds.mul (hW.pow 2)).mul hCH).mul (tJS hβ)).mul hK2).mul hK
  have hop0 : 2 * GLv.nW ell a 0 θ₁ ^ 2 * CHf ell a t 0 θ₁ * 0
      * (K2s ell * Real.exp (2 * (3600 * (ell : ℝ) * 0) / rr ell) * ell / (1 - 1 / (ell : ℝ))) * KhatM0 ell a t 0 = 0 := by
    ring
  have hgamop : Tendsto (fun x : ℝ × ℝ => gam0M0f ell a t x.1
      (2 * GLv.nW ell a x.1 θ₁ ^ 2 * CHf ell a t x.1 θ₁ * JSfree x.2 * K2free ell x.1 * KhatM0 ell a t x.1)
      (KDfree ell * CH1f ell a t x.1 θ₁ (nuf ell a t x.1 x.2 θ₁) (deltaf ell a t x.1 x.2 θ₁) * JSfree x.2)
      (dCM0 ell x.1) (cBM0 ell x.1))
      (𝓝 0) (𝓝 (gam0Form γ a 0 (KDfree ell * CH1f ell a t 0 θ₁ 0 0 * 0) 0 0
        (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)))) := by
    unfold gam0M0f
    rw [hop0] at hop
    exact tgam0Form hop hεJ (tEbar hρ ell hell1 a t ha) (tdCM0 hρ ell) (tcBM0 hρ ell) (by norm_num)
  have hgamop0 : gam0Form γ a 0 (KDfree ell * CH1f ell a t 0 θ₁ 0 0 * 0) 0 0
      (1 + (ell : ℝ) ^ 3 * Real.sqrt (1 / (ell : ℝ) ^ 3)) = γ / 4 := by
    unfold gam0Form; ring
  rw [hgamop0] at hgamop
  rw [hop0] at hop
  -- the eventual conditions
  have E1 := abs_lt_of_tendsto_zero hρ hε
  have E2 := abs_lt_of_tendsto_zero hν hε
  have E3 := abs_lt_of_tendsto_zero hδ hε
  have E4 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ), 1536 * (ell : ℝ) ^ 2 * e2Majorant (rhoOf ell x.1) < 1 - 1 / (ell : ℝ) := by
    have h := (tendsto_const_nhds (x := 1536 * (ell : ℝ) ^ 2)).mul (te2rho hρ ell)
    rw [mul_zero] at h
    refine h.eventually_lt tendsto_const_nhds ?_
    have : 1 / (ell : ℝ) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  have E5 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ), 192 * (8 * (ell : ℝ) * kapHat ell x.1
      + 8 * e2Majorant (rhoOf ell (kapHat ell x.1))) < 1 / (2 * (ell : ℝ) ^ 3) := by
    have h := (tendsto_const_nhds (x := (192 : ℝ))).mul (((tendsto_const_nhds (x := 8 * (ell : ℝ))).mul hk).add
      ((tendsto_const_nhds (x := (8 : ℝ))).mul (te2rho hk ell)))
    simp only [mul_zero, add_zero] at h
    exact h.eventually_lt tendsto_const_nhds (by positivity)
  have E6 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ), nuf ell a t x.1 x.2 θ₁ * KhatM0 ell a t x.1 < 1 := by
    have h := hν.mul hK
    rw [zero_mul] at h
    exact h.eventually_lt tendsto_const_nhds (by norm_num)
  have E7 := (tendsto_const_nhds (x := γ / 8)).eventually_lt hgam (by linarith)
  have E7op := (tendsto_const_nhds (x := γ / 8)).eventually_lt hgamop (by linarith)
  have Eop := hop.eventually_lt (tendsto_const_nhds (x := (1 : ℝ))) (by norm_num)
  have E8 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ), 8 * (ell : ℝ) * kapHat ell x.1 < 1 / (8 * Real.pi) := by
    have h := (tendsto_const_nhds (x := 8 * (ell : ℝ))).mul hk; rw [mul_zero] at h
    exact h.eventually_lt tendsto_const_nhds (by positivity)
  have E9 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ), AdalyFormal.RegBgKU.Kc ell ^ 2 * (x.1 / (3 * Real.pi) + x.1 ^ 2) < 1 := by
    have h := (tendsto_const_nhds (x := AdalyFormal.RegBgKU.Kc ell ^ 2)).mul ((hρ.div_const (3 * Real.pi)).add (hρ.pow 2))
    simp only [zero_div, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h
    exact h.eventually_lt tendsto_const_nhds (by norm_num)
  have E10 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ), (8 * (ell : ℝ) - 6) * kapHat ell x.1 < r0 := by
    have h := (tendsto_const_nhds (x := 8 * (ell : ℝ) - 6)).mul hk; rw [mul_zero] at h
    exact h.eventually_lt tendsto_const_nhds AdalyFormal.NonflatJet.r0_pos
  have E11 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ), kapHat ell x.1 < 1 / (1000 * (ell : ℝ) ^ 4) :=
    hk.eventually_lt tendsto_const_nhds (by positivity)
  have E12 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ), Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ)
      * kapHat ell x.1) < r0 := by
    have h := (tendsto_const_nhds (x := Real.pi / 2)).mul
      ((tendsto_const_nhds (x := (SmallnessBridge.Assemble.loopFactorBound ell : ℝ))).mul hk)
    rw [mul_zero, mul_zero] at h
    exact h.eventually_lt tendsto_const_nhds AdalyFormal.NonflatJet.r0_pos
  have E13 := (tdCM0 hρ ell).eventually_lt (tendsto_const_nhds (x := (1 : ℝ))) (by norm_num)
  have hall := E1.and (E2.and (E3.and (E4.and (E5.and (E6.and (E7.and (E7op.and (Eop.and (E8.and (E9.and (E10.and
    (E11.and (E12.and E13)))))))))))))
  obtain ⟨ε₀, hε₀, hP⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨θ₁, hθ₁, ε₀, hε₀, γ / 8, by positivity, fun ρ β hρ0 hρ1 hβ0 hβ1 => ?_⟩
  have hdist : dist ((ρ, β) : ℝ × ℝ) 0 < ε₀ := by
    simp only [Prod.dist_eq, Real.dist_eq, Prod.fst_zero, Prod.snd_zero, sub_zero]
    exact max_lt (by rw [abs_of_nonneg hρ0]; exact hρ1) (by rw [abs_of_nonneg hβ0]; exact hβ1)
  obtain ⟨P1, P2, P3, P4, P5, P6, P7, P7op, Pop, P8, P9, P10, P11, P12, P13⟩ := hP hdist
  -- the G chain
  obtain ⟨A1, A2, A3', A4, A5, A6, A7, A8', -, -, -⟩ := hA θ₁ ρ 0 0 hθ1 P1 hz hz
  have hc : CondM0 ell a ρ θ₁ := ⟨hell, ha, hρ0, A4, A5, hθ₁.le, A1.le, A2.le, A3'⟩
  have hEG : 4 * EGM0 ell a ρ θ₁ hc ≤ 1 / KhatM0 ell a t ρ := by rw [EGM0_GL]; exact A7.le
  have hN : ENfree ell a t ρ θ₁ hc A6 hEG < 1 / bNS a ρ (δS ell ρ) := by rw [ENfree_GL]; exact A8'
  have hK2c := P4
  have hνψ : 0 ≤ nuPsi ell a t ρ β θ₁ hc A6 hEG := by
    unfold nuPsi
    have h1 := CHfree_nonneg ell a t ρ θ₁ hθ₁ hc A6 hEG hN
    have h2 := JSfree_nonneg β hβ0
    have h3 := K2free_nonneg ell ρ hell hρ0 hK2c
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) h3
  have hδψ : 0 ≤ deltaPsi ell a t ρ β θ₁ hc A6 hEG := by
    unfold deltaPsi
    have h5 : 1 ≤ Real.exp (5 * θ₁) := Real.one_le_exp (by positivity)
    exact mul_nonneg (mul_nonneg hνψ (by norm_num)) (mul_nonneg (by linarith) (by linarith))
  -- the G₁ chain
  have hνε : |nuPsi ell a t ρ β θ₁ hc A6 hEG| < ε := by rw [nuPsi_nuf]; exact P2
  have hδε : |deltaPsi ell a t ρ β θ₁ hc A6 hEG| < ε := by rw [deltaPsi_deltaf]; exact P3
  obtain ⟨-, -, -, -, -, -, -, -, B9, B10, B11⟩ := hA θ₁ ρ _ _ hθ1 P1 hνε hδε
  have hcg1 : 0 < cg1 ell a t ρ θ₁ hc (nuPsi ell a t ρ β θ₁ hc A6 hEG) := by rw [cg1_GL]; exact B9
  have hEG1 : 4 * EGM1 ell a ρ θ₁ hc (nuPsi ell a t ρ β θ₁ hc A6 hEG) (deltaPsi ell a t ρ β θ₁ hc A6 hEG) hνψ hδψ
      ≤ cg1 ell a t ρ θ₁ hc (nuPsi ell a t ρ β θ₁ hc A6 hEG) := by
    rw [EGM1_GL, cg1_GL]; exact B10.le
  have hN1 : EN1free ell a t ρ θ₁ hc (nuPsi ell a t ρ β θ₁ hc A6 hEG) (deltaPsi ell a t ρ β θ₁ hc A6 hEG) hνψ hδψ A6 hcg1
      hEG1 < 1 / bN1 ell a t ρ θ₁ hc (nuPsi ell a t ρ β θ₁ hc A6 hEG) := by
    rw [EN1free_GL, cg1_GL, bN1_GL]; exact B11
  have hε' : 2 * CHfree ell a t ρ θ₁ hc A6 hEG * JSfree β * K2free ell ρ * KhatM0 ell a t ρ < 1 := P6
  let Num : M0ClassNum ell a t ρ β θ₁ :=
    ⟨hθ₁, hβ0, hc, A6, hEG, hN, hK2c, P5.le, hνψ, hδψ, hcg1, hEG1, hN1, hε'⟩
  refine ⟨⟨P8.le, P9.le, P10⟩, ⟨P11.le, P12, P13⟩, Num, P7.le, ?_, ?_⟩
  · rw [eps2op_CHf]; exact Pop
  · rw [AdalyFormal.DLayer.gam0M0_eq_f, eps2op_CHf]; exact P7op.le

#print axioms eps2op_CHf
#print axioms stageB2

end AdalyFormal.DLayer
