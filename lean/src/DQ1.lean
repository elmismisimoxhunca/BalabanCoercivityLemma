import DS3
import DLR107
import GCa4

/-!
# DQ1 -- a cut-off exponential configuration and its link / plaquette bounds (sub-builder DQ of the M1 D-layer lane, 2026-10-13)

Generic in the lattice.  Given a Hermitian traceless field `A`, a step `η ≥ 0` and a cut-off `χ` with values in `[0,1]`,
`cutCfg η χ A hA e = exp(i η χ(e₋) A(e))` (in `SU(2)` by `ClassPropagationUbar.exp_mem_special`).
* `cutH_le` / `cut_link` : if `η‖A e‖ ≤ a₁` wherever `χ(e₋) ≠ 0`, then `‖iηχA(e)‖ ≤ a₁` and `dv ≤ 2a₁` (`a₁ ≤ 1/2`).
* **`cut_plaq`** : if in addition `η‖A(x+μ,ν) − A(x,ν)‖ ≤ a₂` wherever `χ(x+μ) ≠ 0`, `η‖A(x,ν)‖ ≤ a₁` wherever `χ(x) ≠ 0` or
  `χ(x+μ) ≠ 0`, and `|χ(x+μ) − χ(x)| ≤ λ`, then every plaquette holonomy has
  `dv ≤ 2(a₂ + λa₁) + 8a₁² + 512a₁³`  (`4a₁ ≤ 1`; DL55 `exp4`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1DStrat.DQ

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.DLayer (AHT exp4 S4 T4 Exp2 HT_AHT fN_add fN_sub fN_neg fN_csmul fN_zero exp_conjT exp_sub_one_le)
open AdalyFormal.CurvBlock (dv)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

/-- the cut-off exponent `i η χ(e₋) A(e)` -/
noncomputable def cutH (η : ℝ) (χ : PeriodicLatticeSite L → ℝ) (A : Bond L → Mt) (e : Bond L) : Mt :=
  (((η * χ e.1 : ℝ) : ℂ) * Complex.I) • A e

theorem cutH_AHT (η : ℝ) (χ : PeriodicLatticeSite L → ℝ) (A : Bond L → Mt)
    (hA : ∀ e, (A e)ᴴ = A e ∧ Matrix.trace (A e) = 0) (e : Bond L) : AHT (cutH η χ A e) :=
  HT_AHT _ _ (hA e)

/-- the cut-off configuration -/
noncomputable def cutCfg (η : ℝ) (χ : PeriodicLatticeSite L → ℝ) (A : Bond L → Mt)
    (hA : ∀ e, (A e)ᴴ = A e ∧ Matrix.trace (A e) = 0) : PeriodicLinkConfiguration SU2 L :=
  fun e => ⟨NormedSpace.exp (cutH η χ A e),
    AdalyFormal.Balaban.ClassPropagationUbar.exp_mem_special (cutH_AHT η χ A hA e).ah (cutH_AHT η χ A hA e).tr⟩

theorem cutCfg_coe (η : ℝ) (χ : PeriodicLatticeSite L → ℝ) (A : Bond L → Mt)
    (hA : ∀ e, (A e)ᴴ = A e ∧ Matrix.trace (A e) = 0) (e : Bond L) :
    ((cutCfg η χ A hA e : SU2) : Mt) = NormedSpace.exp (cutH η χ A e) := rfl

/-- where `χ = 1` the cut-off configuration is `exp(iηA)` -/
theorem cutH_of_one (η : ℝ) (χ : PeriodicLatticeSite L → ℝ) (A : Bond L → Mt) (e : Bond L) (h : χ e.1 = 1) :
    cutH η χ A e = (((η : ℝ) : ℂ) * Complex.I) • A e := by
  unfold cutH; rw [h, mul_one]

theorem norm_ofReal_mul_I (r : ℝ) : ‖((r : ℂ) * Complex.I)‖ = |r| := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem cutH_le (η : ℝ) (χ : PeriodicLatticeSite L → ℝ) (A : Bond L → Mt) (a1 : ℝ) (hη : 0 ≤ η)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) (ha1 : 0 ≤ a1)
    (h1 : ∀ e : Bond L, χ e.1 ≠ 0 → η * frobNorm (A e) ≤ a1) (e : Bond L) :
    frobNorm (cutH η χ A e) ≤ a1 := by
  unfold cutH
  rw [fN_csmul, norm_ofReal_mul_I, abs_of_nonneg (mul_nonneg hη (hχ0 e.1))]
  by_cases hc : χ e.1 = 0
  · rw [hc, mul_zero, zero_mul]; exact ha1
  · have h := h1 e hc
    have hA := frobNorm_nonneg (A e)
    have : η * χ e.1 * frobNorm (A e) ≤ η * frobNorm (A e) := by
      have := mul_le_mul_of_nonneg_right (hχ1 e.1) (mul_nonneg hη hA)
      nlinarith
    linarith

theorem cut_link (η : ℝ) (χ : PeriodicLatticeSite L → ℝ) (A : Bond L → Mt)
    (hA : ∀ e, (A e)ᴴ = A e ∧ Matrix.trace (A e) = 0) (a1 : ℝ) (hη : 0 ≤ η)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1)
    (h1 : ∀ e : Bond L, χ e.1 ≠ 0 → η * frobNorm (A e) ≤ a1) (e : Bond L) :
    dv (cutCfg η χ A hA e) ≤ 2 * a1 := by
  have hH := cutH_le η χ A a1 hη hχ0 hχ1 ha1 h1 e
  show frobNorm (NormedSpace.exp (cutH η χ A e) - 1) ≤ 2 * a1
  exact (exp_sub_one_le _ (cutH_AHT η χ A hA e) (hH.trans ha1')).trans (by linarith)

/-- the difference of two cut-off exponents along a direction -/
theorem cutH_diff_le (η : ℝ) (χ : PeriodicLatticeSite L → ℝ) (A : Bond L → Mt) (a1 a2 lam : ℝ) (hη : 0 ≤ η)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hlam : 0 ≤ lam)
    (x : PeriodicLatticeSite L) (μ ν : Fin 3)
    (h2 : χ (periodicLatticeShift x μ) ≠ 0 →
      η * frobNorm (A (periodicLatticeShift x μ, ν) - A (x, ν)) ≤ a2)
    (h1 : χ x ≠ 0 ∨ χ (periodicLatticeShift x μ) ≠ 0 → η * frobNorm (A (x, ν)) ≤ a1)
    (hlip : |χ (periodicLatticeShift x μ) - χ x| ≤ lam) :
    frobNorm (cutH η χ A (periodicLatticeShift x μ, ν) - cutH η χ A (x, ν)) ≤ a2 + lam * a1 := by
  set c1 : ℂ := ((η * χ (periodicLatticeShift x μ) : ℝ) : ℂ) * Complex.I with hc1
  set c0 : ℂ := ((η * χ x : ℝ) : ℂ) * Complex.I with hc0
  set cd : ℂ := ((η * (χ (periodicLatticeShift x μ) - χ x) : ℝ) : ℂ) * Complex.I with hcd
  have hcd' : c1 - c0 = cd := by rw [hc1, hc0, hcd]; push_cast; ring
  have e1 : cutH η χ A (periodicLatticeShift x μ, ν) - cutH η χ A (x, ν)
      = c1 • (A (periodicLatticeShift x μ, ν) - A (x, ν)) + cd • A (x, ν) := by
    unfold cutH
    rw [← hcd', smul_sub, sub_smul]
    abel
  rw [e1]
  refine (fN_add _ _).trans ?_
  rw [fN_csmul, fN_csmul, hc1, hcd, norm_ofReal_mul_I, norm_ofReal_mul_I]
  have t1 : |η * χ (periodicLatticeShift x μ)| * frobNorm (A (periodicLatticeShift x μ, ν) - A (x, ν)) ≤ a2 := by
    rw [abs_of_nonneg (mul_nonneg hη (hχ0 _))]
    by_cases hc : χ (periodicLatticeShift x μ) = 0
    · rw [hc, mul_zero, zero_mul]; exact ha2
    · have h := h2 hc
      have hA := frobNorm_nonneg (A (periodicLatticeShift x μ, ν) - A (x, ν))
      have := mul_le_mul_of_nonneg_right (hχ1 (periodicLatticeShift x μ)) (mul_nonneg hη hA)
      nlinarith
  have t2 : |η * (χ (periodicLatticeShift x μ) - χ x)| * frobNorm (A (x, ν)) ≤ lam * a1 := by
    rw [abs_mul, abs_of_nonneg hη]
    by_cases hc : χ x = 0 ∧ χ (periodicLatticeShift x μ) = 0
    · rw [hc.1, hc.2, sub_zero, abs_zero, mul_zero, zero_mul]; exact mul_nonneg hlam ha1
    · have hor : χ x ≠ 0 ∨ χ (periodicLatticeShift x μ) ≠ 0 := by
        by_contra hn; push Not at hn; exact hc hn
      have h := h1 hor
      have hA := frobNorm_nonneg (A (x, ν))
      have e2 : η * |χ (periodicLatticeShift x μ) - χ x| * frobNorm (A (x, ν))
          = |χ (periodicLatticeShift x μ) - χ x| * (η * frobNorm (A (x, ν))) := by ring
      rw [e2]
      exact mul_le_mul hlip h (mul_nonneg hη hA) hlam
  linarith

/-- **the plaquette bound of the cut-off configuration** -/
theorem cut_plaq (η : ℝ) (χ : PeriodicLatticeSite L → ℝ) (A : Bond L → Mt)
    (hA : ∀ e, (A e)ᴴ = A e ∧ Matrix.trace (A e) = 0) (a1 a2 lam : ℝ) (hη : 0 ≤ η)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hlam : 0 ≤ lam) (h4 : 4 * a1 ≤ 1)
    (h2 : ∀ (x : PeriodicLatticeSite L) (μ ν : Fin 3), χ (periodicLatticeShift x μ) ≠ 0 →
      η * frobNorm (A (periodicLatticeShift x μ, ν) - A (x, ν)) ≤ a2)
    (h1 : ∀ (x : PeriodicLatticeSite L) (μ ν : Fin 3), χ x ≠ 0 ∨ χ (periodicLatticeShift x μ) ≠ 0 →
      η * frobNorm (A (x, ν)) ≤ a1)
    (hlip : ∀ (x : PeriodicLatticeSite L) (μ : Fin 3), |χ (periodicLatticeShift x μ) - χ x| ≤ lam)
    (p : PeriodicLatticePlaquette L) :
    dv (periodicPlaquetteHolonomy (cutCfg η χ A hA) p) ≤ 2 * (a2 + lam * a1) + 8 * a1 ^ 2 + 512 * a1 ^ 3 := by
  obtain ⟨x, d⟩ := p
  set μ : Fin 3 := (d : Fin 3 × Fin 3).1 with hμ
  set ν : Fin 3 := (d : Fin 3 × Fin 3).2 with hν
  have h1e : ∀ e : Bond L, χ e.1 ≠ 0 → η * frobNorm (A e) ≤ a1 := fun e he => h1 e.1 0 e.2 (Or.inl he)
  set H1 := cutH η χ A (x, μ) with hH1
  set H2 := cutH η χ A (periodicLatticeShift x μ, ν) with hH2
  set H3 := cutH η χ A (periodicLatticeShift x ν, μ) with hH3
  set H4 := cutH η χ A (x, ν) with hH4
  have g1 := cutH_le η χ A a1 hη hχ0 hχ1 ha1 h1e (x, μ)
  have g2 := cutH_le η χ A a1 hη hχ0 hχ1 ha1 h1e (periodicLatticeShift x μ, ν)
  have g3 := cutH_le η χ A a1 hη hχ0 hχ1 ha1 h1e (periodicLatticeShift x ν, μ)
  have g4 := cutH_le η χ A a1 hη hχ0 hχ1 ha1 h1e (x, ν)
  have A1 := cutH_AHT η χ A hA (x, μ)
  have A2 := cutH_AHT η χ A hA (periodicLatticeShift x μ, ν)
  have A3 := cutH_AHT η χ A hA (periodicLatticeShift x ν, μ)
  have A4 := cutH_AHT η χ A hA (x, ν)
  have hcoe : ((periodicPlaquetteHolonomy (cutCfg η χ A hA) (x, d) : SU2) : Mt)
      = NormedSpace.exp H1 * NormedSpace.exp H2 * NormedSpace.exp (-H3) * NormedSpace.exp (-H4) := by
    show NormedSpace.exp H1 * NormedSpace.exp H2 * (NormedSpace.exp H3)ᴴ * (NormedSpace.exp H4)ᴴ = _
    rw [exp_conjT _ A3, exp_conjT _ A4]
  have f1 := frobNorm_nonneg H1
  have f2 := frobNorm_nonneg H2
  have f3 := frobNorm_nonneg H3
  have f4 := frobNorm_nonneg H4
  have hn3 : frobNorm (-H3) = frobNorm H3 := fN_neg H3
  have hn4 : frobNorm (-H4) = frobNorm H4 := fN_neg H4
  have hσ : frobNorm H1 + frobNorm H2 + frobNorm (-H3) + frobNorm (-H4) ≤ 4 * a1 := by
    rw [hn3, hn4]; linarith
  have hE := exp4 H1 H2 (-H3) (-H4) A1 A2 A3.neg A4.neg (hσ.trans h4)
  set σ := frobNorm H1 + frobNorm H2 + frobNorm (-H3) + frobNorm (-H4) with hσdef
  have hσ0 : 0 ≤ σ := hE.hσ
  -- the linear term
  have hS : frobNorm (S4 H1 H2 (-H3) (-H4)) ≤ 2 * (a2 + lam * a1) := by
    have eS : S4 H1 H2 (-H3) (-H4) = (H2 - H4) - (H3 - H1) := by unfold S4; abel
    rw [eS]
    have d1 : frobNorm (H2 - H4) ≤ a2 + lam * a1 :=
      cutH_diff_le η χ A a1 a2 lam hη hχ0 hχ1 ha1 ha2 hlam x μ ν (h2 x μ ν) (h1 x μ ν) (hlip x μ)
    have d2 : frobNorm (H3 - H1) ≤ a2 + lam * a1 :=
      cutH_diff_le η χ A a1 a2 lam hη hχ0 hχ1 ha1 ha2 hlam x ν μ (h2 x ν μ) (h1 x ν μ) (hlip x ν)
    exact (fN_sub _ _).trans (by linarith)
  have hP : frobNorm (NormedSpace.exp H1 * NormedSpace.exp H2 * NormedSpace.exp (-H3) * NormedSpace.exp (-H4) - 1)
      ≤ frobNorm (S4 H1 H2 (-H3) (-H4)) + σ ^ 2 / 2 + 8 * σ ^ 3 := by
    set P := NormedSpace.exp H1 * NormedSpace.exp H2 * NormedSpace.exp (-H3) * NormedSpace.exp (-H4)
    have e : P - 1 = S4 H1 H2 (-H3) (-H4) + T4 H1 H2 (-H3) (-H4) + (P - 1 - S4 H1 H2 (-H3) (-H4) - T4 H1 H2 (-H3) (-H4)) := by
      abel
    rw [e]
    refine (fN_add _ _).trans ?_
    have := (fN_add (S4 H1 H2 (-H3) (-H4)) (T4 H1 H2 (-H3) (-H4)))
    linarith [hE.rem, hE.hT]
  have hσ2 : σ ^ 2 / 2 ≤ 8 * a1 ^ 2 := by nlinarith
  have hσ3 : 8 * σ ^ 3 ≤ 512 * a1 ^ 3 := by
    have := pow_le_pow_left₀ hσ0 hσ 3
    nlinarith
  show frobNorm (((periodicPlaquetteHolonomy (cutCfg η χ A hA) (x, d) : SU2) : Mt) - 1) ≤ _
  rw [hcoe]
  linarith

#print axioms cutH
#print axioms cutCfg
#print axioms cutH_AHT
#print axioms cutCfg_coe
#print axioms cutH_of_one
#print axioms norm_ofReal_mul_I
#print axioms cutH_le
#print axioms cut_link
#print axioms cutH_diff_le
#print axioms cut_plaq

end AdalyFormal.M1DStrat.DQ
