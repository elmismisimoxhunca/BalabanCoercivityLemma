import M1B
import DLR2

/-!
# DS1 -- the stratified D-layer premises at ONE configuration from six elementary premises (M1 D-layer lane, 2026-10-13)

Generic in `P : IngrBParams` (no `Ω₀ = univ`, any tower).  Weights: a bond weight `ω b > 0` (to be `ℓ^{-3 bstrat b}`), and lane B's
`wnormSq P.S P.ell P.k` (`Σ_b ℓ^{-2 bstrat b}|A b|²`).
* `psi_le_of_wcol` : weighted column bound of `H` + `‖Jf b‖ ≤ SJ·ω b` ⟹ `‖ψ(p)‖ ≤ CΨ·SJ` (the D2 form: `Σ_b ω_b ‖H(b,c)‖ ≤ CΨ`).
* `psi1u_le_of_wcol` : the same for `ψ₁ = H₁in* Jf` (the D5 form).
* **`delta2_strat`** (D1 without `hOm`): `|⟪A,Δ⁽²⁾A⟫| ≤ 2·Sψ·K2·CW·wnormSq A` from `‖ψ‖ ≤ Sψ`, the stratified quadratic ℓ¹ bound
  `Σ_p ‖C2fullOf z p‖ ≤ K2·wnormSq z` (D4) and the weighted bound `wnormSq (W ιA) ≤ CW·wnormSq A` of the gauge-fixing map.
* **`hJ_strat`** : `|⟪H₁in(D2in B), Jf⟫| ≤ (CH1·SJ)·KD·‖B‖²` from the weighted `H₁in` columns and `Σ_e ‖D2in B e‖ ≤ KD‖B‖²`.
* **`dlayerStrat_of_parts`** : lane B's `DLayerStrat` at one point from the six premises.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.DLayer (psiD psi1u delta2_abs_le inner_single_right norm_le_of_pair hJ_le)
open AdalyFormal.M1

/-- **ψ from a WEIGHTED column bound of `H`**: `Σ_b ω_b ‖(Hδ_p v)(b)‖ ≤ CΨ‖v‖` and `‖Jf b‖ ≤ SJ ω_b` give `‖ψ(p)‖ ≤ CΨ SJ`. -/
theorem psi_le_of_wcol (P : IngrBParams) (ω : Bond P.Lf → ℝ) (CΨ SJ : ℝ) (hCΨ : 0 ≤ CΨ) (hSJ : 0 ≤ SJ)
    (hcol : ∀ (p : BIdx P.G) (v : SuTwo),
      ∑ b, ω b * ‖(iE P.G (P.data.H (WithLp.toLp 2 (Pi.single p v) : FSp P.G))) b‖ ≤ CΨ * ‖v‖)
    (hJ : ∀ b, ‖P.Jf b‖ ≤ SJ * ω b) (p : BIdx P.G) : ‖psiD P p‖ ≤ CΨ * SJ := by
  classical
  refine norm_le_of_pair _ _ (mul_nonneg hCΨ hSJ) (fun v => ?_)
  set z : FSp P.G := WithLp.toLp 2 (Pi.single p v) with hz
  have h1 : ⟪psiD P p, v⟫ = ⟪psiD P, z⟫ := (inner_single_right (psiD P) p v).symm
  have h2 : ⟪psiD P, z⟫ = ⟪P.data.J, P.data.H z⟫ := by
    unfold psiD; rw [ContinuousLinearMap.adjoint_inner_left]
  have h3 : ⟪P.data.J, P.data.H z⟫ = ⟪P.Jf, iE P.G (P.data.H z)⟫ := by
    show ⟪pE P.G P.Jf, _⟫ = _
    rw [pE_inner_left]
  rw [h1, h2, h3, PiLp.inner_apply]
  calc ∑ b, ⟪P.Jf b, (iE P.G (P.data.H z)) b⟫ ≤ ∑ b, ‖P.Jf b‖ * ‖(iE P.G (P.data.H z)) b‖ :=
        Finset.sum_le_sum (fun b _ => real_inner_le_norm _ _)
    _ ≤ ∑ b, (SJ * ω b) * ‖(iE P.G (P.data.H z)) b‖ :=
        Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_right (hJ b) (norm_nonneg _))
    _ = SJ * ∑ b, ω b * ‖(iE P.G (P.data.H z)) b‖ := by rw [Finset.mul_sum]; congr 1; funext b; ring
    _ ≤ SJ * (CΨ * ‖v‖) := mul_le_mul_of_nonneg_left (hcol p v) hSJ
    _ = CΨ * SJ * ‖v‖ := by ring

/-- the same for `ψ₁ = H₁in* Jf` -/
theorem psi1u_le_of_wcol (P : IngrBParams) (ω : Bond P.Lf → ℝ) (CH1 SJ : ℝ) (hCH1 : 0 ≤ CH1) (hSJ : 0 ≤ SJ)
    (e : Bond P.Lu)
    (hcol : ∀ v : SuTwo,
      ∑ b, ω b * ‖(P.H1in (WithLp.toLp 2 (Pi.single e v) : BondFnL2 P.Lu)) b‖ ≤ CH1 * ‖v‖)
    (hJ : ∀ b, ‖P.Jf b‖ ≤ SJ * ω b) : ‖psi1u P e‖ ≤ CH1 * SJ := by
  classical
  refine norm_le_of_pair _ _ (mul_nonneg hCH1 hSJ) (fun v => ?_)
  set z : BondFnL2 P.Lu := WithLp.toLp 2 (Pi.single e v) with hz
  have h1 : ⟪psi1u P e, v⟫ = ⟪psi1u P, z⟫ := (inner_single_right (psi1u P) e v).symm
  have h2 : ⟪psi1u P, z⟫ = ⟪P.Jf, P.H1in z⟫ := by
    unfold psi1u; rw [ContinuousLinearMap.adjoint_inner_left]
  rw [h1, h2, PiLp.inner_apply]
  calc ∑ b, ⟪P.Jf b, (P.H1in z) b⟫ ≤ ∑ b, ‖P.Jf b‖ * ‖(P.H1in z) b‖ :=
        Finset.sum_le_sum (fun b _ => real_inner_le_norm _ _)
    _ ≤ ∑ b, (SJ * ω b) * ‖(P.H1in z) b‖ :=
        Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_right (hJ b) (norm_nonneg _))
    _ = SJ * ∑ b, ω b * ‖(P.H1in z) b‖ := by rw [Finset.mul_sum]; congr 1; funext b; ring
    _ ≤ SJ * (CH1 * ‖v‖) := mul_le_mul_of_nonneg_left (hcol v) hSJ
    _ = CH1 * SJ * ‖v‖ := by ring

/-- **D1 without `hOm`**: the stratified form bound of `Δ⁽²⁾`. -/
theorem delta2_strat (P : IngrBParams) (Sψ K2 CW : ℝ) (hS : 0 ≤ Sψ) (hK2 : 0 ≤ K2)
    (hψ : ∀ p, ‖psiD P p‖ ≤ Sψ)
    (hC : ∀ z : BondFnL2 P.Lf, ∑ p, ‖C2fullOf P.G P.U z p‖ ≤ K2 * wnormSq P.S P.ell P.k z)
    (hW : ∀ A : ↥(bondSupp P.G), wnormSq P.S P.ell P.k (Wop P.G P.U P.a (iE P.G A))
      ≤ CW * wnormSq P.S P.ell P.k (A : BondFnL2 P.Lf))
    (A : ↥(bondSupp P.G)) :
    |⟪A, P.data.Delta2 P.data_laws A⟫| ≤ 2 * Sψ * K2 * CW * wnormSq P.S P.ell P.k (A : BondFnL2 P.Lf) := by
  have h1 := delta2_abs_le P Sψ hψ A
  have hC2 : P.data.C2 A = C2fullOf P.G P.U (Wop P.G P.U P.a (iE P.G A)) := rfl
  rw [hC2] at h1
  have h2 := hC (Wop P.G P.U P.a (iE P.G A))
  have h3 := hW A
  calc |⟪A, P.data.Delta2 P.data_laws A⟫|
        ≤ 2 * Sψ * ∑ p, ‖C2fullOf P.G P.U (Wop P.G P.U P.a (iE P.G A)) p‖ := h1
    _ ≤ 2 * Sψ * (K2 * wnormSq P.S P.ell P.k (Wop P.G P.U P.a (iE P.G A))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 2 * Sψ * (K2 * (CW * wnormSq P.S P.ell P.k (A : BondFnL2 P.Lf))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hK2) (by positivity)
    _ = 2 * Sψ * K2 * CW * wnormSq P.S P.ell P.k (A : BondFnL2 P.Lf) := by ring

/-- **the J cross term**: weighted `H₁in` columns at every unit bond, `sup ‖Jf‖/ω ≤ SJ`, quadratic ℓ¹ bound of `D2in`. -/
theorem hJ_strat (P : IngrBParams) (ω : Bond P.Lf → ℝ) (CH1 SJ KD : ℝ) (hCH1 : 0 ≤ CH1) (hSJ : 0 ≤ SJ)
    (hcol : ∀ (e : Bond P.Lu) (v : SuTwo),
      ∑ b, ω b * ‖(P.H1in (WithLp.toLp 2 (Pi.single e v) : BondFnL2 P.Lu)) b‖ ≤ CH1 * ‖v‖)
    (hJ : ∀ b, ‖P.Jf b‖ ≤ SJ * ω b)
    (B : BondFnL2 P.Lu) (hKD : ∑ e, ‖(P.D2in B) e‖ ≤ KD * ‖B‖ ^ 2) :
    |⟪P.H1in (P.D2in B), P.Jf⟫| ≤ (CH1 * SJ) * KD * ‖B‖ ^ 2 := by
  have hψ1 : ∀ e, ‖psi1u P e‖ ≤ CH1 * SJ := fun e => psi1u_le_of_wcol P ω CH1 SJ hCH1 hSJ e (hcol e) hJ
  have h1 := hJ_le P (CH1 * SJ) hψ1 B
  calc _ ≤ CH1 * SJ * ∑ e, ‖(P.D2in B) e‖ := h1
    _ ≤ CH1 * SJ * (KD * ‖B‖ ^ 2) := mul_le_mul_of_nonneg_left hKD (mul_nonneg hCH1 hSJ)
    _ = (CH1 * SJ) * KD * ‖B‖ ^ 2 := by ring

/-- the six elementary premises at one configuration (`ω` = the J-scaling weight; `wnormSq` = lane B's weighted norm). -/
structure DParts (P : IngrBParams) (ω : Bond P.Lf → ℝ) (SJ CΨ K2 CW CH1 KD : ℝ) : Prop where
  hSJ : 0 ≤ SJ
  hCΨ : 0 ≤ CΨ
  hK2 : 0 ≤ K2
  hCH1 : 0 ≤ CH1
  /-- D3: the source is stratum-scaled -/
  hJ : ∀ b, ‖P.Jf b‖ ≤ SJ * ω b
  /-- D2: weighted ℓ¹ columns of `H` -/
  hHcol : ∀ (p : BIdx P.G) (v : SuTwo),
    ∑ b, ω b * ‖(iE P.G (P.data.H (WithLp.toLp 2 (Pi.single p v) : FSp P.G))) b‖ ≤ CΨ * ‖v‖
  /-- D4: stratified quadratic ℓ¹ bound of the composite second jet -/
  hC2 : ∀ z : BondFnL2 P.Lf, ∑ p, ‖C2fullOf P.G P.U z p‖ ≤ K2 * wnormSq P.S P.ell P.k z
  /-- weighted bound of the gauge-fixing map `W` -/
  hW : ∀ A : ↥(bondSupp P.G), wnormSq P.S P.ell P.k (Wop P.G P.U P.a (iE P.G A))
      ≤ CW * wnormSq P.S P.ell P.k (A : BondFnL2 P.Lf)
  /-- D5: weighted ℓ¹ columns of `H₁in` -/
  hH1col : ∀ (e : Bond P.Lu) (v : SuTwo),
    ∑ b, ω b * ‖(P.H1in (WithLp.toLp 2 (Pi.single e v) : BondFnL2 P.Lu)) b‖ ≤ CH1 * ‖v‖
  /-- D4': quadratic ℓ¹ bound of `D̃⁽²⁾` -/
  hKD : ∀ B : BondFnL2 P.Lu, ∑ e, ‖(P.D2in B) e‖ ≤ KD * ‖B‖ ^ 2

/-- the two pieces of `DLayerStrat` with explicit constants, at a generic `P`. -/
theorem dparts_bounds (P : IngrBParams) (ω : Bond P.Lf → ℝ) (SJ CΨ K2 CW CH1 KD : ℝ)
    (h : DParts P ω SJ CΨ K2 CW CH1 KD) :
    (∀ x : ↥(bondSupp P.G), |⟪x, P.data.Delta2 P.data_laws x⟫|
        ≤ (2 * (CΨ * SJ) * K2 * CW) * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf)) ∧
    ∀ B : BondFnL2 P.Lu, |⟪P.H1in (P.D2in B), P.Jf⟫| ≤ ((CH1 * SJ) * KD) * ‖B‖ ^ 2 := by
  have hψ : ∀ p, ‖psiD P p‖ ≤ CΨ * SJ := psi_le_of_wcol P ω CΨ SJ h.hCΨ h.hSJ h.hHcol h.hJ
  refine ⟨fun x => ?_, fun B => ?_⟩
  · exact delta2_strat P (CΨ * SJ) K2 CW (mul_nonneg h.hCΨ h.hSJ) h.hK2 hψ h.hC2 h.hW x
  · exact hJ_strat P ω CH1 SJ KD h.hCH1 h.hSJ h.hH1col h.hJ B (h.hKD B)

/-- **lane B's `DLayerStrat` at one point from the six premises** (tolerances: any `ε2s ≥ 2 CΨ SJ K2 CW`, `εJ ≥ CH1 SJ KD`). -/
theorem dlayerStrat_of_parts (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (ε2s εJ : ℝ)
    (ω : Bond (scaleUp ell k Lu) → ℝ) (SJ CΨ K2 CW CH1 KD : ℝ)
    (h : DParts (gparams ell k Lu hell S U a Lam) ω SJ CΨ K2 CW CH1 KD)
    (h2 : 2 * (CΨ * SJ) * K2 * CW ≤ ε2s) (hJ : (CH1 * SJ) * KD ≤ εJ) :
    DLayerStrat ell k Lu hell S U a Lam ε2s εJ := by
  obtain ⟨hA, hB⟩ := dparts_bounds (gparams ell k Lu hell S U a Lam) ω SJ CΨ K2 CW CH1 KD h
  refine ⟨fun x => (hA x).trans ?_, fun Bt _ _ => (hB _).trans ?_⟩
  · have : 0 ≤ wnormSq S ell k (x : BondFnL2 (scaleUp ell k Lu)) := by
      unfold wnormSq; exact Finset.sum_nonneg (fun b _ => by positivity)
    exact mul_le_mul_of_nonneg_right h2 this
  · exact mul_le_mul_of_nonneg_right hJ (sq_nonneg _)

#print axioms psi_le_of_wcol
#print axioms psi1u_le_of_wcol
#print axioms delta2_strat
#print axioms hJ_strat
#print axioms dparts_bounds
#print axioms dlayerStrat_of_parts

end AdalyFormal.M1DStrat
