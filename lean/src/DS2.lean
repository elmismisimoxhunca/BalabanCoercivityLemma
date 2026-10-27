import DS1

/-!
# DS2 -- `DLayerObligation` (lane B) from a k-free package of the six premises (M1 D-layer lane, 2026-10-13)

`DPackage ell M R hell a`: there are `β₀ > 0` and constants `cJ, CΨ, K2, CW, CH1, KD ≥ 0` (free of `k`, the torus, the tower, `Λ`,
`U`, `α₀`) such that on the whole M1 domain of `DLayerObligation` with `12Mα₀ ≤ β₀` the six premises `DParts` hold with
`SJ = cJ·(12Mα₀)` and the J-weight `ω b = (ℓ^{bstrat b})⁻¹ ^ 3`.
* **`dlayerObligation_of_package`** : `DPackage → DLayerObligation` (the smallness is `SJ ∝ α₀`; every other constant is fixed).
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
open AdalyFormal.M1

/-- the J-scaling bond weight `ℓ^{-3 bstrat b}` -/
noncomputable def omJ {L : PeriodicLatticeExtent} (S : Tower L) (ell k : ℕ) (b : Bond L) : ℝ :=
  (((ell : ℝ) ^ bstrat S k b)⁻¹) ^ 3

/-- **the package**: k-free constants for the six premises on the M1 domain, `SJ = cJ·(12Mα₀)`. -/
def DPackage (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ cJ CΨ K2 CW CH1 KD : ℝ, 0 ≤ cJ ∧ 0 ≤ CΨ ∧ 0 ≤ K2 ∧ 0 ≤ CW ∧ 0 ≤ CH1 ∧ 0 ≤ KD ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ β₀ →
    TorusOK ell M Lu →
    ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S → CoversOm0p ell M 12 k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      DParts (gparams ell k Lu hell S U a Lam) (omJ S ell k) (cJ * ((12 : ℝ) * M * α₀)) CΨ K2 CW CH1 KD

/-- **`DLayerObligation` from the package.** -/
theorem dlayerObligation_of_package {ell M R : ℕ} {hell : 0 < ell} {a : ℝ} (h : DPackage ell M R hell a) :
    DLayerObligation ell M R hell a := by
  obtain ⟨β₀, hβ₀, cJ, CΨ, K2, CW, CH1, KD, hcJ, hCΨ, hK2, hCW, hCH1, hKD, hall⟩ := h
  intro ε2s hε2s εJ hεJ
  set c2 : ℝ := 2 * (CΨ * cJ) * K2 * CW + 1 with hc2
  set cJJ : ℝ := (CH1 * cJ) * KD + 1 with hcJJ
  have hc2p : 0 < c2 := by positivity
  have hcJp : 0 < cJJ := by positivity
  refine ⟨min β₀ (min (ε2s / c2) (εJ / cJJ)), lt_min hβ₀ (lt_min (div_pos hε2s hc2p) (div_pos hεJ hcJp)), ?_⟩
  intro k hk Lu α₀ hα hsm hT S hS hcov Lam hL U hU
  set β : ℝ := (12 : ℝ) * M * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hb1 : β ≤ β₀ := hsm.trans (min_le_left _ _)
  have hb2 : β ≤ ε2s / c2 := hsm.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb3 : β ≤ εJ / cJJ := hsm.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP := hall k hk Lu α₀ hα hb1 hT S hS hcov Lam hL U hU
  refine dlayerStrat_of_parts ell k Lu hell S U a Lam ε2s εJ (omJ S ell k) (cJ * β) CΨ K2 CW CH1 KD hP ?_ ?_
  · have e1 : β * c2 ≤ ε2s := by rwa [le_div_iff₀ hc2p] at hb2
    have : 2 * (CΨ * (cJ * β)) * K2 * CW = (2 * (CΨ * cJ) * K2 * CW) * β := by ring
    rw [this]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCΨ hcJ) hK2) hCW) hβ0]
  · have e1 : β * cJJ ≤ εJ := by rwa [le_div_iff₀ hcJp] at hb3
    have : (CH1 * (cJ * β)) * KD = ((CH1 * cJ) * KD) * β := by ring
    rw [this]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hCH1 hcJ) hKD) hβ0]

#print axioms omJ
#print axioms DPackage
#print axioms dlayerObligation_of_package

end AdalyFormal.M1DStrat
