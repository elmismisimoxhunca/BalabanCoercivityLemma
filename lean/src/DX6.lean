import DX5

/-!
# DX6 -- lane B's `DLayerObligation` on the M1 regime, modulo W4 with a fixed constant (M1 D-layer lane, 2026-10-14)

* `DLayerObligationW4 ℓ M R hell a cw` : lane B's `DLayerObligation` (M1B) with ONE extra premise per configuration:
  W4 at `U` with the constant `cw` (`cw · wnormSq A ≤ ⟪A, G⁻¹A⟫` on `E₀`);
* **`dlayerObligationW4_holds`** : for `ℓ ≥ 2`, `a > 0`, `cw > 0` there is `N₀` such that `DLayerObligationW4 ℓ M R hell a cw`
  holds for EVERY `M ≥ 5`, `R ≥ 8ℓ`, `RM ≥ max(18ℓ, N₀)`; the threshold `a₁` is `k`-free;
* `dlayerObligation_of_W4` : if W4 holds with constant `cw` on every configuration the obligation quantifies over, then
  lane B's `DLayerObligation` holds (M1B's `M1Core_of_DL` then applies).
Named input: W4 with a constant `cw` uniform over the regime.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1 (M1Regular wnormSq DLayerStrat DLayerObligation)
open AdalyFormal.StatementLane2 (CoversOm0p)

/-- lane B's obligation with W4 (constant `cw`) as a premise at every configuration -/
def DLayerObligationW4 (ell M R : ℕ) (hell : 0 < ell) (a cw : ℝ) : Prop :=
  ∀ ε2s : ℝ, 0 < ε2s → ∀ εJ : ℝ, 0 < εJ → ∃ a₁ : ℝ, 0 < a₁ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₁ →
    TorusOK ell M Lu →
    ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S → CoversOm0p ell M 12 k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
        cw * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) ≤ ⟪A, (gparams ell k Lu hell S U a Lam).data.Ginv A⟫) →
      DLayerStrat ell k Lu hell S U a Lam ε2s εJ

/-- **the D-layer obligation on the M1 regime, modulo W4** -/
theorem dlayerObligationW4_holds {ell : ℕ} (hell2 : 2 ≤ ell) (hell : 0 < ell) {a : ℝ} (ha : 0 < a) {cw : ℝ}
    (hcw : 0 < cw) :
    ∃ N₀ : ℕ, ∀ M R : ℕ, 5 ≤ M → 8 * ell ≤ R → 18 * ell ≤ R * M → N₀ ≤ R * M →
      DLayerObligationW4 ell M R hell a cw := by
  obtain ⟨C1, hC1, N1, t1, ht1, h1⟩ := clause1_M1 hell2 ha hcw
  obtain ⟨C2, hC2, N2, t2, ht2, h2⟩ := clause2_M1 hell2 ha hcw
  refine ⟨max N1 N2, fun M R hM5 hR8 hroom hN ε2s hε2s εJ hεJ => ?_⟩
  refine ⟨min (min t1 t2) (min (ε2s / (C1 + 1)) (εJ / (C2 + 1))),
    lt_min (lt_min ht1 ht2) (lt_min (by positivity) (by positivity)), ?_⟩
  intro k hk Lu α₀ hα ht hT S hS hcov Lam hL U hU hW4
  have hM : 0 < M := by omega
  have hLu5 : ∀ μ, 5 ≤ Lu μ + 1 := fun μ => le_trans hM5 (Nat.le_of_dvd (Nat.succ_pos _) (hT.2.2 μ))
  have hLu : ∀ μ, ell < Lu μ + 1 := hT.2.1
  have ht0 : 0 ≤ (12 : ℝ) * M * α₀ := by positivity
  have hta : (12 : ℝ) * M * α₀ ≤ t1 := ht.trans ((min_le_left _ _).trans (min_le_left _ _))
  have htb : (12 : ℝ) * M * α₀ ≤ t2 := ht.trans ((min_le_left _ _).trans (min_le_right _ _))
  have htc : (12 : ℝ) * M * α₀ ≤ ε2s / (C1 + 1) := ht.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htd : (12 : ℝ) * M * α₀ ≤ εJ / (C2 + 1) := ht.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc1 : C1 * ((12 : ℝ) * M * α₀) ≤ ε2s := by
    have h := mul_le_mul_of_nonneg_left htc (show 0 ≤ C1 + 1 by linarith)
    rw [mul_div_cancel₀ _ (by positivity : (C1 + 1 : ℝ) ≠ 0)] at h
    nlinarith
  have hc2 : C2 * ((12 : ℝ) * M * α₀) ≤ εJ := by
    have h := mul_le_mul_of_nonneg_left htd (show 0 ≤ C2 + 1 by linarith)
    rw [mul_div_cancel₀ _ (by positivity : (C2 + 1 : ℝ) ≠ 0)] at h
    nlinarith
  refine ⟨fun x => ?_, fun Bt _ _ => ?_⟩
  · have h := h1 hell hS hM hR8 hroom ((le_max_left _ _).trans hN) hLu5 hLu hα.le hta U hU Lam hW4 x
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right hc1 (wnormSq_nonneg' S _)
  · exact (h2 hell hS hM hR8 hroom ((le_max_right _ _).trans hN) hLu5 hT hα htb Lam hL U hU hW4 _).trans
      (mul_le_mul_of_nonneg_right hc2 (sq_nonneg _))

/-- **with a uniform W4 the lane-B obligation holds** -/
theorem dlayerObligation_of_W4 {ell M R : ℕ} {hell : 0 < ell} {a cw : ℝ} (h : DLayerObligationW4 ell M R hell a cw)
    (hW4 : ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → TorusOK ell M Lu →
      ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S → CoversOm0p ell M 12 k S →
      ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
      ∀ (U : LinkCfg (scaleUp ell k Lu)), M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      ∀ A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
        cw * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) ≤ ⟪A, (gparams ell k Lu hell S U a Lam).data.Ginv A⟫) :
    DLayerObligation ell M R hell a := by
  intro ε2s hε2s εJ hεJ
  obtain ⟨a₁, ha₁, hall⟩ := h ε2s hε2s εJ hεJ
  exact ⟨a₁, ha₁, fun k hk Lu α₀ hα hsm hT S hS hcov Lam hL U hU =>
    hall k hk Lu α₀ hα hsm hT S hS hcov Lam hL U hU (hW4 k hk Lu α₀ hα hT S hS hcov Lam hL U hU)⟩

#print axioms DLayerObligationW4
#print axioms dlayerObligationW4_holds
#print axioms dlayerObligation_of_W4

end AdalyFormal.M1DStrat
