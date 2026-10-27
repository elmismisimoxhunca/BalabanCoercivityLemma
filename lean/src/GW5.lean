import GW3

/-!
# GW5 -- W4 at `U` from `M1Regular` (M1 gauge lane, 2026-10-14)

`w4_M1` : for a witness `(g, A)` of `M1Regular`-type data (`U^g = exp(iηA)`, `M1Bounds`), the stratum-weighted coercivity
`cwW4 · wnormSq ≤ ⟪·, Ginv ·⟫` holds at `U` with the `k`-free mass-commutator constant `CMcStar … (SstarM …)`.
Hypotheses that remain: `PatchCoercive` (at `U`), the structural size conditions, and `W4Num` (k-free numerics).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1GaugeW4

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar delStar massComm_M1 qs_injective_M1 rho1_nonneg)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneG (gparams GenP.WellDef)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.M1 (M1Bounds)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

theorem hbig_of (ell k : ℕ) (Lu : PeriodicLatticeExtent) (h5 : ∀ μ, 5 ≤ Lu μ + 1) :
    ∀ σ, 4 * ell ^ k < scaleUp ell k Lu σ + 1 := by
  intro σ
  unfold scaleUp
  have h2 := h5 σ
  by_cases hell : ell = 0
  · subst hell
    by_cases hk : k = 0
    · subst hk; simp; omega
    · simp [zero_pow hk]
  · have hp : 1 ≤ ell ^ k := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hell)
    have h3 : 5 * ell ^ k ≤ (Lu σ + 1) * ell ^ k := Nat.mul_le_mul_right _ h2
    generalize (Lu σ + 1) * ell ^ k = P at h3 ⊢
    generalize ell ^ k = p at hp h3 ⊢
    omega

section main
variable {ell M R k f κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c) {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
  (hroom : 17 * ell ≤ R * M) (hLu5 : ∀ μ, 5 ≤ Lu μ + 1)
  (U : LinkCfg (scaleUp ell k Lu)) (g : PeriodicLatticeSite (scaleUp ell k Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ)
  (A0 : Bond (scaleUp ell k Lu) → Matrix (Fin 2) (Fin 2) ℂ) {α₀ η : ℝ}
  (hUg : ∀ e : Bond (scaleUp ell k Lu), ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp (((η : ℂ) * Complex.I) • A0 e))
  (hB : M1Bounds S ell M f k α₀ η A0) (hη : 0 < η) (hα0 : 0 ≤ α₀)
  (ha1 : (f : ℝ) * M * α₀ ≤ 1)
  (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 f M α₀ ≤ 1)
  (hsmA : (1 + 3 * Real.pi) * rho1 f M α₀ ≤ 1 / (1000 * (ell : ℝ) ^ 4))
  (hrr : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 f M α₀))
      < AdalyFormal.NonflatJet.r0)
include hell0 hS hκ hM hell hR1 hR hc hW hWR hroom hLu5 hUg hB hη hα0 ha1 hsm4 hsmA hrr

/-- **W4 at `U^g`** (the M1 gauge), no global tower hypothesis. -/
theorem w4_M1_gauged (a : ℝ) (ha : 0 < a) (Lam : Set (PeriodicLatticeSite Lu))
    (ε1 ε2 : ℝ) (hε1 : 0 < ε1) (hε2 : 0 < ε2) (hN : W4Num ell M f W a α₀ ε1)
    (cP : ℝ) (hP : PatchCoercive ell M k κ c Lu hell0 S (periodicGaugeTransform g U) a Lam cP)
    (A : ↥(bondSupp (gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam).G)) :
    cwW4 ell M κ c W a (rhoT ell f M α₀) (rho1 f M α₀) ε1 ε2 cP (epsXnum ell W a (rhoT ell f M α₀))
        (CMcStar ell M κ c a (SstarM ell f M α₀))
      * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S (periodicGaugeTransform g U) a Lam).data.Ginv A⟫ := by
  have hρ := rhoT_nonneg ell f M α₀ hα0
  obtain ⟨h216, h12⟩ := rhoT_smalls ell f M α₀ hα0 (by omega) hsm4
  have hT3 : ∀ μ, 3 ≤ Lu μ + 1 := fun μ => by have := hLu5 μ; omega
  have hU' := site_hU_M1 hell (hS := hS) U g A0 hUg hB hη hα0
  have hT' := site_hT_M1 hell hS (by nlinarith) (hbig_of ell k Lu hLu5) U g A0 hUg hB hη hα0 ha1 hsm4
  have ha0 : 0 ≤ (f : ℝ) * M * α₀ := by have := Real.pi_pos; positivity
  have hreg := holRegime_M1 hell0 U g A0 hUg hB hη ha0 ha1
  have hMass := massComm_M1 hell hS hroom hT3 U g A0 hUg hB hη hα0 ha1 hsm4 hsmA hrr hκ hM hR1 hR hc a ha.le
  have hCM : 0 ≤ CMcStar ell M κ c a (SstarM ell f M α₀) := by
    unfold AdalyFormal.TowerLoc.CMcStar AdalyFormal.TowerLoc.Estar
    have := KG_nonneg ell M κ c
    positivity
  have hρh : 0 ≤ rho1 f M α₀ := rho1_nonneg f M α₀ hα0
  exact ginv_weighted_coercive_M1 hell0 hS hκ hM hell hR1 hR hc hW hWR (periodicGaugeTransform g U) a ha Lam
    (rhoT ell f M α₀) hρ h216 h12 hU' hT' hN.hsm hN.hsmD hN.hgs (rho1 f M α₀) hρh hreg _ hCM hMass ε1 ε2 hε1 hε2 hN.hη
    cP hP A

/-- **W4 at `U`**. -/
theorem w4_M1 (a : ℝ) (ha : 0 < a) (Lam : Set (PeriodicLatticeSite Lu))
    (ε1 ε2 : ℝ) (hε1 : 0 < ε1) (hε2 : 0 < ε2) (hN : W4Num ell M f W a α₀ ε1)
    (cP : ℝ) (hP : PatchCoercive ell M k κ c Lu hell0 S U a Lam cP)
    (A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G)) :
    cwW4 ell M κ c W a (rhoT ell f M α₀) (rho1 f M α₀) ε1 ε2 cP (epsXnum ell W a (rhoT ell f M α₀))
        (CMcStar ell M κ c a (SstarM ell f M α₀))
      * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ :=
  coercive_of_gauge hell0 S a Lam U g _
    (fun A' => w4_M1_gauged hell0 hS hκ hM hell hR1 hR hc hW hWR hroom hLu5 U g A0 hUg hB hη hα0 ha1 hsm4 hsmA hrr a ha Lam
      ε1 ε2 hε1 hε2 hN cP (patchCoercive_gauge hell0 S a Lam U g cP hP) A') A

end main

end AdalyFormal.M1GaugeW4

#print axioms AdalyFormal.M1GaugeW4.hbig_of
#print axioms AdalyFormal.M1GaugeW4.w4_M1_gauged
#print axioms AdalyFormal.M1GaugeW4.w4_M1
