import W4N4

/-!
# W4N5 -- `wellDef_M1_final` (lane m1_w4num_20261014)

`wellDef_M1_final`: `GW9.wellDef_M1_patched` with `W4Num`, `QsNum` and the linear smallness hypotheses discharged by one threshold
`12 M α₀ ≤ aS`.  Remaining named inputs: `hD2` (with `ε₂' < cwW4`) and `hb`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1W4Num

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.M1GaugeW4
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar delStar rho1_nonneg)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneG (gparams GenP.WellDef)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.NonflatJet (r0)
open AdalyFormal.M1 (M1Bounds)
open AdalyFormal.M1NonFlat (epsNF PkA thetaN)

/-- **W5 at `U ∈ M1Regular`, numerics discharged** (`W = R·M·ell`).  Remaining named inputs: `hD2` with `ε₂' < cwW4`, and `hb`. -/
theorem wellDef_M1_final {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ D : ℕ, 12 * ell + 10 ≤ D ∧
    (∀ d, D ≤ d → epsNF ell (PkA a) (thetaN ell) d ≤ cW / 2) ∧
    ∃ Wmin : ℕ, 1 ≤ Wmin ∧ ∃ ε1 : ℝ, 0 < ε1 ∧ ∃ aS : ℝ, 0 < aS ∧
    ∀ {M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
      {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hR1 : 1 ≤ R)
      (hR4 : (c + 4) * κ * ell ≤ R) (hc : 5 ≤ c) (hroom : 17 * ell ≤ R * M) {d : ℕ} (hdD : D ≤ d)
      (hdM : d + 64 * ell ^ 2 ≤ κ * M) (hRW : Wmin ≤ R) (hLu5 : ∀ μ, 5 ≤ Lu μ + 1)
      (U : LinkCfg (scaleUp ell k Lu)) {α₀ : ℝ}
      (hreg : AdalyFormal.M1.M1Regular ell M 12 k S α₀ (((ell : ℝ) ^ k)⁻¹) U) (hα0 : 0 < α₀)
      (hsmall : (12 : ℝ) * M * α₀ ≤ aS)
      (Lam : Set (PeriodicLatticeSite Lu)) (ε2 : ℝ) (hε2 : 0 < ε2) (ε2' : ℝ)
      (hlt : ε2' < cwW4 ell M κ c (R * M * ell) a (rhoT ell 12 M α₀) (rho1 12 M α₀) ε1 ε2
          (cPnf ell (R * M * ell) d a cW α₀ ε1 12 M)
          (epsXnum ell (R * M * ell) a (rhoT ell 12 M α₀)) (CMcStar ell M κ c a (SstarM ell 12 M α₀)))
      (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G),
        |⟪A, (gparams ell k Lu hell0 S U a Lam).data.Delta2 (gparams ell k Lu hell0 S U a Lam).data_laws A⟫|
          ≤ ε2' * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)))
      (hb : Function.Bijective (H0 (gparams ell k Lu hell0 S U a Lam).Lam (gparams ell k Lu hell0 S U a Lam).Q1)),
      GenP.WellDef (gparams ell k Lu hell0 S U a Lam) := by
  obtain ⟨cW, hcW, a₀, ha₀, D, hD, hDle, hall⟩ := wellDef_M1_patched hell ha
  obtain ⟨W₀, hW₀, ε1, hε1, a₁, ha₁, hN⟩ := w4Num_exists ell hell a ha
  obtain ⟨a₂, ha₂, hQ⟩ := qsNum_small_exists ell (by omega)
  have hl := aLin_pos ell (by omega)
  refine ⟨cW, hcW, a₀, ha₀, D, hD, hDle, W₀, hW₀, ε1, hε1, min a₀ (min a₁ (min (aLin ell) a₂)),
    lt_min ha₀ (lt_min ha₁ (lt_min hl ha₂)), ?_⟩
  intro M R k κ c Lu hell0 S hS hκ hM hR1 hR4 hc hroom d hdD hdM hRW hLu5 U α₀ hreg hα0 hsmall Lam ε2 hε2 ε2' hlt hD2 hb
  have h1 : (12 : ℝ) * M * α₀ ≤ a₀ := le_trans hsmall (min_le_left _ _)
  have h2 : (12 : ℝ) * M * α₀ ≤ a₁ := le_trans hsmall (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : (12 : ℝ) * M * α₀ ≤ aLin ell :=
    le_trans hsmall (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have h4 : (12 : ℝ) * M * α₀ ≤ a₂ :=
    le_trans hsmall (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  obtain ⟨ha1, hsm4, hsmA, hrr⟩ := lin_small ell M hell0 α₀ hα0.le h3
  obtain ⟨hW, -, hNum⟩ := hN M R hM hRW α₀ hα0.le h2
  exact hall hell0 hS hκ hM hR1 hR4 hc hroom hdD hdM hW le_rfl hLu5 U hreg hα0 h1 ha1 hsm4 hsmA hrr Lam ε1 ε2 hε1 hε2 hNum
    (hQ M α₀ hα0.le h4) ε2' hlt hD2 hb

end AdalyFormal.M1W4Num

#print axioms AdalyFormal.M1W4Num.wellDef_M1_final
