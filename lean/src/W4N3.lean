import GW9
import W4N2

/-!
# W4N3 -- `w4_M1_final`, `wellDef_M1_final`, `hb_M1_of_small` (lane m1_w4num_20261014)

`GW9.w4_M1_patched` / `wellDef_M1_patched` with the numeric bundles `W4Num`, `QsNum` AND the four linear smallness hypotheses
(`ha1`, `hsm4`, `hsmA`, `hrr`) discharged by ONE threshold `12 M α₀ ≤ aS(ell, a, a₀)`; `W := R*M*ell`, `ε1 := 1/4` (from `w4Num_exists`).
Remaining named inputs: `hD2` with `ε₂' < cwW4` (W5 only) and `hb` (W5 only).
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
open AdalyFormal.M1 (M1Bounds)
open AdalyFormal.M1NonFlat (epsNF PkA thetaN)

/-- the linear smallness threshold replacing `ha1, hsm4, hsmA, hrr`. -/
noncomputable def aLin (ell : ℕ) : ℝ :=
  min 1 (min (1 / (80000000 * (ell : ℝ) ^ 2)) (min (1 / (260000 * (ell : ℝ) ^ 4))
    (AdalyFormal.NonflatJet.r0 / (1040 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) + 1)))))

theorem aLin_pos (ell : ℕ) (hell : 0 < ell) : 0 < aLin ell := by
  unfold aLin
  have := AdalyFormal.NonflatJet.r0_pos
  have hl : (0 : ℝ) < ell := by exact_mod_cast hell
  have : (0 : ℝ) ≤ (SmallnessBridge.Assemble.loopFactorBound ell : ℝ) := Nat.cast_nonneg _
  refine lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))

theorem lin_small (ell M : ℕ) (hell : 0 < ell) (α₀ : ℝ) (hα : 0 ≤ α₀) (ht : (12 : ℝ) * M * α₀ ≤ aLin ell) :
    ((12 : ℕ) : ℝ) * M * α₀ ≤ 1 ∧
    4000000 * (ell : ℝ) ^ 2 * rho1 12 M α₀ ≤ 1 ∧
    (1 + 3 * Real.pi) * rho1 12 M α₀ ≤ 1 / (1000 * (ell : ℝ) ^ 4) ∧
    Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 12 M α₀))
      < AdalyFormal.NonflatJet.r0 := by
  have hl : (0 : ℝ) < ell := by exact_mod_cast hell
  set t : ℝ := (12 : ℝ) * M * α₀ with htdef
  have ht0 : 0 ≤ t := by positivity
  have h1 : t ≤ 1 := le_trans ht (min_le_left _ _)
  have h2 : t ≤ 1 / (80000000 * (ell : ℝ) ^ 2) := le_trans ht (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : t ≤ 1 / (260000 * (ell : ℝ) ^ 4) :=
    le_trans ht (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have h4 : t ≤ AdalyFormal.NonflatJet.r0 / (1040 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) + 1)) :=
    le_trans ht (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hr := rho1_le M α₀ hα
  have hr0 := rho1_nonneg 12 M α₀ hα
  have hp := Real.pi_lt_four
  have hpp := Real.pi_pos
  have hrt : rho1 12 M α₀ ≤ 20 * t := hr
  refine ⟨by push_cast; exact h1, ?_, ?_, ?_⟩
  · have := (le_div_iff₀ (by positivity : (0 : ℝ) < 80000000 * (ell : ℝ) ^ 2)).1 h2
    have e : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M α₀ ≤ 4000000 * (ell : ℝ) ^ 2 * (20 * t) :=
      mul_le_mul_of_nonneg_left hrt (by positivity)
    nlinarith
  · have := (le_div_iff₀ (by positivity : (0 : ℝ) < 260000 * (ell : ℝ) ^ 4)).1 h3
    have e : (1 + 3 * Real.pi) * rho1 12 M α₀ ≤ 13 * (20 * t) := by
      calc (1 + 3 * Real.pi) * rho1 12 M α₀ ≤ 13 * rho1 12 M α₀ := by nlinarith
        _ ≤ 13 * (20 * t) := by linarith
    rw [le_div_iff₀ (by positivity)]
    have e' := mul_le_mul_of_nonneg_right e (by positivity : (0 : ℝ) ≤ 1000 * (ell : ℝ) ^ 4)
    nlinarith
  · set lf : ℝ := (SmallnessBridge.Assemble.loopFactorBound ell : ℝ) with hlf
    have hlf0 : 0 ≤ lf := Nat.cast_nonneg _
    have hr0' := AdalyFormal.NonflatJet.r0_pos
    have h4' := (le_div_iff₀ (by positivity : (0 : ℝ) < 1040 * (lf + 1))).1 h4
    have e : (1 + 3 * Real.pi) * rho1 12 M α₀ ≤ 13 * (20 * t) := by
      calc (1 + 3 * Real.pi) * rho1 12 M α₀ ≤ 13 * rho1 12 M α₀ := by nlinarith
        _ ≤ 13 * (20 * t) := by linarith
    have e2 : lf * ((1 + 3 * Real.pi) * rho1 12 M α₀) ≤ lf * (13 * (20 * t)) :=
      mul_le_mul_of_nonneg_left e hlf0
    have e3 : Real.pi / 2 * (lf * ((1 + 3 * Real.pi) * rho1 12 M α₀)) ≤ 2 * (lf * (13 * (20 * t))) := by
      apply mul_le_mul (by linarith) e2 (by positivity) (by norm_num)
    nlinarith [mul_nonneg hlf0 ht0]

/-- **W4 at `U ∈ M1Regular`, numerics discharged** (`W = R·M·ell`).  Constants `cW, a₀, D, Wmin, ε1, aS` depend on `ell, a` only. -/
theorem w4_M1_final {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
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
      (Lam : Set (PeriodicLatticeSite Lu)) (ε2 : ℝ) (hε2 : 0 < ε2)
      (A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G)),
      cwW4 ell M κ c (R * M * ell) a (rhoT ell 12 M α₀) (rho1 12 M α₀) ε1 ε2
          (cPnf ell (R * M * ell) d a cW α₀ ε1 12 M)
          (epsXnum ell (R * M * ell) a (rhoT ell 12 M α₀)) (CMcStar ell M κ c a (SstarM ell 12 M α₀))
        * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
        ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ := by
  obtain ⟨cW, hcW, a₀, ha₀, D, hD, hDle, hall⟩ := w4_M1_patched hell ha
  obtain ⟨W₀, hW₀, ε1, hε1, a₁, ha₁, hN⟩ := w4Num_exists ell hell a ha
  have hl := aLin_pos ell (by omega)
  refine ⟨cW, hcW, a₀, ha₀, D, hD, hDle, W₀, hW₀, ε1, hε1, min a₀ (min a₁ (aLin ell)),
    lt_min ha₀ (lt_min ha₁ hl), ?_⟩
  intro M R k κ c Lu hell0 S hS hκ hM hR1 hR4 hc hroom d hdD hdM hRW hLu5 U α₀ hreg hα0 hsmall Lam ε2 hε2 A
  have h1 : (12 : ℝ) * M * α₀ ≤ a₀ := le_trans hsmall (min_le_left _ _)
  have h2 : (12 : ℝ) * M * α₀ ≤ a₁ := le_trans hsmall (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : (12 : ℝ) * M * α₀ ≤ aLin ell := le_trans hsmall (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨ha1, hsm4, hsmA, hrr⟩ := lin_small ell M hell0 α₀ hα0.le h3
  obtain ⟨hW, -, hNum⟩ := hN M R hM hRW α₀ hα0.le h2
  exact hall hell0 hS hκ hM hR1 hR4 hc hroom hdD hdM hW le_rfl hLu5 U hreg hα0 h1 ha1 hsm4 hsmA hrr Lam ε1 ε2 hε1 hε2 hNum A

end AdalyFormal.M1W4Num

#print axioms AdalyFormal.M1W4Num.w4_M1_final
