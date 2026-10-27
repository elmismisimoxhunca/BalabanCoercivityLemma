import GW2
import TL9
import TL6b

/-!
# GW3 -- W4 / W5 at `U` from `M1Regular` (M1 gauge lane, 2026-10-14)

Assembly.  Given an `M1Regular` witness `(g, A)` of `U`, the regional tower data of `TL9` (k-free `S*`), lane C's regime discharges
(`GW2`) at `U^g`, lane E `ginv_weighted_coercive_M1` (MI28) is applied at `U^g` with `hMass := massComm_M1` (`CMcStar`) and the
result is transported to `U` by `GW1` (`coercive_of_gauge`).  No `RegTower`, no `TowerClass`, no `hV` is assumed.

Inputs that REMAIN hypotheses: `PatchCoercive` (at `U`), the D-layer bound `hD2` (at `U`), `hb` (at `U`), and the explicit numeric
smallness `W4Num` (no `k`, `U`, `S`, `Lu` in its type).
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

/-- the site constant `ρ_T = (ℓ + 3πℓ²)·ρ₁`. -/
noncomputable def rhoT (ell f M : ℕ) (α₀ : ℝ) : ℝ := ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * rho1 f M α₀

theorem rhoT_nonneg (ell f M : ℕ) (α₀ : ℝ) (h : 0 ≤ α₀) : 0 ≤ rhoT ell f M α₀ := by
  unfold rhoT
  have := rho1_nonneg f M α₀ h
  have := Real.pi_pos
  positivity

/-- `ρ_T ≤ 13 ℓ² ρ₁`. -/
theorem rhoT_le (ell f M : ℕ) (α₀ : ℝ) (h : 0 ≤ α₀) (hell : 1 ≤ ell) :
    rhoT ell f M α₀ ≤ 13 * (ell : ℝ) ^ 2 * rho1 f M α₀ := by
  unfold rhoT
  have h1 := rho1_nonneg f M α₀ h
  have hl : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hp := Real.pi_lt_four
  have : (ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2 ≤ 13 * (ell : ℝ) ^ 2 := by nlinarith [Real.pi_pos]
  exact mul_le_mul_of_nonneg_right this h1

theorem rhoT_smalls (ell f M : ℕ) (α₀ : ℝ) (h : 0 ≤ α₀) (hell : 1 ≤ ell)
    (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 f M α₀ ≤ 1) :
    216 * rhoT ell f M α₀ ^ 2 < 1 ∧ 12 * rhoT ell f M α₀ ≤ 1 := by
  have h0 := rhoT_nonneg ell f M α₀ h
  have h1 := rhoT_le ell f M α₀ h hell
  have h2 : rhoT ell f M α₀ ≤ 13 / 4000000 := by
    have : 13 * (ell : ℝ) ^ 2 * rho1 f M α₀ ≤ 13 / 4000000 := by nlinarith
    linarith
  constructor <;> nlinarith

/-- explicit numeric ingredients of the D-layer chain (no `k`, `U`, `S`, `Lu`). -/
noncomputable def dDnum (ell W : ℕ) : ℝ := Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)
noncomputable def dQnum (ell W : ℕ) (a : ℝ) : ℝ := Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1)

/-- the explicit value of `epsX` for the hat instance: `c = csOf a ρ`, `δD`, `δQ`, `m = 1`, `q = √(max a 1)`. -/
noncomputable def epsXnum (ell W : ℕ) (a ρ : ℝ) : ℝ :=
  (4 / csOf a ρ) * dQnum ell W a + (4 / csOf a ρ) * dDnum ell W * (Real.sqrt (max a 1) / Real.sqrt (csOf a ρ))
    + (Real.sqrt (48 / csOf a ρ) * dDnum ell W + (8 / csOf a ρ) * dDnum ell W ^ 2
        + (4 / csOf a ρ) * 1 * (2 * Real.sqrt (max a 1) * dQnum ell W a + dQnum ell W a ^ 2))
      * (Real.sqrt (max a 1) / csOf a ρ)

/-- **the `k`-free numeric regime of W4/W5**: no `k`, no `U`, no `S`, no `Lu` occurs in its type.  (`ρ_T = rhoT`, `ρ_h = rho1`.) -/
structure W4Num (ell M f W : ℕ) (a α₀ ε1 : ℝ) : Prop where
  hsm : 24 * (dDnum ell W ^ 2 + 1 * dQnum ell W a ^ 2) ≤ csOf a (rhoT ell f M α₀)
  hsmD : 4 * dDnum ell W ^ 2 ≤ csOf a (rhoT ell f M α₀)
  hgs : Real.sqrt (max a 1) * ((1 + 12 * rhoT ell f M α₀) ^ 2 + (512 * rhoT ell f M α₀ ^ 2 + 4704) / a)
        * epsXnum ell W a (rhoT ell f M α₀) < (1 - 12 * rhoT ell f M α₀) ^ 2
  hη : etaC ell W (csOf a (rhoT ell f M α₀)) (rho1 f M α₀) ε1 < 1

end AdalyFormal.M1GaugeW4

#print axioms AdalyFormal.M1GaugeW4.rhoT_smalls
#print axioms AdalyFormal.M1GaugeW4.epsXnum
