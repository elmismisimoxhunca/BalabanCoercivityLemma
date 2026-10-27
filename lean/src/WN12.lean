import WN11
import LV10

/-!
# WN12 -- the non-flat W3 results with `LemIFlat` DISCHARGED

`LemIFlat` is proved in compute/lemi_flat_20261013 (`AdalyFormal.LemIFlat.lemIFlat ell hell a ha :
LemIFlat ell a (CS ell a * KV ell a)`, LV10; oleans plain-copied into deps/lv).  Hence, for every `ell ≥ 2`, `a > 0`:
* **`w3_nonflat`** : lane D's `W3Stmt ell _ a` (Ginv form, non-flat `U` in the M1 regime on the patch);
* **`w3G0_nonflat`** : `W3G0Stmt ell a` (decoupled form `G0`, every `A`);
* **`w3G0At_nonflat`** : the W2 lane's `W3G0At ell L U a cW` for `U` in the M1 regime on every two-stratum patch
  tower of `L`.
No hypothesis other than `2 ≤ ell`, `0 < a` (and, for `w3G0At_nonflat`, the per-patch regime).  No sorry / axiom.
-/
set_option autoImplicit false

namespace AdalyFormal.W3NF

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (BlockClosed)
open AdalyFormal.M1Patch (patchTower W3Stmt)

theorem CSKV_nonneg (ell : ℕ) {a : ℝ} (ha : 0 < a) :
    0 ≤ AdalyFormal.LemIFlat.CS ell a * AdalyFormal.LemIFlat.KV ell a := by
  have h1 : 0 ≤ AdalyFormal.LemIFlat.CS ell a := by unfold AdalyFormal.LemIFlat.CS; positivity
  exact mul_nonneg h1 (AdalyFormal.LemIFlat.KV_nonneg ell a ha.le)

/-- **W3 (lane D's `W3Stmt`) at non-flat `U`, unconditional.** -/
theorem w3_nonflat {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) : W3Stmt ell (by omega) a :=
  w3_nonflat_of_LemI hell ha (CSKV_nonneg ell ha) (AdalyFormal.LemIFlat.lemIFlat ell (by omega) a ha)

/-- **W3 for the decoupled form `G0` at non-flat `U`, unconditional.** -/
theorem w3G0_nonflat {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) : W3G0Stmt ell a :=
  w3G0_nonflat_of_LemI hell ha (CSKV_nonneg ell ha) (AdalyFormal.LemIFlat.lemIFlat ell (by omega) a ha)

/-- **`W3G0At` at non-flat `U` (per-patch M1 regime), unconditional.** -/
theorem w3G0At_nonflat {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (L : PeriodicLatticeExtent) (U : Cfg L) (α₀ : ℝ), 0 < α₀ → α₀ ≤ ρ₀ →
      (∀ (i : ℕ) (Rg : Set (PeriodicLatticeSite L)), BlockClosed (ell ^ (i + 1)) Rg →
        (∀ μ : Fin 3, ell ^ (i + 1) ∣ L μ + 1) →
        AdalyFormal.M1.M1Regular ell 1 1 (i + 1) (patchTower i Rg) α₀ ((ell : ℝ) ^ (i + 1))⁻¹ U) →
      AdalyFormal.M1W2.W3G0At ell L U a cW :=
  w3G0At_of_stmt (by omega) (w3G0_nonflat hell ha)

#print axioms CSKV_nonneg
#print axioms w3_nonflat
#print axioms w3G0_nonflat
#print axioms w3G0At_nonflat

end AdalyFormal.W3NF
