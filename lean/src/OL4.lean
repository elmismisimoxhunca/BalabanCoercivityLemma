import OL3

/-!
# OL4 -- `hW` at a configuration from the F1/F2 fields (lane m2_oplayer_20261015)

* **`hW_of_fields`** : from `SiteS1` at `cs = csOf a (rhoT ℓ 12 M α)` (F1), `RowBound` with `γ` (F2), `W4Num ℓ M 12 W a α ε1`
  and `216 ρ_T² < 1`:  `wnormSq (W(ι A)) ≤ ℓ² · CWcN ℓ W a cs γ² · wnormSq A` for every `A ∈ E₀`
  (SK3 `hatPack_of_S1`, `gi_of_rowBound`; DC1 `W_wnormSq`; DC1's `CWc` is `CWcN` definitionally).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2OpLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.M1Site AdalyFormal.M1IMS
open AdalyFormal.M1GaugeW4 (rhoT W4Num)
open AdalyFormal.M2Skel (SiteS1 RowBound)

theorem hW_of_fields {ell M R k W : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
    (hS : Admissible ell M R k S) (hW1 : 1 ≤ W) (hell : 2 ≤ ell) (hR : 1 ≤ R) (hM : 1 ≤ M) (hWR : W ≤ R * M * ell)
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a) {α ε1 : ℝ} (hN : W4Num ell M 12 W a α ε1)
    (h216 : 216 * rhoT ell 12 M α ^ 2 < 1) (hS1 : SiteS1 ell k S U a (csOf a (rhoT ell 12 M α)))
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hRB : RowBound ell k S U a γ) (Lam : Set (PeriodicLatticeSite Lu))
    (A : ↥(bondSupp (gparams ell k Lu (by omega) S U a Lam).G)) :
    AdalyFormal.M1.wnormSq (gparams ell k Lu (by omega) S U a Lam).S (gparams ell k Lu (by omega) S U a Lam).ell
        (gparams ell k Lu (by omega) S U a Lam).k
        (Wop (gparams ell k Lu (by omega) S U a Lam).G (gparams ell k Lu (by omega) S U a Lam).U
          (gparams ell k Lu (by omega) S U a Lam).a (iE (gparams ell k Lu (by omega) S U a Lam).G A))
      ≤ ((ell : ℝ) ^ 2 * AdalyFormal.M1DStrat.CWcN ell W a (csOf a (rhoT ell 12 M α)) γ ^ 2)
        * AdalyFormal.M1.wnormSq (gparams ell k Lu (by omega) S U a Lam).S (gparams ell k Lu (by omega) S U a Lam).ell
          (gparams ell k Lu (by omega) S U a Lam).k (A : BondFnL2 (gparams ell k Lu (by omega) S U a Lam).Lf) := by
  have hp := AdalyFormal.M2Skel.hatPack_of_S1 (W := W) (show 1 ≤ ell by omega) ha hN h216 hS1
  obtain ⟨Gi, hG1, -⟩ := AdalyFormal.M2Skel.gi_of_rowBound (geomOf ell k S) (show 1 ≤ (geomOf ell k S).ell by
    show 1 ≤ ell; omega) U a γ hRB
  exact AdalyFormal.M1DStrat.W_wnormSq hS hW1 hell hR hM hWR U a _ hp Gi hG1 γ hγ0 hRB (iE (geomOf ell k S) A)

end AdalyFormal.M2OpLayer

#print axioms AdalyFormal.M2OpLayer.hW_of_fields
