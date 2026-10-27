import OLN

/-!
# OL11 -- the two statements of the operator-layer discharge (lane m2_oplayer_20261015)

* **`ClassRightInv`** : at every printed-class configuration (thick torus `13M ≤ Lu+1`, `Λ ≠ ∅`, `U = 1` off class bonds — the
  only configurations at which OG11 `class_coreK` consumes the operator layer), the bond `Q` has an ENERGY right inverse:
  `∀ v, ∃ g ∈ E₀, Q g = v ∧ ⟪g, G⁻¹ g⟫ ≤ bN ‖√w v‖²`, with `bN > 0` chosen after `m` and BEFORE `R` (and before `k, Lu, α₀, S, Λ, U`).
  This is DH1's premise `hext` (M1: DU1 `hext_of_rightinv` from DR1 `bond_rightinv_M1`, both in ONE global gauge).
* **`OpLayerThick`** : OG10 `Residual.opLayer` with the two premises `(∀ σ, 13M ≤ Lu σ + 1) → Λ.Nonempty →` added in front of
  `OpLayer` (same `ClassFam`, same constant tuple and constraint `Q`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.M2OpLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.IngredientFamilyR2 (geomOf FSp bondSupp diagW massW)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M2Skel (ClassFam)

/-- **the energy right inverse at the printed class** (thick tori, `Λ ≠ ∅`) -/
def ClassRightInv : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → ∃ bN : ℝ, 0 < bN ∧
    ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → ∃ s : ℝ, 0 < s ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    (∀ σ : Fin 3, 13 * ell ^ m ≤ Lu σ + 1) →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam → Lam.Nonempty →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) 12 k S e → U e = 1) →
    ∀ v : FSp (geomOf ell k S), ∃ g : ↥(bondSupp (geomOf ell k S)),
      (gparams ell k Lu (by omega) S U a Lam).data.Q g = v ∧
      ⟪g, (gparams ell k Lu (by omega) S U a Lam).data.Ginv g⟫
        ≤ bN * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) a p)) v‖ ^ 2

/-- **OG10 `Residual.opLayer`, at thick tori and `Λ ≠ ∅`** -/
def OpLayerThick : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ClassFam ell (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ)
      (fun M R c => 0 < c.1 ∧ (ell : ℝ) ^ 3 * Real.exp (-(c.1 * (R * M))) ≤ 1 / 2 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2.1 ∧
        0 ≤ c.2.2.2.1 ∧ 0 ≤ c.2.2.2.2.1 ∧ 0 ≤ c.2.2.2.2.2)
      (fun M R k Lu c S Lam U α₀ => (∀ σ : Fin 3, 13 * M ≤ Lu σ + 1) → Lam.Nonempty →
        AdalyFormal.M2DLayer.OpLayer ell M R k Lu (by omega) S U a Lam
          c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2)

end AdalyFormal.M2OpLayer

#print axioms AdalyFormal.M2OpLayer.ClassRightInv
#print axioms AdalyFormal.M2OpLayer.OpLayerThick
