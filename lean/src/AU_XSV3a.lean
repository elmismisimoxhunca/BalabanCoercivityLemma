import RI6
import AU_BCG
import AU_OL3
import AU_XBCG
import AC_OG8
import AC_Base

/-!
# AU_XSV3a -- the UNIFORM-in-`fc` field inputs (lane allc_20261016, uniform-in-c route)

Copies of `AC_SV3a.FieldsK0, ClassRightInvCov0, ClassRightInv0, OpLayerThick0` with the thresholds `m1`, `R1` (and, for `ClassRightInv*`, the constants
before `R1`) chosen BEFORE the cube factor `fc >= 10`.  `FieldsK0X` carries one extra conjunct: the `BallChartsAt` instance at the constant `C <= K`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false

namespace AdalyFormal.AllC

open AdalyFormal.M2Skel (ClassFamX)

section d2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK pdist)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.IngredientFamilyR2 (geomOf BIdx bondsLam)
open AdalyFormal.M1Site AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar)
open AdalyFormal.M2Skel (SiteS1 RowBound alpha1)
open AdalyFormal.OneGap12 (AnchorChart12)
open AdalyFormal.OneGap
def FieldsK0X (ell : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ df m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → ∃ K : ℝ, 1 ≤ K ∧ ∃ C : ℝ, 1 ≤ C ∧ C ≤ K ∧ ∃ s : ℝ, 0 < s ∧ ∀ fc : ℕ, 10 ≤ fc →
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    (∀ σ : Fin 3, 13 * (ell ^ m) ≤ Lu σ + 1) →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam → ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupledH ell (ell ^ m) fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : AdalyFormal.Balaban.AdmissibleSubspace.Bond (scaleUp ell k Lu),
      ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) fc k S e → U e = 1) →
    FieldsKAtAC ell hell a df (ell ^ m) R k Lu K S Lam U α₀ ∧
      AdalyFormal.OneGap.BallChartsAt ell (ell ^ m) k S U C α₀ ((ell : ℝ) ^ k)⁻¹
end d2

section d3
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1IMS AdalyFormal.M1GaugeW4 AdalyFormal.TowerLoc
open AdalyFormal.M1Site
open AdalyFormal.M1DStrat (gradWU etaS hext_of_rightinv_cov)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.M2Skel (SiteS1 alpha1)
open AdalyFormal.M2OpLayer
def ClassRightInvCov0X : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → ∃ cW cG : ℝ, 0 ≤ cW ∧ 0 ≤ cG ∧
    ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → ∃ s : ℝ, 0 < s ∧ ∀ fc : ℕ, 10 ≤ fc →
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    (∀ σ : Fin 3, 13 * ell ^ m ≤ Lu σ + 1) →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam → ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupledH ell (ell ^ m) fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) fc k S e → U e = 1) →
    ∀ u : FSp (geomOf ell k S), ∃ x : ↥(bondSupp (geomOf ell k S)),
      (gparams ell k Lu (by omega) S U a Lam).data.Q x = u ∧
      AdalyFormal.M1.wnormSq S ell k (x : BondFnL2 (scaleUp ell k Lu)) ≤ cW * AdalyFormal.W6.nD u ∧
      ∀ ν : Fin 3, gradWU U (x : BondFnL2 (scaleUp ell k Lu)) ν ≤ cG * AdalyFormal.W6.nD u
end d3

section d4
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.IngredientFamilyR2 (geomOf FSp bondSupp diagW massW)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M2Skel (ClassFamAC)
open AdalyFormal.M2OpLayer
def ClassRightInv0X : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → ∃ bN : ℝ, 0 < bN ∧
    ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → ∃ s : ℝ, 0 < s ∧ ∀ fc : ℕ, 10 ≤ fc →
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    (∀ σ : Fin 3, 13 * ell ^ m ≤ Lu σ + 1) →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam → ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupledH ell (ell ^ m) fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) fc k S e → U e = 1) →
    ∀ v : FSp (geomOf ell k S), ∃ g : ↥(bondSupp (geomOf ell k S)),
      (gparams ell k Lu (by omega) S U a Lam).data.Q g = v ∧
      ⟪g, (gparams ell k Lu (by omega) S U a Lam).data.Ginv g⟫
        ≤ bN * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) a p)) v‖ ^ 2
end d4

section d5
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.IngredientFamilyR2 (geomOf FSp bondSupp diagW massW)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M2Skel (ClassFamAC)
open AdalyFormal.M2OpLayer
def OpLayerThick0X : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ClassFamX ell (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ)
      (fun M R c => 0 < c.1 ∧ (ell : ℝ) ^ 3 * Real.exp (-(c.1 * (R * M))) ≤ 1 / 2 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2.1 ∧
        0 ≤ c.2.2.2.1 ∧ 0 ≤ c.2.2.2.2.1 ∧ 0 ≤ c.2.2.2.2.2)
      (fun M R k Lu c S Lam U α₀ => (∀ σ : Fin 3, 13 * M ≤ Lu σ + 1) → AdalyFormal.M2DLayer.OpLayer ell M R k Lu (by omega) S U a Lam
          c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2)
end d5


end AdalyFormal.AllC

#print axioms AdalyFormal.AllC.FieldsK0X
#print axioms AdalyFormal.AllC.ClassRightInvCov0X
#print axioms AdalyFormal.AllC.ClassRightInv0X
#print axioms AdalyFormal.AllC.OpLayerThick0X
