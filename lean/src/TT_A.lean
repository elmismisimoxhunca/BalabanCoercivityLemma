import UA
import AC_SV3a

/-!
# TT_A -- the TOTAL shapes (lane total_20261017).  NOTHING HERE PROVES THE LEMMA.

Text copy of `UnifMax.UMA` (lane unif_20261016) with the cube factor `fc >= 10` QUANTIFIED INSIDE the shape, right after the constants
`m₁, R₁, c, s` and before `m, R` (`ClassFamT`), instead of being a section parameter; and with the extra ball-chart conjunct of the AllC lane's
`AU_XSV3a.FieldsK0X` (constant `C`, `C ≤ K`).  All constants are chosen before `fc`, `m`, `R`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace AdalyFormal.Total

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams LambdaOK2 CoercG8At CoercG8AtWD P428Target8 P428Target8Unif)
open AdalyFormal.IngredientFamilyR2 (geomOf FSp bondSupp diagW massW)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1DStrat (gradWU)
open AdalyFormal.AllC (ClassCoupledH)

/-- **uniform family shape**: thresholds `m₁, R₁` and constants `c, s` before `m, R`. -/
def ClassFamT (ell : ℕ) (Cs : Type)
    (Q : ℕ → ℕ → Cs → Prop)
    (P : ∀ (M R k : ℕ) (Lu : PeriodicLatticeExtent), Cs → Tower (scaleUp ell k Lu) → Set (PeriodicLatticeSite Lu) →
      LinkCfg (scaleUp ell k Lu) → ℝ → Prop) : Prop :=
  ∃ m₁ R₁ : ℕ, ∃ c : Cs, ∃ s : ℝ, 0 < s ∧ ∀ fc : ℕ, 10 ≤ fc → ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → Q (ell ^ m) R c ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupledH ell (ell ^ m) fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) fc k S e → U e = 1) →
      P (ell ^ m) R k Lu c S Lam U α₀

/-- **THE RESIDUAL**: region charts (`GChart`) on every admissible ball, with `C` and `s` depending on `ell` only. -/
def BallChartsGT : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamT ell ℝ (fun _ _ C => 1 ≤ C) (fun M _ k _ C S Lam U α₀ =>
      AdalyFormal.OneGap.BallChartsAtG ell M k S U C α₀ ((ell : ℝ) ^ k)⁻¹)

/-- uniform `BallCharts0` -/
def BallChartsT : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamT ell ℝ (fun _ _ C => 1 ≤ C) (fun M _ k _ C S Lam U α₀ =>
      AdalyFormal.OneGap.BallChartsAt ell M k S U C α₀ ((ell : ℝ) ^ k)⁻¹)

/-- uniform `FieldsK0` -/
def FieldsKT (ell : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ df m₁ R₁ : ℕ, ∃ K : ℝ, 1 ≤ K ∧ ∃ C : ℝ, 1 ≤ C ∧ C ≤ K ∧ ∃ s : ℝ, 0 < s ∧ ∀ fc : ℕ, 10 ≤ fc → ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R →
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    (∀ σ : Fin 3, 13 * (ell ^ m) ≤ Lu σ + 1) →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam → ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupledH ell (ell ^ m) fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : AdalyFormal.Balaban.AdmissibleSubspace.Bond (scaleUp ell k Lu),
      ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) fc k S e → U e = 1) →
    AdalyFormal.OneGap.FieldsKAtAC ell hell a df (ell ^ m) R k Lu K S Lam U α₀ ∧
      AdalyFormal.OneGap.BallChartsAt ell (ell ^ m) k S U C α₀ ((ell : ℝ) ^ k)⁻¹

/-- uniform `ClassRightInvCov0` -/
def ClassRightInvCovT : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ∃ m₁ : ℕ, ∃ cW cG : ℝ, 0 ≤ cW ∧ 0 ≤ cG ∧
    ∃ R₁ : ℕ, ∃ s : ℝ, 0 < s ∧ ∀ fc : ℕ, 10 ≤ fc → ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R →
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    (∀ σ : Fin 3, 13 * ell ^ m ≤ Lu σ + 1) →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam → ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupledH ell (ell ^ m) fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) fc k S e → U e = 1) →
    ∀ u : FSp (geomOf ell k S), ∃ x : ↥(bondSupp (geomOf ell k S)),
      (gparams ell k Lu (by omega) S U a Lam).data.Q x = u ∧
      AdalyFormal.M1.wnormSq S ell k (x : AdalyFormal.Balaban.CovariantOperators.BondFnL2 (scaleUp ell k Lu)) ≤ cW * AdalyFormal.W6.nD u ∧
      ∀ ν : Fin 3, gradWU U (x : AdalyFormal.Balaban.CovariantOperators.BondFnL2 (scaleUp ell k Lu)) ν ≤ cG * AdalyFormal.W6.nD u

/-- uniform `ClassRightInv0` -/
def ClassRightInvT : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ∃ m₁ : ℕ, ∃ bN : ℝ, 0 < bN ∧
    ∃ R₁ : ℕ, ∃ s : ℝ, 0 < s ∧ ∀ fc : ℕ, 10 ≤ fc → ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R →
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    (∀ σ : Fin 3, 13 * ell ^ m ≤ Lu σ + 1) →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam → ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupledH ell (ell ^ m) fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) fc k S e → U e = 1) →
    ∀ v : FSp (geomOf ell k S), ∃ g : ↥(bondSupp (geomOf ell k S)),
      (gparams ell k Lu (by omega) S U a Lam).data.Q g = v ∧
      ⟪g, (gparams ell k Lu (by omega) S U a Lam).data.Ginv g⟫
        ≤ bN * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) a p)) v‖ ^ 2

/-- uniform `OpLayerThick0` -/
def OpLayerThickT : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ClassFamT ell (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ)
      (fun M R c => 0 < c.1 ∧ (ell : ℝ) ^ 3 * Real.exp (-(c.1 * (R * M))) ≤ 1 / 2 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2.1 ∧
        0 ≤ c.2.2.2.1 ∧ 0 ≤ c.2.2.2.2.1 ∧ 0 ≤ c.2.2.2.2.2)
      (fun M R k Lu c S Lam U α₀ => (∀ σ : Fin 3, 13 * M ≤ Lu σ + 1) → AdalyFormal.M2DLayer.OpLayer ell M R k Lu (by omega) S U a Lam
          c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2)

end AdalyFormal.Total
