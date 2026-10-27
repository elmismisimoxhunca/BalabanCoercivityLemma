import UA
import AC_SV3a

/-!
# UMA -- the UNIFORM shapes at cube factor `fc` (lane unif_20261016, milestone 7).  NOTHING HERE PROVES THE LEMMA.

Text copies of the `UA` definitions with the class `ClassCoupled ell M 12` replaced by the hybrid class of the AllC lane
`AllC.ClassCoupledH ell M fc 12` (class cubes of side `fc M ℓ^j`, bounds `12 M α₀ (ℓ^j η)^{-n}`), the free bonds `ClassBond ell M fc`,
and the conclusion of `FieldsKU` by `OneGap.FieldsKAtAC` (all patch charts, AllC lane).  `ClassFamUH ell fc` : thresholds `m₁, R₁` and
constants `c, s` before `m, R` (they may depend on `ell`, `fc`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace AdalyFormal.UnifMax

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
def ClassFamUH (ell fc : ℕ) (Cs : Type)
    (Q : ℕ → ℕ → Cs → Prop)
    (P : ∀ (M R k : ℕ) (Lu : PeriodicLatticeExtent), Cs → Tower (scaleUp ell k Lu) → Set (PeriodicLatticeSite Lu) →
      LinkCfg (scaleUp ell k Lu) → ℝ → Prop) : Prop :=
  ∃ m₁ R₁ : ℕ, ∃ c : Cs, ∃ s : ℝ, 0 < s ∧ ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → Q (ell ^ m) R c ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupledH ell (ell ^ m) fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) fc k S e → U e = 1) →
      P (ell ^ m) R k Lu c S Lam U α₀

/-- the uniform shape implies the `ClassFam` shape (same `Q`, `P`). -/
theorem ClassFamUH.toClassFamAC {ell fc : ℕ} {Cs : Type} {Q : ℕ → ℕ → Cs → Prop}
    {P : ∀ (M R k : ℕ) (Lu : PeriodicLatticeExtent), Cs → Tower (scaleUp ell k Lu) → Set (PeriodicLatticeSite Lu) →
      LinkCfg (scaleUp ell k Lu) → ℝ → Prop}
    (h : ClassFamUH ell fc Cs Q P) : AdalyFormal.M2Skel.ClassFamAC ell fc Cs Q P := by
  obtain ⟨m₁, R₁, c, s, hs, hf⟩ := h
  exact ⟨m₁, fun m hm => ⟨R₁, fun R hR => ⟨c, (hf m hm R hR).1, s, hs, (hf m hm R hR).2⟩⟩⟩

/-- **THE RESIDUAL**: region charts (`GChart`) on every admissible ball, with `C` and `s` depending on `ell` only. -/
def BallChartsGUH (fc : ℕ) : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamUH ell fc ℝ (fun _ _ C => 1 ≤ C) (fun M _ k _ C S Lam U α₀ =>
      AdalyFormal.OneGap.BallChartsAtG ell M k S U C α₀ ((ell : ℝ) ^ k)⁻¹)

/-- uniform `BallCharts0` -/
def BallChartsUH (fc : ℕ) : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamUH ell fc ℝ (fun _ _ C => 1 ≤ C) (fun M _ k _ C S Lam U α₀ =>
      AdalyFormal.OneGap.BallChartsAt ell M k S U C α₀ ((ell : ℝ) ^ k)⁻¹)

/-- uniform `FieldsK0` -/
def FieldsKUH (ell fc : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ df m₁ R₁ : ℕ, ∃ K : ℝ, 1 ≤ K ∧ ∃ s : ℝ, 0 < s ∧ ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R →
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    (∀ σ : Fin 3, 13 * (ell ^ m) ≤ Lu σ + 1) →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam → ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupledH ell (ell ^ m) fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : AdalyFormal.Balaban.AdmissibleSubspace.Bond (scaleUp ell k Lu),
      ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) fc k S e → U e = 1) →
    AdalyFormal.OneGap.FieldsKAtAC ell hell a df (ell ^ m) R k Lu K S Lam U α₀

/-- uniform `ClassRightInvCov0` -/
def ClassRightInvCovUH (fc : ℕ) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ∃ m₁ : ℕ, ∃ cW cG : ℝ, 0 ≤ cW ∧ 0 ≤ cG ∧
    ∃ R₁ : ℕ, ∃ s : ℝ, 0 < s ∧ ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R →
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
def ClassRightInvUH (fc : ℕ) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ∃ m₁ : ℕ, ∃ bN : ℝ, 0 < bN ∧
    ∃ R₁ : ℕ, ∃ s : ℝ, 0 < s ∧ ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R →
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
def OpLayerThickUH (fc : ℕ) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ClassFamUH ell fc (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ)
      (fun M R c => 0 < c.1 ∧ (ell : ℝ) ^ 3 * Real.exp (-(c.1 * (R * M))) ≤ 1 / 2 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2.1 ∧
        0 ≤ c.2.2.2.1 ∧ 0 ≤ c.2.2.2.2.1 ∧ 0 ≤ c.2.2.2.2.2)
      (fun M R k Lu c S Lam U α₀ => (∀ σ : Fin 3, 13 * M ≤ Lu σ + 1) → AdalyFormal.M2DLayer.OpLayer ell M R k Lu (by omega) S U a Lam
          c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2)

end AdalyFormal.UnifMax
