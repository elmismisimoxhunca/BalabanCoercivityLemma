import RI6
import SVS

/-!
# UA -- the UNIFORM shapes (lane unif_20261016).  NOTHING HERE PROVES THE LEMMA.

`ClassFamU` is `M2Skel.ClassFam` with the constants `c`, `s` and the thresholds `m₁`, `R₁` chosen BEFORE `m` and `R`
(`ClassFam`: `∃ m₁, ∀ m ≥ m₁, ∃ R₁, ∀ R ≥ R₁, ∃ c, Q ∧ ∃ s, …`).

* `BallChartsGU`  : the ball-chart statement `BallChartsAtG` of `OneGap.BallChartsG` (no `Λ ≠ ∅`, as `StrongVariants.BallChartsG0`),
  with the chart constant `C` and the smallness threshold `s` depending on `ell` only.  This is the RESIDUAL of the lane: it is NOT proved.
* `BallChartsU`, `FieldsKU`, `ClassRightInvCovU`, `ClassRightInvU`, `OpLayerThickU` : the uniform shapes of the five field statements of
  `StrongVariants` (`BallCharts0`, `FieldsK0`, `ClassRightInvCov0`, `ClassRightInv0`, `OpLayerThick0`), same content.
* `P428Target8UnifStrong` : `ZT5A.P428Target8Unif` with the r4 conclusion `CoercG8AtWD` (`WellDefG ∧` inequality).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace AdalyFormal.UnifLane

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams LambdaOK2 CoercG8At CoercG8AtWD P428Target8 P428Target8Unif)
open AdalyFormal.IngredientFamilyR2 (geomOf FSp bondSupp diagW massW)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M2Skel (ClassFam)
open AdalyFormal.M1DStrat (gradWU)

/-- **uniform family shape**: thresholds `m₁, R₁` and constants `c, s` before `m, R`. -/
def ClassFamU (ell : ℕ) (Cs : Type)
    (Q : ℕ → ℕ → Cs → Prop)
    (P : ∀ (M R k : ℕ) (Lu : PeriodicLatticeExtent), Cs → Tower (scaleUp ell k Lu) → Set (PeriodicLatticeSite Lu) →
      LinkCfg (scaleUp ell k Lu) → ℝ → Prop) : Prop :=
  ∃ m₁ R₁ : ℕ, ∃ c : Cs, ∃ s : ℝ, 0 < s ∧ ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → Q (ell ^ m) R c ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) 12 k S e → U e = 1) →
      P (ell ^ m) R k Lu c S Lam U α₀

/-- the uniform shape implies the `ClassFam` shape (same `Q`, `P`). -/
theorem ClassFamU.toClassFam {ell : ℕ} {Cs : Type} {Q : ℕ → ℕ → Cs → Prop}
    {P : ∀ (M R k : ℕ) (Lu : PeriodicLatticeExtent), Cs → Tower (scaleUp ell k Lu) → Set (PeriodicLatticeSite Lu) →
      LinkCfg (scaleUp ell k Lu) → ℝ → Prop}
    (h : ClassFamU ell Cs Q P) : ClassFam ell Cs Q P := by
  obtain ⟨m₁, R₁, c, s, hs, hf⟩ := h
  exact ⟨m₁, fun m hm => ⟨R₁, fun R hR => ⟨c, (hf m hm R hR).1, s, hs, (hf m hm R hR).2⟩⟩⟩

/-- **THE RESIDUAL**: region charts (`GChart`) on every admissible ball, with `C` and `s` depending on `ell` only. -/
def BallChartsGU : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamU ell ℝ (fun _ _ C => 1 ≤ C) (fun M _ k _ C S Lam U α₀ =>
      AdalyFormal.OneGap.BallChartsAtG ell M k S U C α₀ ((ell : ℝ) ^ k)⁻¹)

/-- uniform `BallCharts0` -/
def BallChartsU : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamU ell ℝ (fun _ _ C => 1 ≤ C) (fun M _ k _ C S Lam U α₀ =>
      AdalyFormal.OneGap.BallChartsAt ell M k S U C α₀ ((ell : ℝ) ^ k)⁻¹)

/-- the residual implies the (non-uniform) statement `OneGap.BallChartsG` that the existing chain proved (`M2BallCharts.ballChartsG`). -/
theorem BallChartsGU.toBallChartsG (h : BallChartsGU) : AdalyFormal.OneGap.BallChartsG := by
  intro ell hell
  obtain ⟨m₁, R₁, c, s, hs, hf⟩ := h ell hell
  exact ⟨m₁, fun m hm => ⟨R₁, fun R hR => ⟨c, (hf m hm R hR).1, s, hs,
    fun k hk Lu α₀ hα hsα hT S hS Lam hL U hU hloc _ => (hf m hm R hR).2 k hk Lu α₀ hα hsα hT S hS Lam hL U hU hloc⟩⟩⟩

/-- uniform `FieldsK0` -/
def FieldsKU (ell : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ df m₁ R₁ : ℕ, ∃ K : ℝ, 1 ≤ K ∧ ∃ s : ℝ, 0 < s ∧ ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R →
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    (∀ σ : Fin 3, 13 * (ell ^ m) ≤ Lu σ + 1) →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam → ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : AdalyFormal.Balaban.AdmissibleSubspace.Bond (scaleUp ell k Lu),
      ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) 12 k S e → U e = 1) →
    AdalyFormal.OneGap.FieldsKAt ell hell a df (ell ^ m) R k Lu K S Lam U α₀

/-- uniform `ClassRightInvCov0` -/
def ClassRightInvCovU : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ∃ m₁ : ℕ, ∃ cW cG : ℝ, 0 ≤ cW ∧ 0 ≤ cG ∧
    ∃ R₁ : ℕ, ∃ s : ℝ, 0 < s ∧ ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R →
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    (∀ σ : Fin 3, 13 * ell ^ m ≤ Lu σ + 1) →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam → ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) 12 k S e → U e = 1) →
    ∀ u : FSp (geomOf ell k S), ∃ x : ↥(bondSupp (geomOf ell k S)),
      (gparams ell k Lu (by omega) S U a Lam).data.Q x = u ∧
      AdalyFormal.M1.wnormSq S ell k (x : AdalyFormal.Balaban.CovariantOperators.BondFnL2 (scaleUp ell k Lu)) ≤ cW * AdalyFormal.W6.nD u ∧
      ∀ ν : Fin 3, gradWU U (x : AdalyFormal.Balaban.CovariantOperators.BondFnL2 (scaleUp ell k Lu)) ν ≤ cG * AdalyFormal.W6.nD u

/-- uniform `ClassRightInv0` -/
def ClassRightInvU : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ∃ m₁ : ℕ, ∃ bN : ℝ, 0 < bN ∧
    ∃ R₁ : ℕ, ∃ s : ℝ, 0 < s ∧ ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R →
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    (∀ σ : Fin 3, 13 * ell ^ m ≤ Lu σ + 1) →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam → ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) 12 k S e → U e = 1) →
    ∀ v : FSp (geomOf ell k S), ∃ g : ↥(bondSupp (geomOf ell k S)),
      (gparams ell k Lu (by omega) S U a Lam).data.Q g = v ∧
      ⟪g, (gparams ell k Lu (by omega) S U a Lam).data.Ginv g⟫
        ≤ bN * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) a p)) v‖ ^ 2

/-- uniform `OpLayerThick0` -/
def OpLayerThickU : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ClassFamU ell (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ)
      (fun M R c => 0 < c.1 ∧ (ell : ℝ) ^ 3 * Real.exp (-(c.1 * (R * M))) ≤ 1 / 2 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2.1 ∧
        0 ≤ c.2.2.2.1 ∧ 0 ≤ c.2.2.2.2.1 ∧ 0 ≤ c.2.2.2.2.2)
      (fun M R k Lu c S Lam U α₀ => (∀ σ : Fin 3, 13 * M ≤ Lu σ + 1) → AdalyFormal.M2DLayer.OpLayer ell M R k Lu (by omega) S U a Lam
          c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2)

/-- **UNIF-STRONG**: `ZT5A.P428Target8Unif` (`a₀, γ₀` uniform in `M, R` beyond thresholds) with the conclusion `CoercG8AtWD`
(`WellDefG ∧` the printed inequality).  The quantifier prefix is `ZT5A.P428Target8Unif`'s, unchanged. -/
def P428Target8UnifStrong : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          CoercG8AtWD ell (ell ^ m) R k (by omega) a Lu 12 α₀ γ₀

theorem P428Target8UnifStrong.toUnif (h : P428Target8UnifStrong) : P428Target8Unif := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hU⟩ := h ell hell a ha
  exact ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ h1 h2 => (hU m hm R hR k hk Lu α₀ h1 h2).toHead⟩

theorem P428Target8UnifStrong.toStrong (h : P428Target8UnifStrong) : AdalyFormal.StrongVariants.P428Target8Strong := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hU⟩ := h ell hell a ha
  refine ⟨γ₀, hγ, m₁, hm₁, fun m hm => ⟨R₁, fun R hR => ?_⟩⟩
  refine ⟨⟨hell, ⟨m, by omega, rfl⟩, ha⟩, a₀, ha₀, fun k hk Lu α₀ h1 h2 => ?_⟩
  exact hU m hm R hR k hk Lu α₀ h1 (by simpa using h2)

theorem P428Target8UnifStrong.toTarget (h : P428Target8UnifStrong) : P428Target8 := h.toUnif.toTarget

end AdalyFormal.UnifLane
