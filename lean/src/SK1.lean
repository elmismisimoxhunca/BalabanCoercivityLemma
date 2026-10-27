import MA19
import UD7
import UD10
import MR4
import MR5
import WC8d
import MZ5

/-!
# SK1 -- the open inputs of the M2 assembly, as named Props (lane m2_skeleton_20261015)

`ClassFam` is the common quantifier shape of every field: after `ell`, `a` are fixed it follows the headline order
`∃ m₁, ∀ m ≥ m₁, ∃ R₁, ∀ R ≥ R₁, ∃ constants, ∃ s > 0, ∀ k ≥ 1, Lu, α₀ (12 M α₀ ≤ s), TorusOK, Admissible, LambdaOK2, ClassCoupled, <content>`.
Constants and `s` depend on `(ell, a, M, R)` only, never on `k, Lu, α₀, S, Λ, U`.
Every field is asked only for `U` that is TRIVIAL (`= 1`) off the class-constrained bonds `ClassBond` (= `BothIn Ω₀` under the class coverage);
the headline for a general class `U` follows by the r8 locality theorem `InstIneq_congr_class` (SK6 `class_core`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false
namespace AdalyFormal.M2Skel

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp OnLambdaTildeIn TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled OnLambdaT)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M1Site AdalyFormal.M1IMS
open AdalyFormal.M1GaugeW4 (rhoT)
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar)

/-- the class parameter used by every unit-level numeric: `α₁ = ℓ³ · 2 α₀` (as in `unit_floor_class`). -/
noncomputable def alpha1 (ell : ℕ) (α₀ : ℝ) : ℝ := (ell : ℝ) ^ 3 * (2 * α₀)

/-- the common shape of the open inputs. `Cs` = constants chosen after `(M, R)`; `Q` constrains them; `P` is the content. -/
def ClassFam (ell : ℕ) (Cs : Type)
    (Q : ℕ → ℕ → Cs → Prop)
    (P : ∀ (M R k : ℕ) (Lu : PeriodicLatticeExtent), Cs → Tower (scaleUp ell k Lu) → Set (PeriodicLatticeSite Lu) →
      LinkCfg (scaleUp ell k Lu) → ℝ → Prop) : Prop :=
  ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → ∃ c : Cs, Q (ell ^ m) R c ∧ ∃ s : ℝ, 0 < s ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) 12 k S e → U e = 1) →
      P (ell ^ m) R k Lu c S Lam U α₀

/-- the S1 site coercivity of the hatted chain: `cs · ‖f‖²_w ≤ ⟨f, Δ_pA f⟩`.  (`IsUnit LP` and `0 < cs ≤ 1` are NOT part of the field: they are derived,
SK3 `isUnit_LP_of_S1`, `csOf_pos`, `csOf_le_one`.) -/
def SiteS1 {Lf : PeriodicLatticeExtent} (ell k : ℕ) (S : Tower Lf) (U : Cfg Lf) (a cs : ℝ) : Prop :=
  ∀ f, cs * wNormSq (geomOf ell k S) f ≤ ⟪f, DelpA (geomOf ell k S) U a f⟫

/-- the sharp row bound `‖e^{σ} u‖ ≤ γ ‖X u‖`.  (The inverse `Gi` of `X*X` is NOT part of the field: derived, SK3 `gi_of_rowBound`.) -/
def RowBound {Lf : PeriodicLatticeExtent} (ell k : ℕ) (S : Tower Lf) (U : Cfg Lf) (a γ : ℝ) : Prop :=
  ∀ u, ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ≤ γ * ‖Xop (geomOf ell k S) U a u‖

/-- the open inputs of the M2 assembly (one field per genuinely unproved piece; see REMAINING.md). -/
structure RemainingInputs : Prop where
  /-- (F1) S1 site coercivity of the hatted chain at the printed-class `U` (no gauge). -/
  siteS1 : ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ClassFam ell Unit (fun _ _ _ => True) (fun M R k Lu _ S _ U α₀ =>
      SiteS1 ell k S U a (csOf a (rhoT ell 12 M (alpha1 ell α₀))))
  /-- (F2) the sharp row bound at class `U`, with the M1 constant `gamC`/`epsXnum`. -/
  rowBound : ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ClassFam ell Unit (fun _ _ _ => True) (fun M R k Lu _ S _ U α₀ =>
      RowBound ell k S U a (gamC ell a (rhoT ell 12 M (alpha1 ell α₀))
        (AdalyFormal.M1GaugeW4.epsXnum ell (R * M * ell) a (rhoT ell 12 M (alpha1 ell α₀)))))
  /-- (F3) mass commutator at class `U`, with the M1 constant `CMcStar`. -/
  massComm : ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ClassFam ell Unit (fun _ _ _ => True) (fun M R k Lu _ S _ U α₀ =>
      MassComm ell M k 1 5 S U a (CMcStar ell M 1 5 a (SstarM ell 12 M (alpha1 ell α₀))))
  /-- (F4) interface charts (a gauge on each interface patch), from some `d_f` on. -/
  interfaceCharts : ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ∃ df : ℕ,
    ClassFam ell Unit (fun _ _ _ => True) (fun M R k Lu _ S _ U α₀ =>
      ∀ d : ℕ, df ≤ d → d + 64 * ell ^ 2 + 2 ≤ M →
        AdalyFormal.M2Route.InterfaceCharts ell M k d S U ((ell : ℝ) ^ k)⁻¹ ((12 : ℕ) * M * α₀))
  /-- (F5) the operator layer of the D-layer (weighted-ℓ² Combes-Thomas data) with fixed constants. -/
  opLayer : ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ClassFam ell (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ)
      (fun M R c => 0 < c.1 ∧ (ell : ℝ) ^ 3 * Real.exp (-(c.1 * (R * M))) ≤ 1 / 2 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2.1 ∧
        0 ≤ c.2.2.2.1 ∧ 0 ≤ c.2.2.2.2.1 ∧ 0 ≤ c.2.2.2.2.2)
      (fun M R k Lu c S Lam U α₀ => AdalyFormal.M2DLayer.OpLayer ell M R k Lu (by omega) S U a Lam
        c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2)
  /-- (F6) injectivity of `Q_U*` (W6) at class `U`. -/
  qsInj : ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ClassFam ell Unit (fun _ _ _ => True) (fun M R k Lu _ S Lam U α₀ =>
      Function.Injective (gparams ell k Lu (by omega) S U a Lam).data.Qs)

end AdalyFormal.M2Skel
