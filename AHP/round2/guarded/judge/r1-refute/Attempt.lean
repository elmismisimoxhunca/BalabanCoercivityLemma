import DrEquiv
import GdR6b

/-!
Round-2 statement pin, not a solution of either open direction.
The selector assembly and target definitions below are verbatim copies from
D1Lit, D2Cons, GdR5a and DrEquiv, in a fresh namespace. Their remaining
ingredients are the actual frozen lattice definitions imported by DrEquiv.
No AHP module, abstract replacement operator, or additional class premise is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.Round2.Guarded.Pin

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-! Verbatim operative declarations from D1Lit.lean:29-101. -/
abbrev PlaqSel : Type := ∀ (L : PeriodicLatticeExtent), TowerGeom L → Set (PeriodicLatticePlaquette L)

def selIn : PlaqSel := fun _ G => plaqIn G.Om0

def selAll : PlaqSel := fun _ _ => Set.univ

section Selectors
variable (sD sJ : PlaqSel)

noncomputable def DeltaS {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  AdalyFormal.StatementLaneR6.deltaKLocCLM U (sD L G)

noncomputable def DpiFullS {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (a : ℝ) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  (ContinuousLinearMap.adjoint (Wop G U a)).comp ((DeltaS sD G U).comp (Wop G U a))

theorem DpiFullS_symm {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (a : ℝ) (x y : BondFnL2 L) :
    ⟪DpiFullS sD G U a x, y⟫ = ⟪x, DpiFullS sD G U a y⟫ := by
  simp only [DpiFullS, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  exact AdalyFormal.StatementLaneR6.deltaKLocCLM_symm U _ _ _

section Ops
variable (P : IngrBParams)

noncomputable def JfS : BondFnL2 (scaleUp P.ell P.k P.Lu) :=
  WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1 (sJ _ P.G) P.U b))

noncomputable def dataS : BaseDataS ↥(bondSupp P.G) (SiteL2 (scaleUp P.ell P.k P.Lu)) (FSp P.G) :=
  { baseData P.G P.U P.a P.sector (JfS sJ P) with
    Dpi := (pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G)) }

theorem dataS_laws : (dataS sD sJ P).Laws := by
  refine ⟨fun x y => ?_, P.data_laws.C2_quad⟩
  show ⟪((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) x, y⟫ = ⟪x, ((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) y⟫
  simp only [ContinuousLinearMap.comp_apply]
  rw [pE_inner_left, pE_inner_right]
  exact DpiFullS_symm sD P.G P.U P.a _ _

noncomputable def G1invS : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G) :=
  Classical.choose ((dataS sD sJ P).exists_G1inv (dataS_laws sD sJ P))

noncomputable def H1inS : BondFnL2 P.Lu →L[ℝ] BondFnL2 (scaleUp P.ell P.k P.Lu) :=
  (iE P.G).comp (((dataS sD sJ P).H1 (G1invS sD sJ P)).comp (ContinuousLinearMap.adjoint P.tau))

end Ops

namespace GenS
variable (P : IngrBParams)

noncomputable def NmatS : FSp P.G →L[ℝ] FSp P.G :=
  ((dataS sD sJ P).Q.comp ((dataS sD sJ P).G1 (G1invS sD sJ P))).comp (dataS sD sJ P).Qs

noncomputable def firstTermS (B : BondFnL2 P.Lu) : ℝ :=
  P.eta * ⟪ContinuousLinearMap.adjoint P.tau B, Ring.inverse (NmatS sD sJ P) (ContinuousLinearMap.adjoint P.tau B)⟫

noncomputable def genFormS (B : BondFnL2 P.Lu) : ℝ :=
  firstTermS sD sJ P B - P.a * ⟪B, B⟫ - 2 * ⟪H1inS sD sJ P (P.D2in B), JfS sJ P⟫
end GenS

def InstIneqS (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) : Prop :=
  ∀ (Bt : Bond Lu → SuTwo), OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
    γ₀ * bondEnergy Bt ≤
      GenS.genFormS sD sJ (gparams ell k Lu hell S U a Lam)
        (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt))

end Selectors

/-! Verbatim definitions from D2Cons.lean:56-76. -/
def InstIneqSG (sD sJ : PlaqSel) (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) : Prop :=
  IsUnit (dataS sD sJ (gparams ell k Lu hell S U a Lam)).Ginv → InstIneqS sD sJ ell k hell a Lu γ₀ S Lam U

def CoercG8AtSG (sD sJ : PlaqSel) (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneqSG sD sJ ell k hell a Lu γ₀ S Lam U

def P428Target8SG (sD sJ : PlaqSel) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * (ell ^ m : ℕ) * α₀ ≤ a₀ →
          CoercG8AtSG sD sJ ell (ell ^ m) R k (by omega) a Lu 12 α₀ γ₀

/-! Verbatim definition from GdR5a.lean:54-63. -/
def GuardResidualT (sD sJ : PlaqSel) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
        TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
        (∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt) →
        IsUnit (dataS sD sJ (gparams ell k Lu (by omega) S U a Lam)).Ginv →
        IsUnit (G1invS sD sJ (gparams ell k Lu (by omega) S U a Lam))

/-! Verbatim definitions from DrEquiv.lean:35-46, 53-57, 99. -/
def GShape (C : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell) (_ : Tower (scaleUp ell k Lu))
    (_ : LinkCfg (scaleUp ell k Lu)) (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
        TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
        (∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt) →
        IsUnit (dataS selAll selAll (gparams ell k Lu (by omega) S U a Lam)).Ginv →
        C ell k Lu (by omega) S U a Lam

def CPen : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell) (_ : Tower (scaleUp ell k Lu))
    (_ : LinkCfg (scaleUp ell k Lu)) (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop :=
  fun ell k Lu h S U a Lam =>
    IsUnit ((dataS selAll selAll (gparams ell k Lu h S U a Lam)).Ginv -
      (dataS selIn selIn (gparams ell k Lu h S U a Lam)).Delta2 (dataS_laws selIn selIn (gparams ell k Lu h S U a Lam)))

def GuardPencilT : Prop := GShape CPen

/-! The only open targets. These definitions assert no proof of their bodies. -/
def GoalPos1 : Prop := GuardPencilT
def GoalNeg1 : Prop := ¬ GoalPos1

def GoalPos2 : Prop := P428Target8SG selAll selAll
def GoalNeg2 : Prop := ¬ GoalPos2

/-! Identity checks, not additional research goals. -/
theorem assembly_pin (sD sJ : PlaqSel) (P : IngrBParams) :
    dataS sD sJ P = AdalyFormal.D1Literal.dataS sD sJ P := rfl

theorem corrected_pin (sD sJ : PlaqSel) (P : IngrBParams) :
    G1invS sD sJ P = AdalyFormal.D1Literal.G1invS sD sJ P := rfl

theorem form_pin (sD sJ : PlaqSel) (P : IngrBParams) (B : BondFnL2 P.Lu) :
    GenS.genFormS sD sJ P B = AdalyFormal.D1Literal.GenS.genFormS sD sJ P B := rfl

theorem goalPos1_pin : GoalPos1 = AdalyFormal.D1Residual.GuardPencilT := rfl

theorem goalPos2_pin : GoalPos2 =
    AdalyFormal.D1Literal.P428Target8SG AdalyFormal.D1Literal.selAll AdalyFormal.D1Literal.selAll := rfl

theorem residual_pin : GuardResidualT selAll selAll =
    AdalyFormal.D1Guarded.GuardResidualT AdalyFormal.D1Literal.selAll AdalyFormal.D1Literal.selAll := rfl

theorem goalPos2_iff_goalPos1 : GoalPos2 ↔ GoalPos1 := by
  exact AdalyFormal.D1Residual.P428Target8SG_iff_pencilT

theorem goalNeg1_iff_goalNeg2 : GoalNeg1 ↔ GoalNeg2 :=
  not_congr goalPos2_iff_goalPos1.symm

/-!
An explicit sufficient certificate for GoalNeg1, with the cofinal quantifiers
visible. R is chosen BEFORE a₀. There is no path, flatness, PSD, or prescribed
small torus assumption. This certificate itself is not proved here.
-/
def CofinalPencilFailure : Prop :=
  ∃ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a ∧
    ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ 1 ≤ m ∧
      ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧
        ∀ a₀ : ℝ, 0 < a₀ →
          ∃ (k : ℕ) (_ : 1 ≤ k) (Lu : PeriodicLatticeExtent) (α₀ : ℝ)
            (_ : 0 < α₀) (_ : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀)
            (_ : TorusOK ell (ell ^ m) Lu)
            (S : Tower (scaleUp ell k Lu)) (_ : Admissible ell (ell ^ m) R k S)
            (Lam : Set (PeriodicLatticeSite Lu)) (_ : LambdaOK2 ell (ell ^ m) R k S Lam)
            (U : LinkCfg (scaleUp ell k Lu))
            (_ : ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
            (Bt : Bond Lu → SuTwo),
            OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧
            IsUnit (dataS selAll selAll (gparams ell k Lu (by omega) S U a Lam)).Ginv ∧
            ¬ CPen ell k Lu (by omega) S U a Lam

theorem cofinalPencilFailure_implies_goalNeg1 (h : CofinalPencilFailure) : GoalNeg1 := by
  intro hp
  obtain ⟨ell, hell, a, ha, hmfail⟩ := h
  obtain ⟨m₀, _, hmpos⟩ := hp ell hell a ha
  obtain ⟨m, hm, _, hRfail⟩ := hmfail m₀
  obtain ⟨R₀, hRpos⟩ := hmpos m hm
  obtain ⟨R, hR, hafail⟩ := hRfail R₀
  obtain ⟨a₀, ha₀, hapos⟩ := hRpos R hR
  obtain ⟨k, hk, Lu, α₀, hα, hsmall, hT, S, hS, Lam, hL, U, hU,
    Bt, hBt1, hBt2, hE, hu, hnu⟩ := hafail a₀ ha₀
  exact hnu (hapos k hk Lu α₀ hα hsmall hT S hS Lam hL U hU ⟨Bt, hBt1, hBt2, hE⟩ hu)

theorem cofinalPencilFailure_implies_goalNeg2 (h : CofinalPencilFailure) : GoalNeg2 :=
  goalNeg1_iff_goalNeg2.mp (cofinalPencilFailure_implies_goalNeg1 h)

#check GoalPos1
#check GoalNeg1
#check GoalPos2
#check GoalNeg2
#check CofinalPencilFailure
#check AdalyFormal.D1Residual.P428Target8SG_iff_pencilT
#check AdalyFormal.D1Residual.residualT_iff_pencilT
#check AdalyFormal.D1Residual.G1inv_lit_eq_pencil

#print axioms GoalPos1
#print axioms GoalNeg1
#print axioms GoalPos2
#print axioms GoalNeg2
#print axioms CofinalPencilFailure
#print axioms DpiFullS_symm
#print axioms dataS_laws
#print axioms assembly_pin
#print axioms corrected_pin
#print axioms form_pin
#print axioms goalPos1_pin
#print axioms goalPos2_pin
#print axioms residual_pin
#print axioms goalPos2_iff_goalPos1
#print axioms goalNeg1_iff_goalNeg2
#print axioms cofinalPencilFailure_implies_goalNeg1
#print axioms cofinalPencilFailure_implies_goalNeg2

end AdalyFormal.Round2.Guarded.Pin

/-!
Partial results only. No negative goal is proved below. The small numerical
candidate has not been lifted to the pinned cofinal class.
These lemmas use the copied concrete assembly, not freely chosen matrices.
-/
namespace AdalyFormal.Round2.Guarded.RefuteR1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- Exact polarization of the actual localized correction. -/
theorem second_jet_pairing (P : IngrBParams) (x y : ↥(bondSupp P.G)) :
    ⟪x, (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) y⟫ =
      ⟪(dataS selIn selIn P).H ((dataS selIn selIn P).C2 (x + y)), (dataS selIn selIn P).J⟫ -
      ⟪(dataS selIn selIn P).H ((dataS selIn selIn P).C2 x), (dataS selIn selIn P).J⟫ -
      ⟪(dataS selIn selIn P).H ((dataS selIn selIn P).C2 y), (dataS selIn selIn P).J⟫ := by
  let D := dataS selIn selIn P
  let K := D.Delta2 (dataS_laws selIn selIn P)
  obtain ⟨hs, hf⟩ := D.Delta2_spec (dataS_laws selIn selIn P)
  have hxy := hf (x + y)
  have hx := hf x
  have hy := hf y
  have hsym : ⟪y, K x⟫ = ⟪x, K y⟫ := by
    calc ⟪y, K x⟫ = ⟪K x, y⟫ := real_inner_comm _ _
         _ = ⟪x, K y⟫ := hs x y
  change ⟪x, K y⟫ = _
  change ⟪x + y, K (x + y)⟫ = _ at hxy
  change ⟪x, K x⟫ = _ at hx
  change ⟪y, K y⟫ = _ at hy
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsym] at hxy
  dsimp only [D] at hx hy hxy
  linarith

/-- The complete kernel equation, with no truncated subspace or numerical tolerance. -/
theorem pencil_failure_iff_kernel
    (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) :
    let P := gparams ell k Lu hell S U a Lam
    ¬ CPen ell k Lu hell S U a Lam ↔
      ∃ v : ↥(bondSupp P.G), v ≠ 0 ∧
        (dataS selAll selAll P).Ginv v =
          (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) v := by
  dsimp only
  let P := gparams ell k Lu hell S U a Lam
  let M := (dataS selAll selAll P).Ginv
  let D := (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
  change ¬ IsUnit (M - D) ↔ ∃ v, v ≠ 0 ∧ M v = D v
  have hunit : IsUnit (M - D) ↔ Function.Injective (M - D) := by
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, (LinearMap.injective_iff_surjective (f := (M - D).toLinearMap)).mp h⟩
  rw [hunit, injective_iff_map_eq_zero]
  push Not
  constructor
  · rintro ⟨v, hv, hn⟩
    exact ⟨v, hn, sub_eq_zero.mp hv⟩
  · rintro ⟨v, hn, hv⟩
    exact ⟨v, sub_eq_zero.mpr hv, hn⟩

/-- Source-specific matrix-free criterion: all pairings of the genuine second jet,
not a surrogate correction, must satisfy the singular-pencil equation. -/
theorem pencil_failure_iff_second_jet
    (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) :
    let P := gparams ell k Lu hell S U a Lam
    ¬ CPen ell k Lu hell S U a Lam ↔
      ∃ v : ↥(bondSupp P.G), v ≠ 0 ∧ ∀ x : ↥(bondSupp P.G),
        ⟪x, (dataS selAll selAll P).Ginv v⟫ =
          ⟪(dataS selIn selIn P).H ((dataS selIn selIn P).C2 (x + v)), (dataS selIn selIn P).J⟫ -
          ⟪(dataS selIn selIn P).H ((dataS selIn selIn P).C2 x), (dataS selIn selIn P).J⟫ -
          ⟪(dataS selIn selIn P).H ((dataS selIn selIn P).C2 v), (dataS selIn selIn P).J⟫ := by
  dsimp only
  have hiff := pencil_failure_iff_kernel ell k Lu hell S U a Lam
  dsimp only at hiff
  rw [hiff]
  constructor
  · rintro ⟨v, hv, heq⟩
    refine ⟨v, hv, fun x => ?_⟩
    exact (congrArg (fun z => ⟪x, z⟫) heq).trans
      (second_jet_pairing (gparams ell k Lu hell S U a Lam) x v)
  · rintro ⟨v, hv, hpair⟩
    refine ⟨v, hv, ext_inner_left ℝ (fun x => ?_)⟩
    exact (hpair x).trans
      (second_jet_pairing (gparams ell k Lu hell S U a Lam) x v).symm

/-- A guarded failure needs an actual nonzero local second-jet/source coupling. -/
theorem guarded_failure_forces_second_jet
    (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hu : IsUnit (dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ginv)
    (hfail : ¬ CPen ell k Lu hell S U a Lam) :
    let P := gparams ell k Lu hell S U a Lam
    (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) ≠ 0 ∧
      ∃ x : ↥(bondSupp P.G),
        ⟪(dataS selIn selIn P).H ((dataS selIn selIn P).C2 x), (dataS selIn selIn P).J⟫ ≠ 0 := by
  dsimp only
  let P := gparams ell k Lu hell S U a Lam
  let D := dataS selIn selIn P
  have hn : D.Delta2 (dataS_laws selIn selIn P) ≠ 0 := by
    intro hz
    apply hfail
    change IsUnit ((dataS selAll selAll P).Ginv - D.Delta2 _)
    rw [hz, sub_zero]
    exact hu
  refine ⟨hn, ?_⟩
  by_contra h
  push Not at h
  apply hn
  obtain ⟨hs, hf⟩ := D.Delta2_spec (dataS_laws selIn selIn P)
  refine symm_unique hs (fun x y => by simp) (fun x => ?_)
  rw [hf x]
  simp only [D, P] at h ⊢
  rw [h x]
  simp

/-- Excludes every base-point-flat configuration, not merely the old twist path. -/
theorem guarded_failure_forces_nonflat
    (ell M R k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S)
    (h3 : 3 ≤ R * M) (U : LinkCfg (scaleUp ell k Lu))
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hu : IsUnit (dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ginv)
    (hfail : ¬ CPen ell k Lu hell S U a Lam) :
    ∃ e : Bond (scaleUp ell k Lu), e.1 ∈ S.Om 0 ∧ U e ≠ 1 := by
  by_contra h
  push Not at h
  let P := gparams ell k Lu hell S U a Lam
  have hid := AdalyFormal.D1Guarded.G1invS_eq_Ginv_base
    AdalyFormal.D1Literal.selIn P AdalyFormal.D1Literal.selIn hS hell h3 h
  have hspec := (dataS selIn selIn P).G1inv_unique
    (AdalyFormal.D1Literal.G1invS_spec selIn selIn P)
    ((dataS selIn selIn P).isG1inv_sub (dataS_laws selIn selIn P))
  change G1invS selIn selIn P = (dataS selIn selIn P).Ginv at hid
  change G1invS selIn selIn P = (dataS selIn selIn P).Ginv -
    (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) at hspec
  rw [hid] at hspec
  have hz : (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) = 0 :=
    sub_eq_self.mp hspec.symm
  exact (guarded_failure_forces_second_jet ell k Lu hell S U a Lam hu hfail).1 hz

#print axioms second_jet_pairing
#print axioms pencil_failure_iff_kernel
#print axioms pencil_failure_iff_second_jet
#print axioms guarded_failure_forces_second_jet
#print axioms guarded_failure_forces_nonflat
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.Delta2_spec
#print axioms AdalyFormal.IngredientFamilyR2.symm_unique
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.G1inv_unique
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.isG1inv_sub
#print axioms AdalyFormal.D1Literal.G1invS_spec
#print axioms AdalyFormal.D1Guarded.G1invS_eq_Ginv_base

end AdalyFormal.Round2.Guarded.RefuteR1
