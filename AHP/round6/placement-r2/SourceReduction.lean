import DrEquiv

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
Round-3 support appendix. Everything above is the complete round-2 pin verbatim,
including its namespace and the two equivalent positive/negative goal pairs.
The five definitions below are copied verbatim from the second positive attempt,
with its namespace retained so its existing proof bodies can be reused directly.
They describe the boundary-response route, NOT additional completion targets.
No boundary-response implication is assumed and no open proposition is proved.
-/
namespace AdalyFormal.Round2.Guarded.R2Prove

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def response (Θ B : E →L[ℝ] E) : Θ.range →L[ℝ] Θ.range :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => ⟨(y : E) + Θ (Ring.inverse B y),
        Θ.range.add_mem y.property ⟨Ring.inverse B y, rfl⟩⟩
      map_add' := fun x y => by
        apply Subtype.ext
        simp only [Submodule.coe_add, map_add]
        abel
      map_smul' := fun c x => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, map_smul, smul_add, RingHom.id_apply] }

end Algebra

section Concrete
variable (P : IngrBParams)

noncomputable def boundaryShift : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G) :=
  (dataS selAll selAll P).Ginv - (dataS selIn selIn P).Ginv

noncomputable def localCorrected : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G) :=
  (dataS selIn selIn P).Ginv -
    (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)

end Concrete

def CBoundaryResponse : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell)
    (_ : Tower (scaleUp ell k Lu)) (_ : LinkCfg (scaleUp ell k Lu))
    (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop :=
  fun ell k Lu h S U a Lam =>
    let P := gparams ell k Lu h S U a Lam
    IsUnit (response (boundaryShift P) (localCorrected P))

def CNoBoundaryReturn : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell)
    (_ : Tower (scaleUp ell k Lu)) (_ : LinkCfg (scaleUp ell k Lu))
    (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop :=
  fun ell k Lu h S U a Lam =>
    let P := gparams ell k Lu h S U a Lam
    ∀ y : (boundaryShift P).range,
      boundaryShift P (Ring.inverse (localCorrected P)
        ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
          (Ring.inverse (dataS selIn selIn P).Ginv y))) = 0

#check response
#check boundaryShift
#check localCorrected
#check CBoundaryResponse
#check CNoBoundaryReturn
#check (GShape CBoundaryResponse : Prop)
#check (GShape CNoBoundaryReturn : Prop)

#print axioms response
#print axioms boundaryShift
#print axioms localCorrected
#print axioms CBoundaryResponse
#print axioms CNoBoundaryReturn

end AdalyFormal.Round2.Guarded.R2Prove

/-! Dependency records for every remaining declaration of the copied pin. -/
#print axioms AdalyFormal.Round2.Guarded.Pin.PlaqSel
#print axioms AdalyFormal.Round2.Guarded.Pin.selIn
#print axioms AdalyFormal.Round2.Guarded.Pin.selAll
#print axioms AdalyFormal.Round2.Guarded.Pin.DeltaS
#print axioms AdalyFormal.Round2.Guarded.Pin.DpiFullS
#print axioms AdalyFormal.Round2.Guarded.Pin.JfS
#print axioms AdalyFormal.Round2.Guarded.Pin.dataS
#print axioms AdalyFormal.Round2.Guarded.Pin.G1invS
#print axioms AdalyFormal.Round2.Guarded.Pin.H1inS
#print axioms AdalyFormal.Round2.Guarded.Pin.GenS.NmatS
#print axioms AdalyFormal.Round2.Guarded.Pin.GenS.firstTermS
#print axioms AdalyFormal.Round2.Guarded.Pin.GenS.genFormS
#print axioms AdalyFormal.Round2.Guarded.Pin.InstIneqS
#print axioms AdalyFormal.Round2.Guarded.Pin.InstIneqSG
#print axioms AdalyFormal.Round2.Guarded.Pin.CoercG8AtSG
#print axioms AdalyFormal.Round2.Guarded.Pin.P428Target8SG
#print axioms AdalyFormal.Round2.Guarded.Pin.GuardResidualT
#print axioms AdalyFormal.Round2.Guarded.Pin.GShape
#print axioms AdalyFormal.Round2.Guarded.Pin.CPen
#print axioms AdalyFormal.Round2.Guarded.Pin.GuardPencilT

namespace AdalyFormal.Round6.Guarded.PlacementR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

open Classical in
/-- Only the source on carrier bonds outside level zero can contribute.
This is a field, not a replacement for the correction operator. -/
noncomputable def activeField {L : PeriodicLatticeExtent} (G : TowerGeom L)
    (J : BondFnL2 L) : BondFnL2 L :=
  WithLp.toLp 2 (fun b => if b ∈ bondsOm0 G ∧ b ∉ bondsLam G 0 then J.ofLp b else 0)

noncomputable def activeSource (sJ : PlaqSel) (P : IngrBParams) : ↥(bondSupp P.G) :=
  pE P.G (activeField P.G (JfS sJ P))

/-- Exact source decomposition, without any unit or smallness premise. -/
theorem source_split (sD sJ : PlaqSel) (P : IngrBParams) :
    (dataS sD sJ P).J =
      (dataS sD sJ P).Qs (AdalyFormal.D1Guarded.level0 P.G (JfS sJ P)) + activeSource sJ P := by
  classical
  apply ext_inner_right ℝ
  intro A
  have h1 : ⟪(dataS sD sJ P).J, A⟫ = ⟪JfS sJ P, iE P.G A⟫ := pE_inner_left P.G A _
  have h2 : ⟪(dataS sD sJ P).Qs (AdalyFormal.D1Guarded.level0 P.G (JfS sJ P)), A⟫ =
      ⟪(bondSectorOf P.G P.U).Qfull (iE P.G A), AdalyFormal.D1Guarded.level0 P.G (JfS sJ P)⟫ := by
    show ⟪ContinuousLinearMap.adjoint ((bondSectorOf P.G P.U).Qfull.comp (iE P.G)) _, A⟫ = _
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
    rfl
  rw [inner_add_left, h1, h2, AdalyFormal.D1Guarded.inner_Qfull_level0]
  unfold activeSource
  rw [pE_inner_left]
  simp only [activeField, PiLp.inner_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hb : b ∈ bondsLam P.G 0
  · simp [hb, real_inner_comm]
  · by_cases hb0 : b ∈ bondsOm0 P.G
    · simp [hb, hb0]
    · have hz : (iE P.G A).ofLp b = 0 := A.2 b hb0
      simp [hb, hb0, hz]

/-- The genuine correction pairs only with activeSource. Boundary source
components do not contribute directly, even in a hybrid curved background.
The operators H and C2 still depend on the ENTIRE background. -/
theorem correction_uses_active_source (sD sJ : PlaqSel) (P : IngrBParams)
    (v : ↥(bondSupp P.G)) :
    ⟪v, (dataS sD sJ P).Delta2 (dataS_laws sD sJ P) v⟫ =
      2 * ⟪(dataS sD sJ P).H ((dataS sD sJ P).C2 v), activeSource sJ P⟫ := by
  rw [((dataS sD sJ P).Delta2_spec (dataS_laws sD sJ P)).2 v,
    source_split sD sJ P, inner_add_right]
  have hz := AdalyFormal.D1Guarded.inner_H_Qs (dataS sD sJ P)
    (AdalyFormal.D1Guarded.level0 P.G (JfS sJ P)) ((dataS sD sJ P).C2 v)
    (AdalyFormal.D1Guarded.C2full_level0_inner P.G P.U _ _)
  rw [hz, zero_add]

/-- Nonzero correction requires an actual source on a non-level-zero
carrier bond. No conclusion about the sign follows from this necessity. -/
theorem nonzero_correction_requires_active_source (sD sJ : PlaqSel) (P : IngrBParams)
    (hD : (dataS sD sJ P).Delta2 (dataS_laws sD sJ P) ≠ 0) : activeSource sJ P ≠ 0 := by
  intro hJ
  apply hD
  exact symm_unique ((dataS sD sJ P).Delta2_spec (dataS_laws sD sJ P)).1
    (fun x y => by simp) (fun v => by rw [correction_uses_active_source, hJ]; simp)


#print axioms activeField
#print axioms activeSource
#print axioms source_split
#print axioms correction_uses_active_source
#print axioms nonzero_correction_requires_active_source

/-! Source locality at the actual positive-level constraints. This proves
an exact cancellation identity, NOT equality of the two corrections. -/
open AdalyFormal.IngredientFamily (FnuMuLoc JfieldLoc)
open AdalyFormal.Balaban.DeltaPrime (imHolonomy)
open AdalyFormal.Balaban.SourceJ (DstarDir)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

/-- The localized plaquette source reads only the three base sites of its
four boundary links. -/
theorem FnuMuLoc_congr_region {L : PeriodicLatticeExtent}
    (U V : LinkCfg L) (P : Set (PeriodicLatticePlaquette L))
    (Om : Set (PeriodicLatticeSite L)) (hU : ∀ e : Bond L, e.1 ∈ Om → U e = V e)
    (ν μ : Fin 3) (y : PeriodicLatticeSite L) (h0 : y ∈ Om)
    (h1 : periodicLatticeShift y ν ∈ Om) (h2 : periodicLatticeShift y μ ∈ Om) :
    FnuMuLoc P U ν μ y = FnuMuLoc P V ν μ y := by
  have hc : ∀ p : PeriodicLatticePlaquette L, p.1 = y →
      (p.2.1.1 = ν ∧ p.2.1.2 = μ ∨ p.2.1.1 = μ ∧ p.2.1.2 = ν) →
      imHolonomy U p = imHolonomy V p := by
    intro p hp hdir
    apply AdalyFormal.StatementLaneR6.imHolonomy_congr
    intro e he
    apply hU
    rcases (AdalyFormal.StatementLaneR6.edge_mem p e).mp he with rfl | rfl | rfl | rfl
    · simpa only [hp] using h0
    · rcases hdir with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [hp, a] <;> assumption
    · rcases hdir with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [hp, b] <;> assumption
    · simpa only [hp] using h0
  unfold FnuMuLoc
  split_ifs with hlt hmem hgt hmem'
  · rw [hc (y, ⟨(ν, μ), hlt⟩) rfl (Or.inl ⟨rfl, rfl⟩)]
  · rfl
  · rw [hc (y, ⟨(μ, ν), hgt⟩) rfl (Or.inr ⟨rfl, rfl⟩)]
  · rfl
  · rfl

/-- Localized source equality follows from base-link equality in the
radius-two neighborhood, including the backwards transport bond. -/
theorem JfieldLoc_congr_region {L : PeriodicLatticeExtent}
    (U V : LinkCfg L) (P : Set (PeriodicLatticePlaquette L))
    (Om : Set (PeriodicLatticeSite L)) (hU : ∀ e : Bond L, e.1 ∈ Om → U e = V e)
    (x : PeriodicLatticeSite L) (μ : Fin 3)
    (hcol : ∀ z : PeriodicLatticeSite L, pdist z x ≤ 2 → z ∈ Om) :
    JfieldLoc P U x μ = JfieldLoc P V x μ := by
  unfold JfieldLoc
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  by_cases hνμ : ν = μ
  · simp [hνμ]
  · simp only [hνμ, if_false]
    have hb := AdalyFormal.StatementLaneR8.pdist_shiftBack_le x ν
    have s1 := AdalyFormal.StatementLaneR8.pdist_shift_le x ν
    have s2 := AdalyFormal.StatementLaneR8.pdist_shift_le x μ
    have hF0 : FnuMuLoc P U ν μ x = FnuMuLoc P V ν μ x :=
      FnuMuLoc_congr_region U V P Om hU ν μ x
        (hcol x (by rw [AdalyFormal.StatementLaneR8.pdist_self]; omega))
        (hcol _ (by rw [AdalyFormal.StatementLaneR8.pdist_comm]; omega))
        (hcol _ (by rw [AdalyFormal.StatementLaneR8.pdist_comm]; omega))
    set x' := periodicLatticeShiftBack x ν with hx'
    have t1 := AdalyFormal.StatementLaneR8.pdist_shift_le x' ν
    have t2 := AdalyFormal.StatementLaneR8.pdist_shift_le x' μ
    have tri1 := AdalyFormal.StatementLaneR8.pdist_triangle x x' (periodicLatticeShift x' ν)
    have tri2 := AdalyFormal.StatementLaneR8.pdist_triangle x x' (periodicLatticeShift x' μ)
    have hxmem : x' ∈ Om := hcol x' (by rw [AdalyFormal.StatementLaneR8.pdist_comm]; omega)
    have hF1 : FnuMuLoc P U ν μ x' = FnuMuLoc P V ν μ x' :=
      FnuMuLoc_congr_region U V P Om hU ν μ x' hxmem
        (hcol _ (by rw [AdalyFormal.StatementLaneR8.pdist_comm]; omega))
        (hcol _ (by rw [AdalyFormal.StatementLaneR8.pdist_comm]; omega))
    unfold DstarDir
    simp only []
    rw [← hx', hF0, hF1, hU (x', ν) hxmem]

/-- Arbitrary backgrounds agreeing within distance three of Omega1 have
exactly the SAME active source. No Abelian, amplitude, mass, or unit premise.
In particular arbitrary changes far outside this neighborhood cannot move
the effective correction source closer to the exterior crossing mode. -/
theorem activeSource_congr_near_top (sJ : PlaqSel)
    (ell k M R : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S)
    (U V : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hnear : ∀ e : Bond (scaleUp ell k Lu),
      (∃ w ∈ S.Om 1, pdist e.1 w ≤ 3) → U e = V e) :
    activeSource sJ (gparams ell k Lu hell S U a Lam) =
      activeSource sJ (gparams ell k Lu hell S V a Lam) := by
  classical
  unfold activeSource
  congr 1
  apply congrArg (WithLp.toLp 2)
  funext b
  dsimp only [activeField]
  split_ifs with hb
  · have hz : JfieldLoc (sJ _ (geomOf ell k S)) U b.1 b.2 =
        JfieldLoc (sJ _ (geomOf ell k S)) V b.1 b.2 := by
      apply JfieldLoc_congr_region U V _ {z | ∃ w ∈ S.Om 1, pdist z w ≤ 3} hnear
      intro z hz
      rcases AdalyFormal.D1Guarded.endpoint_om1 hell hS b hb.1 hb.2 with hw | hw
      · exact ⟨b.1, hw, by omega⟩
      · refine ⟨periodicLatticeShift b.1 b.2, hw, ?_⟩
        have htri := AdalyFormal.StatementLaneR8.pdist_triangle z b.1 (periodicLatticeShift b.1 b.2)
        have hshift := AdalyFormal.StatementLaneR8.pdist_shift_le b.1 b.2
        omega
    unfold JfS AdalyFormal.IngredientFamily.JSU2Loc
    apply congrArg Neg.neg
    apply Subtype.ext
    simp only [hz]
  · rfl

/-- Main partial result. The genuine correction after an arbitrary distant
boundary modification uses the ORIGINAL active source. All inverse
propagation and dressing are still those of the MODIFIED background U.
This is NOT exterior independence of D, and asserts no positive sign. -/
theorem boundary_modification_correction_formula (sD sJ : PlaqSel)
    (ell k M R : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (hS : Admissible ell M R k S)
    (U V : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hnear : ∀ e : Bond (scaleUp ell k Lu),
      (∃ w ∈ S.Om 1, pdist e.1 w ≤ 3) → U e = V e)
    (v : ↥(bondSupp (geomOf ell k S))) :
    let P := gparams ell k Lu hell S U a Lam
    let P' := gparams ell k Lu hell S V a Lam
    ⟪v, (dataS sD sJ P).Delta2 (dataS_laws sD sJ P) v⟫ =
      2 * ⟪(dataS sD sJ P).H ((dataS sD sJ P).C2 v), activeSource sJ P'⟫ := by
  dsimp only
  rw [correction_uses_active_source sD sJ (gparams ell k Lu hell S U a Lam) v,
    activeSource_congr_near_top sJ ell k M R Lu hell S hS U V a Lam hnear]

#print axioms FnuMuLoc_congr_region
#print axioms JfieldLoc_congr_region
#print axioms activeSource_congr_near_top
#print axioms boundary_modification_correction_formula

end AdalyFormal.Round6.Guarded.PlacementR2
