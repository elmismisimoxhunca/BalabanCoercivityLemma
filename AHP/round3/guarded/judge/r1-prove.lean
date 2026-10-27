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

/-! Reused round-2 proof bodies. Definitions already occur in the unchanged pin. -/
namespace AdalyFormal.Round2.Guarded.R2Prove
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

theorem unit_of_kernel_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (h : ∀ x, T x = 0 → x = 0) : IsUnit T := by
  have hinj : Function.Injective T := (injective_iff_map_eq_zero T).mpr h
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, (LinearMap.injective_iff_surjective
      (f := (show E →ₗ[ℝ] E from T))).mp hinj⟩


section Algebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem response_apply (Θ B : E →L[ℝ] E) (y : Θ.range) :
    (response Θ B y : E) = (y : E) + Θ (Ring.inverse B y) := rfl

/-- Exact finite-dimensional reduction, using only a unit of the reference B.
The proof reuses the injectivity-to-unit pattern of frozen unit_transfer. -/
theorem unit_add_iff_response (Θ B : E →L[ℝ] E) (hB : IsUnit B) :
    IsUnit (B + Θ) ↔ IsUnit (response Θ B) := by
  have hl : ∀ x, B (Ring.inverse B x) = x := fun x =>
    congrArg (fun T : E →L[ℝ] E => T x) (Ring.mul_inverse_cancel B hB)
  have hr : ∀ x, Ring.inverse B (B x) = x := fun x =>
    congrArg (fun T : E →L[ℝ] E => T x) (Ring.inverse_mul_cancel B hB)
  constructor
  · intro hM
    apply unit_of_kernel_zero
    intro y hy
    have hk : (B + Θ) (Ring.inverse B y) = 0 := by
      have h := congrArg (fun z : Θ.range => (z : E)) hy
      change (y : E) + Θ (Ring.inverse B y) = 0 at h
      simpa only [add_apply, hl] using h
    have hx : Ring.inverse B (y : E) = 0 :=
      (injective_iff_map_eq_zero _).mp
        (ContinuousLinearMap.isUnit_iff_bijective.mp hM).1 _ hk
    apply Subtype.ext
    show (y : E) = 0
    rw [← hl y, hx, map_zero]
  · intro hK
    apply unit_of_kernel_zero
    intro x hx
    have hb : B x = -Θ x := eq_neg_of_add_eq_zero_left hx
    let y : Θ.range := ⟨-Θ x, by exact ⟨-x, by simp⟩⟩
    have hy : (y : E) = B x := hb.symm
    have hxy : Ring.inverse B (y : E) = x := by rw [hy, hr]
    have hk : response Θ B y = 0 := by
      apply Subtype.ext
      change (y : E) + Θ (Ring.inverse B y) = 0
      rw [hy, hr]
      exact hx
    have hz : y = 0 := (injective_iff_map_eq_zero _).mp
      (ContinuousLinearMap.isUnit_iff_bijective.mp hK).1 _ hk
    have hy0 : (y : E) = 0 := congrArg (fun z : Θ.range => (z : E)) hz
    rw [hy0, map_zero] at hxy
    exact hxy.symm

omit [FiniteDimensional ℝ E] in
/-- Resolvent identity with the exact correction; only localized inverses will
be substituted into it below. -/
theorem inverse_sub_apply (B D : E →L[ℝ] E)
    (hB : IsUnit B) (hC : IsUnit (B - D)) (y : E) :
    Ring.inverse (B - D) y - Ring.inverse B y =
      Ring.inverse (B - D) (D (Ring.inverse B y)) := by
  have hl : B (Ring.inverse B y) = y :=
    congrArg (fun T : E →L[ℝ] E => T y) (Ring.mul_inverse_cancel B hB)
  have hr : Ring.inverse (B - D) ((B - D) (Ring.inverse B y)) = Ring.inverse B y :=
    congrArg (fun T : E →L[ℝ] E => T (Ring.inverse B y))
      (Ring.inverse_mul_cancel (B - D) hC)
  calc
    Ring.inverse (B - D) y - Ring.inverse B y =
        Ring.inverse (B - D) y -
          Ring.inverse (B - D) ((B - D) (Ring.inverse B y)) := by rw [hr]
    _ = Ring.inverse (B - D) (y - (B - D) (Ring.inverse B y)) :=
      (map_sub _ _ _).symm
    _ = Ring.inverse (B - D) (D (Ring.inverse B y)) := by
      rw [sub_apply, hl]
      congr 1
      abel

/-- Boundary response changes by the round trip through the genuine correction. -/
theorem response_sub_apply (Θ B D : E →L[ℝ] E)
    (hB : IsUnit B) (hC : IsUnit (B - D)) (y : Θ.range) :
    (response Θ (B - D) y : E) - (response Θ B y : E) =
      Θ (Ring.inverse (B - D) (D (Ring.inverse B y))) := by
  rw [response_apply, response_apply]
  calc
    (y : E) + Θ (Ring.inverse (B - D) y) - ((y : E) + Θ (Ring.inverse B y)) =
        Θ (Ring.inverse (B - D) y) - Θ (Ring.inverse B y) := by abel
    _ = Θ (Ring.inverse (B - D) y - Ring.inverse B y) := (map_sub _ _ _).symm
    _ = Θ (Ring.inverse (B - D) (D (Ring.inverse B y))) := by
      rw [inverse_sub_apply B D hB hC]


end Algebra
section Concrete
variable (P : IngrBParams)

theorem localCorrected_eq : localCorrected P = G1invS selIn selIn P := by
  exact ((dataS selIn selIn P).G1inv_unique
    (AdalyFormal.D1Literal.G1invS_spec selIn selIn P)
    ((dataS selIn selIn P).isG1inv_sub (dataS_laws selIn selIn P))).symm

theorem carrier_eq_local_add_shift :
    (dataS selAll selAll P).Ginv = (dataS selIn selIn P).Ginv + boundaryShift P := by
  unfold boundaryShift
  abel

theorem pencil_eq_local_add_shift :
    (dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) =
        localCorrected P + boundaryShift P := by
  unfold localCorrected boundaryShift
  abel

/-- The literal guard can itself be checked on the boundary response. -/
theorem carrier_isUnit_iff_response (hu : IsUnit (dataS selIn selIn P).Ginv) :
    IsUnit (dataS selAll selAll P).Ginv ↔
      IsUnit (response (boundaryShift P) (dataS selIn selIn P).Ginv) := by
  rw [carrier_eq_local_add_shift P]
  exact unit_add_iff_response _ _ hu

/-- Exact corrected unit criterion on the same boundary space, with only
localized corrected invertibility as input. No literal inverse is used. -/
theorem pencil_isUnit_iff_response (hu : IsUnit (G1invS selIn selIn P)) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) ↔
      IsUnit (response (boundaryShift P) (localCorrected P)) := by
  rw [pencil_eq_local_add_shift P]
  exact unit_add_iff_response _ _ (by rw [localCorrected_eq P]; exact hu)


end Concrete

theorem goalPos1_iff_boundary_response : GoalPos1 ↔ GShape CBoundaryResponse := by
  constructor
  · intro hp
    exact AdalyFormal.D1Residual.GShape_imp AdalyFormal.D1Residual.CPen CBoundaryResponse
      (fun ell k h0 M R Lu S U a Lam _ _ hW _ hc =>
        (pencil_isUnit_iff_response (gparams ell k Lu h0 S U a Lam) hW.2.1).mp hc) hp
  · intro hb
    exact AdalyFormal.D1Residual.GShape_imp CBoundaryResponse AdalyFormal.D1Residual.CPen
      (fun ell k h0 M R Lu S U a Lam _ _ hW _ hc =>
        (pencil_isUnit_iff_response (gparams ell k Lu h0 S U a Lam) hW.2.1).mpr hc) hb

/-- The original guarded headline, with every pinned quantifier retained. -/
theorem goalPos2_iff_boundary_response : GoalPos2 ↔ GShape CBoundaryResponse :=
  goalPos2_iff_goalPos1.trans goalPos1_iff_boundary_response


#print axioms unit_of_kernel_zero
#print axioms response_apply
#print axioms unit_add_iff_response
#print axioms inverse_sub_apply
#print axioms response_sub_apply
#print axioms localCorrected_eq
#print axioms carrier_eq_local_add_shift
#print axioms pencil_eq_local_add_shift
#print axioms carrier_isUnit_iff_response
#print axioms pencil_isUnit_iff_response
#print axioms goalPos1_iff_boundary_response
#print axioms goalPos2_iff_boundary_response
end AdalyFormal.Round2.Guarded.R2Prove

/-! Round-3 positive attempt. None of the conditional criteria below proves a pin. -/
namespace AdalyFormal.Round3.Guarded.R1Prove

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round2.Guarded.R2Prove
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-! Exact selector-shell locality, stronger than vanishing on all level-zero bonds. -/
section Shell
variable (P : IngrBParams)

/-- Fields zero only on edges belonging to a plaquette omitted by selIn. -/
def offSelectorShell : Submodule ℝ ↥(bondSupp P.G) where
  carrier := {x | ∀ p : PeriodicLatticePlaquette P.Lf, p ∉ plaqIn P.G.Om0 →
    ∀ e ∈ periodicPlaquetteBoundaryEdges p, (WithLp.ofLp (iE P.G x)) e = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy p hp e he
    simp [hx p hp e he, hy p hp e he]
  smul_mem' := by
    intro c x hx p hp e he
    simp [hx p hp e he]

/-- The gauge-fixing correction vanishes on these edges for every input, not
just for inputs with zero level-zero trace. Adapted from Wop_zero_on_notIn. -/
theorem Wop_eq_on_selector_shell {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (h4 : 4 ≤ R * M)
    (x : ↥(bondSupp P.G)) {p : PeriodicLatticePlaquette P.Lf}
    (hp : p ∉ plaqIn P.G.Om0) (e : Bond P.Lf)
    (he : e ∈ periodicPlaquetteBoundaryEdges p) :
    (WithLp.ofLp (Wop P.G P.U P.a (iE P.G x))) e =
      (WithLp.ofLp (iE P.G x)) e := by
  obtain ⟨n1, n2⟩ := edge_ends_not_om1_of_notIn hS h4 hp he
  have hfz : ∀ c : PeriodicLatticeSite P.Lf, c ∉ P.S.Om 1 →
      (WithLp.ofLp (Gp P.G P.U P.a
        (Rproj P.G P.U (gradAdj P.U (iE P.G x))))) c = 0 := by
    intro c hc
    by_cases hc0 : c ∈ P.S.Om 0
    · refine Gp_Rproj_lam0 P.G P.U P.a _ (x := c) ?_
      refine ⟨fun μ => by simp, hc0, ?_⟩
      simpa using hc
    · exact Gp_Rproj_out P.G P.U P.a _ (x := c) hc0
  have hgrad : (WithLp.ofLp (gradL2 P.U
      (Gp P.G P.U P.a (Rproj P.G P.U (gradAdj P.U (iE P.G x)))))) e = 0 := by
    rw [gradL2_apply]
    unfold AdalyFormal.Balaban.CovariantOperators.gradValueCovariant
    rw [hfz _ n1, hfz _ n2]
    simp
  change (WithLp.ofLp (iE P.G x)) e -
    (WithLp.ofLp (gradL2 P.U (Gp P.G P.U P.a
      (Rproj P.G P.U (gradAdj P.U (iE P.G x)))))) e = _
  rw [hgrad, sub_zero]

/-- The actual selector difference kills fields zero on the selector shell. -/
theorem boundaryShift_kills_offSelectorShell {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (h4 : 4 ≤ R * M)
    (x : ↥(bondSupp P.G)) (hx : x ∈ offSelectorShell P) :
    boundaryShift P x = 0 := by
  have hΔ : DeltaS selAll P.G P.U (Wop P.G P.U P.a (iE P.G x)) =
      DeltaS selIn P.G P.U (Wop P.G P.U P.a (iE P.G x)) := by
    apply deltaK_set_congr
    intro p hpq e he
    have hp : p ∉ plaqIn P.G.Om0 := by
      intro hin
      apply hpq
      exact ⟨fun _ => hin, fun _ => Set.mem_univ _⟩
    rw [Wop_eq_on_selector_shell P hS h4 x hp e he]
    exact hx p hp e he
  have hD : DpiFullS selAll P.G P.U P.a (iE P.G x) =
      DpiFullS selIn P.G P.U P.a (iE P.G x) := by
    simp only [DpiFullS, ContinuousLinearMap.comp_apply]
    rw [hΔ]
  apply sub_eq_zero.mpr
  change (AdalyFormal.D1Literal.dataS selAll selAll P).Ginv x =
    (AdalyFormal.D1Literal.dataS selIn selIn P).Ginv x
  rw [dataS_Ginv_eq, dataS_Ginv_eq]
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  change pE P.G (DpiFullS selAll P.G P.U P.a (iE P.G x)) + _ + _ =
    pE P.G (DpiFullS selIn P.G P.U P.a (iE P.G x)) + _ + _
  rw [hD]

theorem boundaryShift_symm (x y : ↥(bondSupp P.G)) :
    ⟪boundaryShift P x, y⟫ = ⟪x, boundaryShift P y⟫ := by
  simp only [boundaryShift, sub_apply, inner_sub_left,
    inner_sub_right,
    (dataS selAll selAll P).Ginv_symm (dataS_laws selAll selAll P),
    (dataS selIn selIn P).Ginv_symm (dataS_laws selIn selIn P)]

/-- Exact shell-support statement for the actual difference range. No inverse
has been asserted to preserve this support. -/
theorem boundaryShift_range_le_selector_shell {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (h4 : 4 ≤ R * M) :
    (boundaryShift P).range ≤ (offSelectorShell P)ᗮ := by
  rintro y ⟨x, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  intro v hv
  change ⟪v, boundaryShift P x⟫ = 0
  rw [← boundaryShift_symm P v x,
    boundaryShift_kills_offSelectorShell P hS h4 v hv, inner_zero_left]

/-- The earlier all-level-zero vanishing space is contained in the new space.
No strict containment or properness is asserted here. -/
theorem V0_le_offSelectorShell {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hell0 : 0 < P.ell)
    (h4 : 4 ≤ R * M) : V0 P.G ≤ offSelectorShell P := by
  intro x hx p hp e he
  rw [← Wop_eq_on_selector_shell P hS h4 x hp e he]
  exact Wop_zero_on_notIn hS hell0 h4 P.U P.a x hx hp e he

end Shell

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Inverse-relative response change, on the invariant boundary range. -/
noncomputable def relativeReturn (Θ B C : E →L[ℝ] E) : Θ.range →L[ℝ] Θ.range :=
  (Ring.inverse (response Θ B)).comp (response Θ C - response Θ B)

omit [FiniteDimensional ℝ E] in
/-- Elementary perturbation identity, reusing the frozen kernel-to-unit route. -/
theorem kernel_iff_relative_neg (S T : E →L[ℝ] E) (hS : IsUnit S) (x : E) :
    T x = 0 ↔ ((Ring.inverse S).comp (T - S)) x = -x := by
  have hl : ∀ z, S (Ring.inverse S z) = z := fun z =>
    congrArg (fun F : E →L[ℝ] E => F z) (Ring.mul_inverse_cancel S hS)
  have hr : ∀ z, Ring.inverse S (S z) = z := fun z =>
    congrArg (fun F : E →L[ℝ] E => F z) (Ring.inverse_mul_cancel S hS)
  constructor
  · intro hx
    simp only [ContinuousLinearMap.comp_apply, sub_apply,
      hx, zero_sub, map_neg, hr]
  · intro hx
    have hh := congrArg (fun z => S z) hx
    change S (Ring.inverse S ((T - S) x)) = S (-x) at hh
    rw [hl, map_neg] at hh
    change T x - S x = - S x at hh
    simpa using (sub_eq_iff_eq_add.mp hh)

/-- This does not require positive definiteness of the reference operator. -/
theorem unit_of_relative_norm_lt_one (S T : E →L[ℝ] E) (hS : IsUnit S)
    (hn : ‖(Ring.inverse S).comp (T - S)‖ < 1) : IsUnit T := by
  apply unit_of_kernel_zero
  intro x hx
  have hfix := (kernel_iff_relative_neg S T hS x).mp hx
  have hb := ((Ring.inverse S).comp (T - S)).le_opNorm x
  rw [hfix, norm_neg] at hb
  by_contra hne
  have hlt := mul_lt_mul_of_pos_right hn (norm_pos_iff.mpr hne)
  rw [one_mul] at hlt
  exact (not_lt_of_ge hb) hlt

/-- A failure has an exact minus-one mode of the inverse-relative return. -/
theorem failure_has_relative_mode (S T : E →L[ℝ] E)
    (hS : IsUnit S) (hbad : ¬ IsUnit T) :
    (∃ x : E, x ≠ 0 ∧ T x = 0 ∧ ((Ring.inverse S).comp (T - S)) x = -x) ∧
      1 ≤ ‖(Ring.inverse S).comp (T - S)‖ := by
  have hex : ∃ x : E, T x = 0 ∧ x ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hbad (unit_of_kernel_zero T hn)
  obtain ⟨x, hx, hne⟩ := hex
  refine ⟨⟨x, hne, hx, (kernel_iff_relative_neg S T hS x).mp hx⟩, ?_⟩
  by_contra hn
  exact hbad (unit_of_relative_norm_lt_one S T hS (lt_of_not_ge hn))

/-- Absolute return estimate. Notice that it alone is not a stability criterion. -/
theorem response_sub_norm_le (Θ B D : E →L[ℝ] E)
    (hB : IsUnit B) (hC : IsUnit (B - D)) :
    ‖response Θ (B - D) - response Θ B‖ ≤
      ‖Θ‖ * ‖Ring.inverse (B - D)‖ * ‖D‖ * ‖Ring.inverse B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  change ‖(response Θ (B - D) y : E) - (response Θ B y : E)‖ ≤ _
  rw [response_sub_apply Θ B D hB hC y]
  calc
    ‖Θ (Ring.inverse (B - D) (D (Ring.inverse B y)))‖ ≤
        ‖Θ‖ * ‖Ring.inverse (B - D) (D (Ring.inverse B y))‖ := Θ.le_opNorm _
    _ ≤ ‖Θ‖ * (‖Ring.inverse (B - D)‖ * ‖D (Ring.inverse B y)‖) := by
      gcongr; exact (Ring.inverse (B - D)).le_opNorm _
    _ ≤ ‖Θ‖ * (‖Ring.inverse (B - D)‖ * (‖D‖ * ‖Ring.inverse B y‖)) := by
      gcongr; exact D.le_opNorm _
    _ ≤ ‖Θ‖ * (‖Ring.inverse (B - D)‖ * (‖D‖ * (‖Ring.inverse B‖ * ‖y‖))) := by
      gcongr; exact (Ring.inverse B).le_opNorm _
    _ = (‖Θ‖ * ‖Ring.inverse (B - D)‖ * ‖D‖ * ‖Ring.inverse B‖) * ‖y‖ := by ring

/-- The additional inverse-response factor cannot be dropped from this estimate. -/
theorem relativeReturn_norm_le (Θ B D : E →L[ℝ] E)
    (hB : IsUnit B) (hC : IsUnit (B - D)) :
    ‖relativeReturn Θ B (B - D)‖ ≤
      ‖Ring.inverse (response Θ B)‖ *
        (‖Θ‖ * ‖Ring.inverse (B - D)‖ * ‖D‖ * ‖Ring.inverse B‖) := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (response_sub_norm_le Θ B D hB hC) (norm_nonneg _))

/-- Specialize the finite-dimensional criterion before substituting the nested
concrete carrier, keeping its inherited Hilbert instances explicit to Lean. -/
theorem response_isUnit_of_relative_small (Θ B C : E →L[ℝ] E)
    (hK : IsUnit (response Θ B)) (hn : ‖relativeReturn Θ B C‖ < 1) :
    IsUnit (response Θ C) :=
  unit_of_relative_norm_lt_one _ _ hK hn

theorem response_failure_has_relative_mode (Θ B C : E →L[ℝ] E)
    (hK : IsUnit (response Θ B)) (hbad : ¬ IsUnit (response Θ C)) :
    (∃ y : Θ.range, y ≠ 0 ∧ response Θ C y = 0 ∧
      relativeReturn Θ B C y = -y) ∧ 1 ≤ ‖relativeReturn Θ B C‖ :=
  failure_has_relative_mode _ _ hK hbad

end Algebra

section Concrete
variable (P : IngrBParams)

/-- Positive pointwise criterion on the actual boundary responses. The norm
hypothesis is explicit, and is not obtained from the class in this file. -/
theorem pencil_isUnit_of_relative_boundary_smallness
    (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (hn : ‖relativeReturn (boundaryShift P)
      (dataS selIn selIn P).Ginv (localCorrected P)‖ < 1) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) := by
  apply (pencil_isUnit_iff_response P hW.2.1).mpr
  exact response_isUnit_of_relative_small _ _ _
    ((carrier_isUnit_iff_response P hW.1).mp hu) hn

/-- Exact obstruction using only the boundary range and the localized inverses. -/
theorem guarded_failure_has_relative_boundary_mode
    (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (hbad : ¬ IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))) :
    (∃ y : (boundaryShift P).range, y ≠ 0 ∧
      response (boundaryShift P) (localCorrected P) y = 0 ∧
      relativeReturn (boundaryShift P) (dataS selIn selIn P).Ginv
        (localCorrected P) y = -y) ∧
    1 ≤ ‖relativeReturn (boundaryShift P) (dataS selIn selIn P).Ginv
      (localCorrected P)‖ := by
  exact response_failure_has_relative_mode _ _ _
    ((carrier_isUnit_iff_response P hW.1).mp hu)
    (fun h => hbad ((pencil_isUnit_iff_response P hW.2.1).mpr h))

/-- Exact support route: the return may be nonzero away from the selector shell.
This propagation premise is not inferred from raw-jet locality. -/
theorem pencil_isUnit_of_return_offSelectorShell {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (h4 : 4 ≤ R * M)
    (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (hret : ∀ y : (boundaryShift P).range,
      Ring.inverse (localCorrected P)
        ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
          (Ring.inverse (dataS selIn selIn P).Ginv y)) ∈ offSelectorShell P) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) := by
  have hC : IsUnit (localCorrected P) := by
    rw [localCorrected_eq P]
    exact hW.2.1
  have heq : response (boundaryShift P) (localCorrected P) =
      response (boundaryShift P) (dataS selIn selIn P).Ginv := by
    apply ContinuousLinearMap.ext
    intro y
    apply Subtype.ext
    apply sub_eq_zero.mp
    exact (response_sub_apply (boundaryShift P) (dataS selIn selIn P).Ginv
      ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) hW.1 hC y).trans
      (boundaryShift_kills_offSelectorShell P hS h4 _ (hret y))
  apply (pencil_isUnit_iff_response P hW.2.1).mpr
  rw [heq]
  exact (carrier_isUnit_iff_response P hW.1).mp hu

end Concrete

/-- A sufficient quantitative conclusion, with the entire original GShape prefix. -/
def CRelativeBoundarySmall : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell)
    (_ : Tower (scaleUp ell k Lu)) (_ : LinkCfg (scaleUp ell k Lu))
    (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop :=
  fun ell k Lu h S U a Lam =>
    let P := gparams ell k Lu h S U a Lam
    ‖relativeReturn (boundaryShift P) (dataS selIn selIn P).Ginv (localCorrected P)‖ < 1

/-- Conditional route to the unchanged pin. Its premise remains unproved. -/
theorem goalPos2_of_relative_boundary_smallness (h : GShape CRelativeBoundarySmall) : GoalPos2 := by
  apply goalPos2_iff_goalPos1.mpr
  exact AdalyFormal.D1Residual.GShape_imp CRelativeBoundarySmall AdalyFormal.D1Residual.CPen
    (fun ell k h0 M R Lu S U a Lam _ _ hW hu hn =>
      pencil_isUnit_of_relative_boundary_smallness (gparams ell k Lu h0 S U a Lam) hW hu hn) h

/-- Sufficient propagation conclusion for the exact selector shell. -/
def CReturnOffSelectorShell : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell)
    (_ : Tower (scaleUp ell k Lu)) (_ : LinkCfg (scaleUp ell k Lu))
    (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop :=
  fun ell k Lu h S U a Lam =>
    let P := gparams ell k Lu h S U a Lam
    ∀ y : (boundaryShift P).range,
      Ring.inverse (localCorrected P)
        ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
          (Ring.inverse (dataS selIn selIn P).Ginv y)) ∈ offSelectorShell P

/-- A second conditional route, not a proof that the propagation premise holds. -/
theorem goalPos2_of_return_offSelectorShell (h : GShape CReturnOffSelectorShell) : GoalPos2 := by
  apply goalPos2_iff_goalPos1.mpr
  exact AdalyFormal.D1Residual.GShape_imp CReturnOffSelectorShell AdalyFormal.D1Residual.CPen
    (fun ell k h0 M R Lu S U a Lam hS hr hW hu hn =>
      pencil_isUnit_of_return_offSelectorShell (gparams ell k Lu h0 S U a Lam)
        hS (by omega) hW hu hn) h

#print axioms offSelectorShell
#print axioms V0_le_offSelectorShell
#print axioms response_isUnit_of_relative_small
#print axioms response_failure_has_relative_mode
#print axioms pencil_isUnit_of_return_offSelectorShell
#print axioms CReturnOffSelectorShell
#print axioms goalPos2_of_return_offSelectorShell
#print axioms Wop_eq_on_selector_shell
#print axioms boundaryShift_kills_offSelectorShell
#print axioms boundaryShift_symm
#print axioms boundaryShift_range_le_selector_shell
#print axioms relativeReturn
#print axioms kernel_iff_relative_neg
#print axioms unit_of_relative_norm_lt_one
#print axioms failure_has_relative_mode
#print axioms response_sub_norm_le
#print axioms relativeReturn_norm_le
#print axioms pencil_isUnit_of_relative_boundary_smallness
#print axioms guarded_failure_has_relative_boundary_mode
#print axioms CRelativeBoundarySmall
#print axioms goalPos2_of_relative_boundary_smallness

end AdalyFormal.Round3.Guarded.R1Prove

/-! Directly reused frozen project proof roots. -/
#print axioms AdalyFormal.D1Guarded.edge_ends_not_om1_of_notIn
#print axioms AdalyFormal.D1Guarded.Gp_Rproj_lam0
#print axioms AdalyFormal.D1Guarded.Gp_Rproj_out
#print axioms AdalyFormal.D1Guarded.Wop_zero_on_notIn
#print axioms AdalyFormal.D1Guarded.deltaK_set_congr
#print axioms AdalyFormal.D1Guarded.dataS_Ginv_eq
#print axioms AdalyFormal.D1Guarded.WellDefAt
#print axioms AdalyFormal.IngredientFamilyR2.gradL2_apply
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.Ginv_symm
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.G1inv_unique
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.isG1inv_sub
#print axioms AdalyFormal.D1Literal.G1invS_spec
#print axioms AdalyFormal.D1Residual.GShape_imp
#print axioms AdalyFormal.D1Residual.P428Target8SG_iff_pencilT
