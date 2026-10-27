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

/-! DEV ONLY: verbatim copies of the round-4 definitions in the round-8 prefix. -/
namespace AdalyFormal.Round4.Guarded.RefuteR1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.NonVac (iv_block pcd_clamp pcd_near pcd_self'
  clamp1D coord_box_sub coord_box_in isClassCube_of)
open AdalyFormal.Balaban.CovariantOperators
  (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace
  (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice staircasePath)
open AdalyFormal.Balaban.FullReparamC
  (freeBond freeBond_not_mem_staircase freeBond_not_dropped freeBond_coord_zero)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

def dilLu (q R : ℕ) : PeriodicLatticeExtent :=
  fun μ => if μ = 0 then 6 * (R * q) + 8 * q - 1 else 4 * q - 1

def dilTower (q R : ℕ) : Tower (scaleUp 2 1 (dilLu q R)) where
  Om j := if j = 0 then {x | 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q}
    else if j = 1 then {x | 2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q}
    else ∅

def dilLam (q R : ℕ) : Set (PeriodicLatticeSite (dilLu q R)) :=
  {x | 3 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 3 * (R * q) + 6 * q}

theorem dil_unit_size {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    dilLu q R μ + 1 = if μ = 0 then 6 * (R * q) + 8 * q else 4 * q := by
  by_cases h : μ = 0 <;> simp [dilLu, h] <;> omega

theorem dil_fine_size {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    scaleUp 2 1 (dilLu q R) μ + 1 = if μ = 0 then 12 * (R * q) + 16 * q else 8 * q := by
  simp only [scaleUp, dil_unit_size hq]
  by_cases h : μ = 0 <;> simp [h] <;> omega

theorem dil_fine_bound {q : ℕ} (hq : 0 < q) (R : ℕ)
    (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    (x 0).val < 12 * (R * q) + 16 * q := by
  have h := (x 0).isLt
  simpa only [dil_fine_size hq, ↓reduceIte] using h

def dilPattern (q R : ℕ) (e : Bond (scaleUp 2 1 (dilLu q R))) : Prop :=
  (e.1 0).val = 2*(R*q)+4*q ∧ (e.1 1).val % 2 = 0 ∧ (e.1 2).val % 2 = 0 ∧ e.2 = 1

open Classical in
noncomputable def dilU (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then V e
    else Ug (if dilPattern q R e then ε else 0)

end AdalyFormal.Round4.Guarded.RefuteR1

/-! DEV ONLY: verbatim copies of round-1 definitions. -/
namespace AdalyFormal.Round9.Guarded.AnalyticR1

open scoped RealInnerProductSpace Topology
open Set Filter
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)

/-- The carrier space of the twist family at scale `q` and radius `R`. -/
abbrev TwistSpace (q R : ℕ) : Type := ↥(bondSupp (geomOf 2 1 (dilTower q R)))

/-- The pinned parameters of the curved dilated family with an arbitrary exterior field. -/
noncomputable def extP (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (dilU q R ε V) 1 (dilLam q R)

/-- The all-plaquette carrier with exterior field `V`. -/
noncomputable def extA (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    TwistSpace q R →L[ℝ] TwistSpace q R :=
  (dataS selAll selAll (extP q R ε V)).Ginv

/-- The localized correction with exterior field `V` (independent of `V`, `extD_congr`). -/
noncomputable def extD (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    TwistSpace q R →L[ℝ] TwistSpace q R :=
  (dataS selIn selIn (extP q R ε V)).Delta2 (dataS_laws selIn selIn _)

/-- Soft regularity of the single interior family `ε ↦ dilU q R ε 1` (curved interior,
trivial exterior), as `ε → 0⁺`: continuity of the carrier and of the dressing `W`, and the
first-order coefficient `D₁` of the correction.  No exterior angle appears.  NOT proved here. -/
def InteriorRegularity (q R : ℕ) (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R) : Prop :=
  Tendsto (fun ε : ℝ => extA q R ε 1) (𝓝[>] 0) (𝓝 (extA q R 0 1)) ∧
  Tendsto (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (dilU q R ε 1) 1) (𝓝[>] 0)
    (𝓝 (Wop (geomOf 2 1 (dilTower q R)) (dilU q R 0 1) 1)) ∧
  Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε 1) (𝓝[>] 0) (𝓝 D₁)

/-- The soft half of the final premise, exterior-free.  NOT proved here. -/
def InteriorSoft : Prop :=
  ∀ q R : ℕ, 0 < q → 2 ∣ R → 18 ≤ R →
    ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R, InteriorRegularity q R D₁


end AdalyFormal.Round9.Guarded.AnalyticR1


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## N. Smoothness of the plaquette operator along smooth link families

The frozen `D1Cont` proves continuity of `θ ↦ deltaKLocCLM (U θ) P` for continuous links.  The
same proof, with `ContDiff` in place of `Continuous`, gives smoothness for smooth links: every
matrix entry `⟪x, Δ(U θ) y⟫` is a finite expression in link matrices, their conjugate transposes,
products and real parts of traces. -/
section DeltaSmooth

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply curlValueCovariant)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.StatementLaneR6
open AdalyFormal.IngredientFamilyR2 (conjTR)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- Smooth links (Frobenius matrix norm). -/
def SmoothFam {L : PeriodicLatticeExtent} (U : ℝ → PeriodicLinkConfiguration SU2 L) : Prop :=
  ∀ e, ContDiff ℝ ⊤ (fun t => ((U t e : SU2) : M2))

theorem contDiff_trace2 {f : ℝ → M2} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (fun t => (Matrix.trace (f t)).re) := by
  have e : (fun t => (Matrix.trace (f t)).re) = fun t =>
      Complex.reCLM (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℝ ℂ) (f t)) := by
    funext t
    simp
  rw [e]
  exact Complex.reCLM.contDiff.comp ((LinearMap.toContinuousLinearMap _).contDiff.comp hf)

variable {L : PeriodicLatticeExtent} {U : ℝ → PeriodicLinkConfiguration SU2 L} (hU : SmoothFam U)
include hU

theorem cdF_inv (e : PeriodicLatticeEdge L) : ContDiff ℝ ⊤ (fun t => (((U t e)⁻¹ : SU2) : M2)) := by
  have e1 : (fun t => (((U t e)⁻¹ : SU2) : M2)) = fun t => conjTR ((U t e : SU2) : M2) := by
    funext t; rfl
  rw [e1]
  exact conjTR.contDiff.comp (hU e)

theorem cdF_RMap (e : PeriodicLatticeEdge L) (X : SuTwo) :
    ContDiff ℝ ⊤ (fun t => ((RMap (U t e) X : SuTwo) : M2)) := by
  have e1 : (fun t => ((RMap (U t e) X : SuTwo) : M2)) =
      fun t => ((U t e : SU2) : M2) * (X : M2) * conjTR ((U t e : SU2) : M2) := by
    funext t
    exact RMap_coe_apply (U t e) X
  rw [e1]
  exact ((hU e).mul contDiff_const).mul (conjTR.contDiff.comp (hU e))

theorem cdF_holonomyElem (p : PeriodicLatticePlaquette L) :
    ContDiff ℝ ⊤ (fun t => ((holonomyElem (U t) p : SU2) : M2)) := by
  have e1 : (fun t => ((holonomyElem (U t) p : SU2) : M2)) = fun t =>
      ((U t (p.1, p.2.1.1) : SU2) : M2) * ((U t (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : SU2) : M2) *
        (((U t (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ : SU2) : M2) *
        (((U t (p.1, p.2.1.2))⁻¹ : SU2) : M2) := by
    funext t; rfl
  rw [e1]
  exact (((hU _).mul (hU _)).mul (cdF_inv hU _)).mul (cdF_inv hU _)

theorem cdF_holonomyElemInv (p : PeriodicLatticePlaquette L) :
    ContDiff ℝ ⊤ (fun t => ((holonomyElemInv (U t) p : SU2) : M2)) := by
  have e1 : (fun t => ((holonomyElemInv (U t) p : SU2) : M2)) =
      fun t => conjTR ((holonomyElem (U t) p : SU2) : M2) := by
    funext t; rfl
  rw [e1]
  exact conjTR.contDiff.comp (cdF_holonomyElem hU p)

theorem cdF_reHolonomy (p : PeriodicLatticePlaquette L) : ContDiff ℝ ⊤ (fun t => reHolonomy (U t) p) := by
  unfold reHolonomy
  exact ((cdF_holonomyElem hU p).add (cdF_holonomyElemInv hU p)).const_smul _

theorem cdF_imHolonomy (p : PeriodicLatticePlaquette L) : ContDiff ℝ ⊤ (fun t => imHolonomy (U t) p) := by
  unfold imHolonomy
  exact ((cdF_holonomyElem hU p).sub (cdF_holonomyElemInv hU p)).const_smul _

theorem cdF_curlMat (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    ContDiff ℝ ⊤ (fun t => curlMatLM (U t) p A) := by
  simp only [curlMatLM_apply]
  unfold curlValueCovariant
  simp only [Submodule.coe_add, Submodule.coe_sub]
  exact ((contDiff_const.add (cdF_RMap hU _ _)).sub (cdF_RMap hU _ _)).sub contDiff_const

theorem cdF_a1 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    ContDiff ℝ ⊤ (fun t => a1LM (U t) p A) := by
  show ContDiff ℝ ⊤ fun t => -(bondMatRLM (U t (p.1, p.2.1.2)) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) A)
  simp only [bondMatRLM_apply]
  exact (cdF_RMap hU _ _).neg

theorem cdF_a4 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    ContDiff ℝ ⊤ (fun t => a4LM (U t) p A) := by
  show ContDiff ℝ ⊤ fun t => bondMatRLM (U t (p.1, p.2.1.1)) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) A
  simp only [bondMatRLM_apply]
  exact cdF_RMap hU _ _

omit hU in
theorem cdF_smulI {f : ℝ → M2} (hf : ContDiff ℝ ⊤ f) : ContDiff ℝ ⊤ (fun t => smulILM (f t)) := by
  show ContDiff ℝ ⊤ (fun t => Complex.I • f t)
  exact hf.const_smul _

omit hU in
theorem cdF_tr_re3 {f g h : ℝ → M2} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) (hh : ContDiff ℝ ⊤ h) :
    ContDiff ℝ ⊤ (fun t => (Matrix.trace (f t * g t * h t)).re) :=
  contDiff_trace2 ((hf.mul hg).mul hh)

theorem cdF_bilPlaq (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    ContDiff ℝ ⊤ (fun t => bilPlaq (U t) p A B) := by
  simp only [bilPlaq_atoms]
  have b1A : ContDiff ℝ ⊤ fun t => b1LM (U t) p A := cdF_smulI (cdF_a1 hU p A)
  have b4B : ContDiff ℝ ⊤ fun t => b4LM (U t) p B := cdF_smulI (cdF_a4 hU p B)
  have hre := cdF_reHolonomy hU p
  have him := cdF_imHolonomy hU p
  have hcA : ContDiff ℝ ⊤ fun t => smulILM (curlMatLM (U t) p A) := cdF_smulI (cdF_curlMat hU p A)
  have hcB : ContDiff ℝ ⊤ fun t => smulILM (curlMatLM (U t) p B) := cdF_smulI (cdF_curlMat hU p B)
  have k : ∀ (M : M2), ContDiff ℝ ⊤ fun _ : ℝ => M := fun M => contDiff_const
  refine ((((((cdF_tr_re3 hcA hcB (hre.sub (k 1))).add
    ((cdF_tr_re3 (cdF_smulI b1A) (k _) him).sub (cdF_tr_re3 (k _) b1A him))).add
    ((cdF_tr_re3 (cdF_smulI b1A) (k _) him).sub (cdF_tr_re3 (k _) b1A him))).add
    ((cdF_tr_re3 (cdF_smulI b1A) b4B him).sub (cdF_tr_re3 (cdF_smulI b4B) b1A him))).add
    ((cdF_tr_re3 (k _) (k _) him).sub (cdF_tr_re3 (k _) (k _) him))).add
    ((cdF_tr_re3 (k _) b4B him).sub (cdF_tr_re3 (cdF_smulI b4B) (k _) him))).add
    ((cdF_tr_re3 (k _) b4B him).sub (cdF_tr_re3 (cdF_smulI b4B) (k _) him))

open Classical in
theorem cdF_deltaPrimeBil (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    ContDiff ℝ ⊤ (fun t => deltaPrimeBilNormLoc (U t) P A B) := by
  have h : ∀ A B : Bond L → SuTwo, ContDiff ℝ ⊤ fun t => deltaPrimeBilRawLoc (U t) P A B := by
    intro A B
    simp only [deltaPrimeBilRawLoc_apply]
    refine ContDiff.sum (fun p _ => ?_)
    by_cases hp : p ∈ P
    · simp only [hp, if_true]; exact cdF_bilPlaq hU p A B
    · simp only [hp, if_false]; exact contDiff_const
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  exact contDiff_const.mul (contDiff_const.mul ((h A B).add (h B A)))

open Classical in
theorem cdF_curlInner (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    ContDiff ℝ ⊤ fun θ => (inner ℝ (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) x))
      (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) y)) : ℝ) := by
  simp only [PiLp.inner_apply]
  refine ContDiff.sum (fun p _ => ?_)
  simp only [plaqMask_apply]
  by_cases hp : p ∈ P
  · simp only [hp, if_true]
    show ContDiff ℝ ⊤ fun θ => AdalyFormal.Balaban.SuTwoInner.hsInner
      (curlValueCovariant (U θ) (WithLp.ofLp x) p) (curlValueCovariant (U θ) (WithLp.ofLp y) p)
    unfold AdalyFormal.Balaban.SuTwoInner.hsInner
    refine contDiff_const.mul (contDiff_trace2 ?_)
    exact (cdF_curlMat hU p (WithLp.ofLp x)).mul (cdF_curlMat hU p (WithLp.ofLp y))
  · simp only [hp, if_false]
    exact contDiff_const

theorem cdF_inner_delta (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    ContDiff ℝ ⊤ fun θ => (inner ℝ x (deltaKLocCLM (U θ) P y) : ℝ) := by
  simp only [inner_deltaKLocCLM]
  exact (cdF_curlInner hU P x y).add (cdF_deltaPrimeBil hU P _ _)

end DeltaSmooth

section DeltaSmoothCLM

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.StatementLaneR6 (deltaKLocCLM)

theorem contDiff_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {g : ℝ → E} (h : ∀ w : E, ContDiff ℝ ⊤ fun t => ⟪w, g t⟫) :
    ContDiff ℝ ⊤ g := by
  let b := stdOrthonormalBasis ℝ E
  have e : g = fun t => ∑ i, ⟪b i, g t⟫ • b i := by
    funext t
    exact (b.sum_repr' (g t)).symm
  rw [e]
  exact ContDiff.sum (fun i _ => (h (b i)).smul contDiff_const)

/-- Smoothness of the plaquette operator along smooth links (frozen `D1Cont`, `C^ω` version). -/
theorem contDiff_deltaKLocCLM {L : PeriodicLatticeExtent} {U : ℝ → PeriodicLinkConfiguration SU2 L}
    (hU : SmoothFam U) (P : Set (PeriodicLatticePlaquette L)) :
    ContDiff ℝ ⊤ (fun t => deltaKLocCLM (U t) P) :=
  contDiff_clm_apply_iff.mpr (fun y => contDiff_of_inner (fun w => cdF_inner_delta hU P w y))

/-- The derivative of the exterior path formula `A + P W* (M t - M 0) W I`, for a smooth operator
path `M`.  Stated for abstract carriers and instantiated later: for the concrete submodule carrier
the normed-space and plain instance paths of `E →L[ℝ] E` do not unify during elaboration. -/
theorem hasDerivAt_path_formula {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (M : ℝ → H →L[ℝ] H) (hM : ContDiff ℝ ⊤ M) (P : H →L[ℝ] E) (W : H →L[ℝ] H) (I : E →L[ℝ] H)
    (A : E →L[ℝ] E) (t₀ : ℝ) :
    HasDerivAt (fun t => A + P.comp (((ContinuousLinearMap.adjoint W).comp ((M t - M 0).comp W)).comp I))
      (deriv (fun t => A + P.comp (((ContinuousLinearMap.adjoint W).comp
        ((M t - M 0).comp W)).comp I)) t₀) t₀ := by
  have hM' := hM.differentiable (by simp)
  have h1 := (differentiable_const (ContinuousLinearMap.adjoint W)).clm_comp
    ((hM'.sub (differentiable_const (M 0))).clm_comp (differentiable_const W))
  have h2 := (differentiable_const P).clm_comp (h1.clm_comp (differentiable_const I))
  have hd := (differentiable_const A).add h2
  exact (hd t₀).hasDerivAt

end DeltaSmoothCLM

end AdalyFormal.Round9.Guarded.AnalyticR2

