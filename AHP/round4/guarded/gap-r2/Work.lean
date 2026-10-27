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

/-!
Gap route, second pass. The pin above is unchanged. First retain the weighted
relative estimate on the genuine assembly. Then test exactly which conclusions
follow from the proposed localized gap and smallness argument. The two-coordinate
operators below are an algebraic diagnostic, never a lattice counterexample.
-/
namespace AdalyFormal.Round4.Guarded.GapR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round2.Guarded.R2Prove
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.M1 (wnormSq)

/-- The weighted estimates yield a depth-free relative form bound for B. -/
theorem correction_relative_to_localized (P : IngrBParams) (cw ε : ℝ)
    (hcw : 0 < cw) (hε : 0 ≤ ε)
    (hB : ∀ x : ↥(bondSupp P.G),
      cw * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf) ≤
        ⟪x, (dataS selIn selIn P).Ginv x⟫)
    (hD : ∀ x : ↥(bondSupp P.G),
      |⟪x, (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x⟫| ≤
        ε * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf))
    (x : ↥(bondSupp P.G)) :
    |⟪x, (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x⟫| ≤
      (ε / cw) * ⟪x, (dataS selIn selIn P).Ginv x⟫ := by
  calc
    _ ≤ ε * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf) := hD x
    _ = (ε / cw) * (cw * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf)) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB x) (div_nonneg hε hcw.le)

/-- C and B are relatively close in quadratic form without an ordinary-norm
conversion or a depth-dependent cap. This still says nothing about A. -/
theorem corrected_localized_sandwich (P : IngrBParams) (cw ε : ℝ)
    (hcw : 0 < cw) (hε : 0 ≤ ε)
    (hB : ∀ x : ↥(bondSupp P.G),
      cw * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf) ≤
        ⟪x, (dataS selIn selIn P).Ginv x⟫)
    (hD : ∀ x : ↥(bondSupp P.G),
      |⟪x, (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x⟫| ≤
        ε * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf))
    (x : ↥(bondSupp P.G)) :
    (1 - ε / cw) * ⟪x, (dataS selIn selIn P).Ginv x⟫ ≤
      ⟪x, localCorrected P x⟫ ∧
    ⟪x, localCorrected P x⟫ ≤
      (1 + ε / cw) * ⟪x, (dataS selIn selIn P).Ginv x⟫ := by
  have h := abs_le.mp (correction_relative_to_localized P cw ε hcw hε hB hD x)
  simp only [localCorrected, sub_apply, inner_sub_right]
  constructor <;> nlinarith [h.1, h.2]

#print axioms correction_relative_to_localized
#print axioms corrected_localized_sandwich
end AdalyFormal.Round4.Guarded.GapR2

/-! The next three helpers are copied verbatim from the round-2 response proof. -/
namespace AdalyFormal.Round2.Guarded.R2Prove
open scoped RealInnerProductSpace
/-- Finite-dimensional endomorphism criterion, as used by frozen unit_transfer. -/
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

/-- This is an actual restriction to an invariant range, not an inverse of a
compression of B. -/
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
end Algebra
#print axioms unit_of_kernel_zero
#print axioms response_apply
#print axioms unit_add_iff_response
end AdalyFormal.Round2.Guarded.R2Prove

namespace AdalyFormal.Round4.Guarded.GapR2
open scoped RealInnerProductSpace
open AdalyFormal.Round2.Guarded.R2Prove

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A genuine symmetric two-coordinate continuous operator. -/
noncomputable def block (a b c : ℝ) : Plane →L[ℝ] Plane :=
  (Matrix.toEuclideanLin !![a, b; b, c]).toContinuousLinearMap

theorem block_apply (a b c : ℝ) (x : Plane) :
    WithLp.ofLp (block a b c x) = ![a * x 0 + b * x 1, b * x 0 + c * x 1] := by
  funext i
  fin_cases i <;>
    simp [block, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      LinearMap.coe_toContinuousLinearMap']

theorem block_symm (a b c : ℝ) (x y : Plane) :
    ⟪block a b c x, y⟫ = ⟪x, block a b c y⟫ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    block_apply, block_apply]
  simp [dotProduct, Fin.sum_univ_two]
  ring

theorem block_form (a b c : ℝ) (x : Plane) :
    ⟪x, block a b c x⟫ = a * (x 0)^2 + 2 * b * x 0 * x 1 + c * (x 1)^2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, block_apply]
  simp [dotProduct, Fin.sum_univ_two]
  ring

theorem norm_sq_plane (x : Plane) : ‖x‖^2 = (x 0)^2 + (x 1)^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- Coordinate determinant criterion, without numerical evaluation. -/
theorem block_unit (a b c : ℝ) (h : a * c - b^2 ≠ 0) : IsUnit (block a b c) := by
  apply unit_of_kernel_zero
  intro x hx
  have hx0 := congrArg (fun y : Plane => y 0) hx
  have hx1 := congrArg (fun y : Plane => y 1) hx
  change WithLp.ofLp (block a b c x) 0 = 0 at hx0
  change WithLp.ofLp (block a b c x) 1 = 0 at hx1
  rw [block_apply] at hx0 hx1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hx0 hx1
  have h0 : (a*c-b^2) * x 0 = 0 := by
    calc
      _ = c * (a*x 0+b*x 1) - b * (b*x 0+c*x 1) := by ring
      _ = 0 := by rw [hx0, hx1]; ring
  have h1 : (a*c-b^2) * x 1 = 0 := by
    calc
      _ = a * (b*x 0+c*x 1) - b * (a*x 0+b*x 1) := by ring
      _ = 0 := by rw [hx0, hx1]; ring
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i
  · exact (mul_eq_zero.mp h0).resolve_left h
  · exact (mul_eq_zero.mp h1).resolve_left h

noncomputable def bulk (q : ℝ) : Plane →L[ℝ] Plane := block 1 q 1
noncomputable def correction (d : ℝ) : Plane →L[ℝ] Plane := block 0 0 d
noncomputable def shift (q d : ℝ) : Plane →L[ℝ] Plane := block (q^2 / (1-d) - 1) 0 0

theorem bulk_gap (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1/4) (x : Plane) :
    (3/4 : ℝ) * ‖x‖^2 ≤ ⟪x, bulk q x⟫ := by
  rw [bulk, block_form, norm_sq_plane]
  have h0 := mul_nonneg (show 0 ≤ 1/4-q by linarith) (sq_nonneg (x 0))
  have h1 := mul_nonneg (show 0 ≤ 1/4-q by linarith) (sq_nonneg (x 1))
  have h2 := mul_nonneg hq (sq_nonneg (x 0+x 1))
  nlinarith

theorem correction_norm (d : ℝ) (hd : 0 ≤ d) : ‖correction d‖ ≤ d := by
  apply AdalyFormal.DLayer.opNorm_le_of_symm_form _ (block_symm 0 0 d) hd
  intro x
  rw [correction, block_form, norm_sq_plane]
  simp only [zero_mul, zero_add]
  rw [abs_of_nonneg (mul_nonneg hd (sq_nonneg (x 1)))]
  nlinarith [mul_nonneg hd (sq_nonneg (x 0))]

theorem corrected_gap (q d : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1/4)
    (hd : d ≤ 1/4) (x : Plane) :
    (1/2 : ℝ) * ‖x‖^2 ≤ ⟪x, (bulk q - correction d) x⟫ := by
  have hB := bulk_gap q hq hq1 x
  simp only [sub_apply, inner_sub_right]
  rw [correction, block_form]
  rw [norm_sq_plane] at hB ⊢
  nlinarith [mul_nonneg (show 0 ≤ 1/4-d by linarith) (sq_nonneg (x 1)),
    sq_nonneg (x 0)]

/-- The correction acts strictly off the boundary range. -/
theorem correction_shift_zero (q d : ℝ) : (correction d).comp (shift q d) = 0 := by
  ext x i
  change WithLp.ofLp (correction d (shift q d x)) i = 0
  simp only [correction, shift, block_apply]
  fin_cases i <;> simp

/-- The coupling can be made independently arbitrarily small. -/
theorem bulk_near_identity (q : ℝ) (hq : 0 ≤ q) :
    ‖bulk q - (1 : Plane →L[ℝ] Plane)‖ ≤ q := by
  have he : bulk q - 1 = block 0 q 0 := by
    ext x i
    change WithLp.ofLp (bulk q x) i - x i = WithLp.ofLp (block 0 q 0 x) i
    simp only [bulk, block_apply]
    fin_cases i <;> simp
  rw [he]
  apply AdalyFormal.DLayer.opNorm_le_of_symm_form _ (block_symm 0 q 0) hq
  intro x
  rw [block_form, norm_sq_plane]
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hq (sq_nonneg (x 0+x 1))]
  · nlinarith [mul_nonneg hq (sq_nonneg (x 0-x 1))]

#print axioms Plane
#print axioms block
#print axioms block_apply
#print axioms block_symm
#print axioms block_form
#print axioms norm_sq_plane
#print axioms block_unit
#print axioms bulk
#print axioms correction
#print axioms shift
#print axioms bulk_gap
#print axioms correction_norm
#print axioms corrected_gap
#print axioms correction_shift_zero
#print axioms bulk_near_identity

/-- An exact kernel vector, not a determinant sign sample. -/
theorem block_not_unit (a b c : ℝ) (hc : c ≠ 0) (hd : a*c-b^2 = 0) :
    ¬ IsUnit (block a b c) := by
  intro hu
  let x : Plane := WithLp.toLp 2 ![c, -b]
  have hx : block a b c x = 0 := by
    apply WithLp.ofLp_injective 2
    rw [block_apply]
    funext i
    fin_cases i <;> simp [x]
    · nlinarith
    · ring
  have hz : x = 0 := (injective_iff_map_eq_zero _).mp
    (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1 x hx
  have := congrArg (fun y : Plane => y 0) hz
  exact hc (by simpa [x] using this)

theorem carrier_block (q d : ℝ) :
    bulk q + shift q d = block (q^2/(1-d)) q 1 := by
  ext x i
  change WithLp.ofLp (bulk q x) i + WithLp.ofLp (shift q d x) i = _
  simp only [bulk, shift, block_apply]
  fin_cases i <;> simp <;> ring

theorem pencil_block (q d : ℝ) :
    bulk q - correction d + shift q d = block (q^2/(1-d)) q (1-d) := by
  ext x i
  change WithLp.ofLp (bulk q x) i - WithLp.ofLp (correction d x) i +
    WithLp.ofLp (shift q d x) i = _
  simp only [bulk, correction, shift, block_apply]
  fin_cases i <;> simp <;> ring

theorem model_bulk_unit (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1/4) :
    IsUnit (bulk q) :=
  AdalyFormal.DLayer.coercive_isUnit _ (by norm_num : (0:ℝ) < 3/4)
    (bulk_gap q hq hq1)

theorem model_corrected_unit (q d : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1/4)
    (hd : d ≤ 1/4) : IsUnit (bulk q - correction d) :=
  AdalyFormal.DLayer.coercive_isUnit _ (by norm_num : (0:ℝ) < 1/2)
    (corrected_gap q d hq hq1 hd)

theorem model_carrier_unit (q d : ℝ) (hq : 0 < q) (hd : 0 < d) (hd1 : d < 1) :
    IsUnit (bulk q + shift q d) := by
  rw [carrier_block]
  apply block_unit
  have hn : 1-d ≠ 0 := ne_of_gt (sub_pos.mpr hd1)
  have he : q^2/(1-d)*1-q^2 = q^2*d/(1-d) := by field_simp; ring
  rw [he]
  exact ne_of_gt (div_pos (mul_pos (sq_pos_of_pos hq) hd) (sub_pos.mpr hd1))

theorem model_pencil_not_unit (q d : ℝ) (hd1 : d < 1) :
    ¬ IsUnit (bulk q - correction d + shift q d) := by
  rw [pencil_block]
  apply block_not_unit _ _ _ (ne_of_gt (sub_pos.mpr hd1))
  field_simp

/-- Full-carrier inverse on an actual boundary source. The second coordinate
is nonzero when the coupling and source are nonzero, despite direct locality. -/
theorem bulk_inverse_boundary (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1/4)
    (y : Plane) (hy : y 1 = 0) :
    Ring.inverse (bulk q) y =
      WithLp.toLp 2 ![y 0 / (1-q^2), -q * y 0 / (1-q^2)] := by
  have hn : 1-q^2 ≠ 0 := by nlinarith
  let z : Plane := WithLp.toLp 2 ![y 0 / (1-q^2), -q * y 0 / (1-q^2)]
  have hz : bulk q z = y := by
    apply WithLp.ofLp_injective 2
    rw [bulk, block_apply]
    funext i
    fin_cases i <;> simp [z, hy]
    · field_simp
      ring
    · ring
  rw [← hz]
  exact congrArg (fun T : Plane →L[ℝ] Plane => T z)
    (Ring.inverse_mul_cancel (bulk q) (model_bulk_unit q hq hq1))

theorem shift_range_second_zero (q d : ℝ) (y : (shift q d).range) :
    (y : Plane) 1 = 0 := by
  obtain ⟨x, hx⟩ := y.property
  rw [← hx]
  change WithLp.ofLp (block _ _ _ x) 1 = 0
  rw [block_apply]
  simp

/-- Exact scalar response, on the pin's range-space definition. -/
theorem model_response_formula (q d : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1/4)
    (hd1 : d < 1) :
    response (shift q d) (bulk q) =
      (q^2*d/((1-d)*(1-q^2))) • (1 : (shift q d).range →L[ℝ] (shift q d).range) := by
  have hqn : 1-q^2 ≠ 0 := by nlinarith
  have hdn : 1-d ≠ 0 := ne_of_gt (sub_pos.mpr hd1)
  ext y i
  change ((y : Plane) + shift q d (Ring.inverse (bulk q) (y : Plane))) i =
    (q^2*d/((1-d)*(1-q^2))) * (y : Plane) i
  rw [bulk_inverse_boundary q hq hq1 _ (shift_range_second_zero q d y)]
  change (y : Plane) i + WithLp.ofLp (shift q d _) i = _
  simp only [shift, block_apply]
  fin_cases i <;> simp [shift_range_second_zero q d y]
  field_simp
  ring

/-- The guarded response has no positive uniform gap, even though both
localized operators have fixed positive ordinary-norm gaps. -/
theorem model_response_norm_small (q d : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/4)
    (hd : 0 < d) (hd1 : d ≤ 1/4) :
    ‖response (shift q d) (bulk q)‖ < d := by
  rw [model_response_formula q d hq.le hq1 (by linarith)]
  have hq2 : 0 < 1-q^2 := by nlinarith
  have hd2 : 0 < 1-d := by linarith
  have hr : 0 ≤ q^2*d/((1-d)*(1-q^2)) := by positivity
  have hden : q^2 < (1-d)*(1-q^2) := by nlinarith [sq_nonneg q]
  have hlt : q^2*d/((1-d)*(1-q^2)) < d := by
    apply (div_lt_iff₀ (mul_pos hd2 hq2)).mpr
    nlinarith [mul_pos (sub_pos.mpr hden) hd]
  calc
    _ ≤ q^2*d/((1-d)*(1-q^2)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
      exact mul_le_of_le_one_right hr ContinuousLinearMap.norm_id_le
    _ < d := hlt

/-- Diagnostic only: even direct annihilation of the boundary range and
arbitrarily weak mixing do not justify the proposed gap transfer. -/
theorem localized_gap_and_direct_locality_insufficient
    (cap mixing : ℝ) (hcap : 0 < cap) (hmix : 0 < mixing) :
    ∃ (B D Θ : Plane →L[ℝ] Plane),
      (∀ x y, ⟪B x, y⟫ = ⟪x, B y⟫) ∧
      (∀ x y, ⟪D x, y⟫ = ⟪x, D y⟫) ∧
      (∀ x y, ⟪Θ x, y⟫ = ⟪x, Θ y⟫) ∧
      (∀ x, (3/4 : ℝ) * ‖x‖^2 ≤ ⟪x, B x⟫) ∧
      (∀ x, (1/2 : ℝ) * ‖x‖^2 ≤ ⟪x, (B-D) x⟫) ∧
      ‖D‖ < cap ∧ ‖B-1‖ < mixing ∧ D.comp Θ = 0 ∧
      IsUnit B ∧ IsUnit (B-D) ∧ IsUnit (B+Θ) ∧ ¬ IsUnit (B-D+Θ) ∧
      IsUnit (response Θ B) ∧ ¬ IsUnit (response Θ (B-D)) ∧
      ‖response Θ B‖ < cap := by
  let q := min (mixing/2) (1/4)
  let d := min (cap/2) (1/4)
  have hq : 0 < q := lt_min (by positivity) (by norm_num)
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have hq1 : q ≤ 1/4 := min_le_right _ _
  have hd1 : d ≤ 1/4 := min_le_right _ _
  have hqm : q < mixing := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdc : d < cap := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hB := model_bulk_unit q hq.le hq1
  have hC := model_corrected_unit q d hq.le hq1 hd1
  have hA := model_carrier_unit q d hq hd (by linarith)
  have hbad := model_pencil_not_unit q d (by linarith)
  exact ⟨bulk q, correction d, shift q d,
    block_symm 1 q 1, block_symm 0 0 d, block_symm _ 0 0,
    bulk_gap q hq.le hq1, corrected_gap q d hq.le hq1 hd1,
    (correction_norm d hd.le).trans_lt hdc,
    (bulk_near_identity q hq.le).trans_lt hqm,
    correction_shift_zero q d, hB, hC, hA, hbad,
    (unit_add_iff_response _ _ hB).mp hA,
    fun h => hbad ((unit_add_iff_response _ _ hC).mpr h),
    (model_response_norm_small q d hq hq1 hd hd1).trans hdc⟩

#print axioms block_not_unit
#print axioms carrier_block
#print axioms pencil_block
#print axioms model_bulk_unit
#print axioms model_corrected_unit
#print axioms model_carrier_unit
#print axioms model_pencil_not_unit
#print axioms bulk_inverse_boundary
#print axioms shift_range_second_zero
#print axioms model_response_formula
#print axioms model_response_norm_small
#print axioms localized_gap_and_direct_locality_insufficient
end AdalyFormal.Round4.Guarded.GapR2
