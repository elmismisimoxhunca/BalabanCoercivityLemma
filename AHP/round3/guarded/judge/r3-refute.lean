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
Wide-top numerical family: exact geometry and competitor only.
No spectral separation or negative headline is asserted.
-/
namespace AdalyFormal.Round3.Guarded.RefuteR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.CovariantOperators
  (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace
  (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice staircasePath)
open AdalyFormal.Balaban.FullReparamC
  (freeBond freeBond_not_mem_staircase freeBond_not_dropped freeBond_coord_zero)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonVac (iv_block pcd_clamp pcd_near pcd_self')

/-- Fine sides are (12R+16,8,8), exactly the lifted numerical family. -/
def wideLu (R : ℕ) : PeriodicLatticeExtent :=
  fun μ => if μ = 0 then 6 * R + 7 else 3

def wideTower (R : ℕ) : Tower (scaleUp 2 1 (wideLu R)) where
  Om j := if j = 0 then {x | 4 ≤ (x 0).val ∧ (x 0).val < 12 * R + 12}
    else if j = 1 then {x | 2 * R + 4 ≤ (x 0).val ∧ (x 0).val < 10 * R + 12}
    else ∅

def wideLam (R : ℕ) : Set (PeriodicLatticeSite (wideLu R)) :=
  {x | 3 * R + 4 ≤ (x 0).val ∧ (x 0).val < 3 * R + 6}

theorem wide_torus (R : ℕ) : TorusOK 2 2 (wideLu R) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro μ <;>
    by_cases h : μ = 0 <;> simp [wideLu, h] <;> omega

theorem wide_fine_size (R : ℕ) (μ : Fin 3) :
    scaleUp 2 1 (wideLu R) μ + 1 = if μ = 0 then 12 * R + 16 else 8 := by
  by_cases h : μ = 0 <;> simp [scaleUp, wideLu, h]
  all_goals omega

theorem wide_fine_bound (R : ℕ)
    (x : PeriodicLatticeSite (scaleUp 2 1 (wideLu R))) :
    (x 0).val < 12 * R + 16 := by
  have h := (x 0).isLt
  simp only [wide_fine_size] at h
  exact h

theorem zero_coord_le_pdist {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) :
    pcd (L 0 + 1) (x 0).val (y 0).val ≤ pdist x y :=
  Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)

/-- All six frozen admissibility clauses hold, not only block alignment. -/
theorem wide_admissible {R : ℕ} (hR : 2 ∣ R) :
    Admissible 2 2 R 1 (wideTower R) := by
  have hp : 4 ∣ 2 * R + 4 := by obtain ⟨t, rfl⟩ := hR; exact ⟨t + 1, by omega⟩
  have hq : 4 ∣ 10 * R + 12 := by obtain ⟨t, rfl⟩ := hR; exact ⟨5 * t + 3, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases h0 : j = 0
    · subst j
      change (2 * R + 4 ≤ (x 0).val ∧ (x 0).val < 10 * R + 12) at hx
      change 4 ≤ (x 0).val ∧ (x 0).val < 12 * R + 12
      omega
    · simp [wideTower, h0] at hx
  · intro j hj
    simp [wideTower, show j ≠ 0 by omega, show j ≠ 1 by omega]
  · intro j hj μ
    rw [wide_fine_size]
    interval_cases j <;> by_cases hμ : μ = 0 <;> simp [bigSide, hμ] <;> omega
  · intro j hj x hx y hy
    interval_cases j
    · change (4 ≤ (x 0).val ∧ (x 0).val < 12 * R + 12) at hx
      change 4 ≤ (y 0).val ∧ (y 0).val < 12 * R + 12
      exact iv_block (by norm_num : 0 < 2) (by omega) (by omega) (hy 0) hx
    · change (2 * R + 4 ≤ (x 0).val ∧ (x 0).val < 10 * R + 12) at hx
      change 2 * R + 4 ≤ (y 0).val ∧ (y 0).val < 10 * R + 12
      exact iv_block (by norm_num : 0 < 4) hp hq (hy 0) hx
  · intro j hj x hx y hy
    interval_cases j
    · change ¬ (4 ≤ (x 0).val ∧ (x 0).val < 12 * R + 12) at hx
      change (2 * R + 4 ≤ (y 0).val ∧ (y 0).val < 10 * R + 12) at hy
      have hxb := wide_fine_bound R x
      have hpd := zero_coord_le_pdist x y
      simp only [wide_fine_size] at hpd
      have hcoord : R * 2 < pcd (12 * R + 16) (x 0).val (y 0).val := by
        unfold pcd
        split_ifs <;> omega
      exact lt_of_lt_of_le hcoord hpd
    · simp [wideTower] at hy
  · intro x
    change (4 ≤ (x 0).val ∧ (x 0).val < 12 * R + 12) ↔ _
    constructor
    · intro hx
      let v := if (x 0).val < 2 * R + 4 then 2 * R + 4
        else if (x 0).val < 10 * R + 12 then (x 0).val else 10 * R + 11
      have hv : v < scaleUp 2 1 (wideLu R) 0 + 1 := by
        rw [wide_fine_size, if_pos rfl]
        dsimp [v]; split_ifs <;> omega
      refine ⟨Function.update x 0 ⟨v, hv⟩, ?_, x, fun μ => rfl, ?_⟩
      · change 2 * R + 4 ≤ v ∧ v < 10 * R + 12
        dsimp [v]; split_ifs <;> omega
      · unfold pdist
        rw [Finset.sum_eq_single (0 : Fin 3)]
        · simp only [Function.update_self]
          simp only [wide_fine_size]
          have hc := pcd_clamp (N := 12 * R + 16) (a := (x 0).val)
            (lo := 2 * R + 4) (hi := 10 * R + 12) (D := R * 2)
            (by omega) (by omega) (wide_fine_bound R x) (by omega)
          simpa [v] using hc
        · intro μ _ hμ
          rw [Function.update_of_ne hμ, pcd_self']
        · intro h
          exact (h (Finset.mem_univ _)).elim
    · rintro ⟨y, hy, z, hz, hd⟩
      change (2 * R + 4 ≤ (y 0).val ∧ (y 0).val < 10 * R + 12) at hy
      have hcoord := le_trans (zero_coord_le_pdist z y) hd
      simp only [wide_fine_size] at hcoord
      have hn := pcd_near (wide_fine_bound R z) hy
        (show R * 2 ≤ 2 * R + 4 by omega)
        (show 10 * R + 12 + R * 2 ≤ 12 * R + 16 by omega) hcoord
      have hzmem : 4 ≤ (z 0).val ∧ (z 0).val < 12 * R + 12 := by omega
      exact iv_block (by norm_num : 0 < 2) (by omega) (by omega) (hz 0).symm hzmem

def wideEmb (R : ℕ) (y : PeriodicLatticeSite (wideLu R)) :
    PeriodicLatticeSite (scaleUp 2 1 (wideLu R)) :=
  fun μ => ⟨2 * (y μ).val, by
    have h := (y μ).isLt
    by_cases hμ : μ = 0 <;>
      simp [wideLu, hμ] at h <;>
      simp [wide_fine_size, hμ] <;> omega⟩

theorem wide_lambda {R : ℕ} (hR : 2 ∣ R) :
    LambdaOK2 2 2 R 1 (wideTower R) (wideLam R) := by
  have hp : 2 ∣ 3 * R + 4 := by obtain ⟨t, rfl⟩ := hR; exact ⟨3 * t + 2, by omega⟩
  have hq : 2 ∣ 3 * R + 6 := by obtain ⟨t, rfl⟩ := hR; exact ⟨3 * t + 3, by omega⟩
  have hblock : BlockClosed 2 (wideLam R) := by
    intro x hx y hy
    exact iv_block (by norm_num) hp hq (hy 0) hx
  refine ⟨⟨hblock, wideEmb R, fun y μ => rfl, ?_, ?_⟩, ?_⟩
  · intro y hy
    change 2 * R + 4 ≤ 2 * (y 0).val ∧ 2 * (y 0).val < 10 * R + 12
    change (3 * R + 4 ≤ (y 0).val ∧ (y 0).val < 3 * R + 6) at hy
    omega
  · intro y hy z hz
    change (3 * R + 4 ≤ (y 0).val ∧ (y 0).val < 3 * R + 6) at hy
    change ¬ (2 * R + 4 ≤ 2 * (z 0).val ∧ 2 * (z 0).val < 10 * R + 12) at hz
    have hzb : (z 0).val < 6 * R + 8 := (z 0).isLt
    have hcoord : R * 2 < pcd (6 * R + 8) (y 0).val (z 0).val := by
      unfold pcd; split_ifs <;> omega
    have hpd := zero_coord_le_pdist y z
    simpa [wideLu] using lt_of_lt_of_le hcoord hpd
  · intro x hx
    let y : PeriodicLatticeSite (wideLu R) := fun μ =>
      ⟨2 * ((x μ).val / 2), lt_of_le_of_lt (Nat.mul_div_le _ _) (x μ).isLt⟩
    have hy : ∀ μ, (y μ).val = 2 * ((x μ).val / 2) := fun μ => rfl
    refine ⟨y, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_CoarseLattice]
      intro μ
      rw [hy]
      omega
    · intro z hz
      apply hblock x hx z
      rw [mem_blockOf] at hz
      intro μ
      have hh := hz μ
      rw [hy] at hh
      omega
    · rw [mem_blockOf]
      intro μ
      rw [hy]
      omega

def wideSeed (R : ℕ) : PeriodicLatticeSite (wideLu R) :=
  fun μ => ⟨if μ = 0 then 3 * R + 4 else 0, by
    by_cases hμ : μ = 0 <;> simp [wideLu, hμ]
    all_goals omega⟩

noncomputable def wideBt (R : ℕ) : Bond (wideLu R) → SuTwo :=
  Pi.single (freeBond 2 (wideSeed R)) suTwoWitness

theorem wide_competitor {R : ℕ} (hR : 2 ∣ R) :
    OnLambdaTildeIn (wideLam R) 2 (wideBt R) ∧
      OnLambdaT (wideLam R) (wideBt R) ∧ 0 < bondEnergy (wideBt R) := by
  have hdvd := (wide_torus R).1
  have hy : wideSeed R ∈ CoarseLattice (wideLu R) 2 := by
    rw [mem_CoarseLattice]
    intro μ
    obtain ⟨t, rfl⟩ := hR
    by_cases hμ : μ = 0 <;> simp [wideSeed, hμ]
    all_goals omega
  have hoff : ∀ b, b ≠ freeBond 2 (wideSeed R) → wideBt R b = 0 :=
    fun b hb => Pi.single_eq_of_ne hb _
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro y hy' x hx b hb
    apply hoff
    rintro rfl
    exact freeBond_not_mem_staircase (by norm_num) hdvd (wideSeed R) hy y hy'.1 x hx hb
  · intro b hb
    apply hoff
    rintro rfl
    obtain ⟨c, _, hc⟩ := hb
    exact freeBond_not_dropped (by norm_num) hdvd (wideSeed R) hy ⟨c, hc⟩
  · intro b hb
    by_cases hbe : b = freeBond 2 (wideSeed R)
    · exfalso
      apply hb
      subst b
      left
      have hfit : ((wideSeed R) 0).val + 2 ≤ wideLu R 0 + 1 := by
        simp [wideSeed, wideLu]; omega
      have hc := freeBond_coord_zero (wideSeed R) hfit (by norm_num : 2 ≤ 2)
      change 3 * R + 4 ≤ _ ∧ _ < 3 * R + 6
      simp [wideSeed] at hc
      omega
    · exact hoff b hbe
  · have hne : 0 < ‖wideBt R (freeBond 2 (wideSeed R))‖ ^ 2 := by
      have hsingle : wideBt R (freeBond 2 (wideSeed R)) = suTwoWitness := Pi.single_eq_same _ _
      rw [hsingle]
      have := suTwoWitness_ne_zero
      positivity
    have hs := Finset.single_le_sum (f := fun b : Bond (wideLu R) => ‖wideBt R b‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ (freeBond 2 (wideSeed R)))
    exact lt_of_lt_of_le hne hs

/-- Compiled repair of the earlier thin-top obstruction, not an in-class
spectral witness: coverage, regularity, and both spectral conditions are absent. -/
theorem wide_probe_geometry_and_competitor {R : ℕ} (hR : 2 ∣ R) :
    TorusOK 2 2 (wideLu R) ∧ Admissible 2 2 R 1 (wideTower R) ∧
    LambdaOK2 2 2 R 1 (wideTower R) (wideLam R) ∧
    OnLambdaTildeIn (wideLam R) 2 (wideBt R) ∧
    OnLambdaT (wideLam R) (wideBt R) ∧ 0 < bondEnergy (wideBt R) :=
  ⟨wide_torus R, wide_admissible hR, wide_lambda hR, wide_competitor hR⟩

#print axioms wideLu
#print axioms wideTower
#print axioms wideLam
#print axioms wide_torus
#print axioms wide_fine_size
#print axioms wide_fine_bound
#print axioms zero_coord_le_pdist
#print axioms wide_admissible
#print axioms wideEmb
#print axioms wide_lambda
#print axioms wideSeed
#print axioms wideBt
#print axioms wide_competitor
#print axioms wide_probe_geometry_and_competitor
#print axioms AdalyFormal.NonVac.iv_block
#print axioms AdalyFormal.NonVac.pcd_clamp
#print axioms AdalyFormal.NonVac.pcd_near
#print axioms AdalyFormal.NonVac.pcd_self'
#print axioms AdalyFormal.Balaban.FullReparamC.freeBond
#print axioms AdalyFormal.Balaban.FullReparamC.freeBond_coord_zero
#print axioms AdalyFormal.Balaban.FullReparamC.freeBond_not_mem_staircase
#print axioms AdalyFormal.Balaban.FullReparamC.freeBond_not_dropped
#print axioms AdalyFormal.Balaban.CovariantOperators.suTwoWitness
#print axioms AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero

end AdalyFormal.Round3.Guarded.RefuteR2

namespace AdalyFormal.Round3.Guarded.RefuteR3

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round3.Guarded.RefuteR2
open AdalyFormal.NonVac (clamp1D coord_box_sub coord_box_in isClassCube_of)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- On this rectangular torus, the short transverse directions are entirely
covered by every factor-12 box; only the longitudinal coordinate needs clamping. -/
theorem wide_box {R s t : ℕ} (hs : 1 ≤ s) (ht : s ∣ t)
    (hfit : t + 12 * s ≤ 12 * R + 16) :
    ∃ z : PeriodicLatticeSite (scaleUp 2 1 (wideLu R)), GridCorner s z ∧
      ∀ y, y ∈ siteBox z (12 * s) ↔ t ≤ (y 0).val ∧ (y 0).val < t + 12 * s := by
  let z : PeriodicLatticeSite (scaleUp 2 1 (wideLu R)) := fun μ =>
    ⟨if μ = 0 then t else 0, by rw [wide_fine_size]; split_ifs <;> omega⟩
  have hz0 : (z 0).val = t := by simp [z]
  refine ⟨z, ?_, ?_⟩
  · intro μ
    by_cases hμ : μ = 0
    · subst μ; simpa [hz0] using Nat.mod_eq_zero_of_dvd ht
    · simp [z, hμ]
  · intro y
    constructor
    · intro hy
      have hy0 := hy 0
      simp only [wide_fine_size, hz0] at hy0
      exact coord_box_sub hfit (wide_fine_bound R y) hy0
    · intro hy μ
      by_cases hμ : μ = 0
      · subst μ
        simp only [wide_fine_size, hz0]
        exact coord_box_in hfit hy.1 hy.2
      · have hz : (z μ).val = 0 := by simp [z, hμ]
        simp only [wide_fine_size, if_neg hμ, hz]
        have hm := Nat.mod_lt ((y μ).val + 8 - 0) (by norm_num : 0 < 8)
        omega

/-- A longitudinal window, including the possible successor, is contained in
one actual class cube. All level and uniqueness obligations are retained. -/
theorem wide_region_cube {R j lo hi v w : ℕ} (hR : 2 ∣ R) (hj : j ≤ 1)
    (hlo : bigSide 2 2 j ∣ lo) (hhi : bigSide 2 2 j ∣ hi)
    (hwid : lo + 12 * bigSide 2 2 j ≤ hi) (hhiN : hi ≤ 12 * R + 16)
    (hvlo : lo ≤ v) (hvw : v ≤ w) (hw1 : w ≤ v + 1) (hwhi : w < hi)
    (hreg : ∀ y : PeriodicLatticeSite (scaleUp 2 1 (wideLu R)),
      lo ≤ (y 0).val → (y 0).val < hi →
      y ∈ towerBj (wideTower R) j ∪ towerBj (wideTower R) (j + 1))
    (hwit : ∃ u, v ≤ u ∧ u ≤ w ∧ ∀ y : PeriodicLatticeSite (scaleUp 2 1 (wideLu R)),
      (y 0).val = u → y ∈ towerBj (wideTower R) j) :
    ∃ sites, IsClassCube 2 2 12 1 (wideTower R) sites j ∧
      ∀ y : PeriodicLatticeSite (scaleUp 2 1 (wideLu R)),
        v ≤ (y 0).val → (y 0).val ≤ w → y ∈ sites := by
  have hs : 0 < bigSide 2 2 j := by dsimp [bigSide]; positivity
  obtain ⟨t, ht, hlot, hthi, htv, hwt⟩ := clamp1D hs hlo hhi hwid hvlo hvw hw1 hwhi
  obtain ⟨z, hz, hbox⟩ := wide_box (R := R) hs ht (by omega)
  refine ⟨siteBox z (12 * bigSide 2 2 j), isClassCube_of (wide_admissible hR).1
    ⟨hj, ⟨z, hz, rfl⟩, ?_, ?_⟩, ?_⟩
  · intro y hy
    have := (hbox y).mp hy
    exact hreg y (by omega) (by omega)
  · obtain ⟨u, hvu, huw, hu⟩ := hwit
    let y : PeriodicLatticeSite (scaleUp 2 1 (wideLu R)) := fun μ =>
      ⟨if μ = 0 then u else 0, by rw [wide_fine_size]; split_ifs <;> omega⟩
    have hy : (y 0).val = u := by simp [y]
    exact ⟨y, (hbox y).mpr (by rw [hy]; omega), hu y hy⟩
  · intro y hy1 hy2
    exact (hbox y).mpr (by omega)

theorem wide_cube_neighborhood {R : ℕ} (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    (x : PeriodicLatticeSite (scaleUp 2 1 (wideLu R))) (hx : x ∈ (wideTower R).Om 0) :
    ∃ sites j, IsClassCube 2 2 12 1 (wideTower R) sites j ∧
      ∀ y : PeriodicLatticeSite (scaleUp 2 1 (wideLu R)),
        (x 0).val ≤ (y 0).val → (y 0).val ≤ (x 0).val + 1 →
        y ∈ (wideTower R).Om 0 → y ∈ sites := by
  change (4 ≤ (x 0).val ∧ (x 0).val < 12 * R + 12) at hx
  have hp : 4 ∣ 2 * R + 4 := by obtain ⟨t, rfl⟩ := hR; exact ⟨t + 1, by omega⟩
  have hq : 4 ∣ 10 * R + 12 := by obtain ⟨t, rfl⟩ := hR; exact ⟨5 * t + 3, by omega⟩
  by_cases hcore : 2 * R + 4 ≤ (x 0).val ∧ (x 0).val + 1 < 10 * R + 12
  · obtain ⟨sites, hc, hall⟩ := wide_region_cube (j := 1) (lo := 2 * R + 4)
      (hi := 10 * R + 12) (v := (x 0).val) (w := (x 0).val + 1)
      hR (by omega) hp hq (by dsimp [bigSide]; omega) (by omega)
      hcore.1 (by omega) le_rfl hcore.2
      (by intro y hy1 hy2; left; simp [towerBj, wideTower]; omega)
      ⟨(x 0).val, le_rfl, by omega, by intro y hy; simp [towerBj, wideTower]; omega⟩
    exact ⟨sites, 1, hc, fun y hy1 hy2 _ => hall y hy1 hy2⟩
  · have hreg : ∀ y : PeriodicLatticeSite (scaleUp 2 1 (wideLu R)),
        4 ≤ (y 0).val → (y 0).val < 12 * R + 12 →
        y ∈ towerBj (wideTower R) 0 ∪ towerBj (wideTower R) 1 := by
      intro y hy1 hy2
      by_cases h : 2 * R + 4 ≤ (y 0).val ∧ (y 0).val < 10 * R + 12
      · right; simpa [towerBj, wideTower] using h
      · left; simp [towerBj, wideTower]; omega
    have hwit : ∃ u, (x 0).val ≤ u ∧ u ≤ min ((x 0).val + 1) (12 * R + 11) ∧
        ∀ y : PeriodicLatticeSite (scaleUp 2 1 (wideLu R)), (y 0).val = u →
          y ∈ towerBj (wideTower R) 0 := by
      by_cases hleft : (x 0).val < 2 * R + 4
      · refine ⟨(x 0).val, le_rfl, by omega, ?_⟩
        intro y hy; simp [towerBj, wideTower]; omega
      · refine ⟨max (x 0).val (10 * R + 12), by omega, by omega, ?_⟩
        intro y hy; simp [towerBj, wideTower]; omega
    obtain ⟨sites, hc, hall⟩ := wide_region_cube (j := 0) (lo := 4)
      (hi := 12 * R + 12) (v := (x 0).val) (w := min ((x 0).val + 1) (12 * R + 11))
      hR (by omega) (by norm_num [bigSide]) (by simp [bigSide]; omega)
      (by dsimp [bigSide]; omega) (by omega) hx.1 (by omega) (by omega) (by omega)
      hreg hwit
    refine ⟨sites, 0, hc, ?_⟩
    intro y hy1 hy2 hy
    change (4 ≤ (y 0).val ∧ (y 0).val < 12 * R + 12) at hy
    exact hall y hy1 (by omega)

/-- An explicit level-zero cube can be anchored by either end of the interval,
not necessarily by the plaquette's base point. This covers the small collars. -/
theorem wide_zero_cube {R t : ℕ} (hR : 2 ∣ R) (ht : 2 ∣ t)
    (hlo : 4 ≤ t) (hhi : t + 24 ≤ 12 * R + 12)
    (hw : t < 2 * R + 4 ∨ 10 * R + 12 ≤ t + 23) :
    ∃ sites, IsClassCube 2 2 12 1 (wideTower R) sites 0 ∧
      ∀ y : PeriodicLatticeSite (scaleUp 2 1 (wideLu R)),
        t ≤ (y 0).val → (y 0).val < t + 24 → y ∈ sites := by
  obtain ⟨z, hz, hbox⟩ := wide_box (R := R) (s := 2) (by omega) ht (by omega)
  have hreg : ∀ y : PeriodicLatticeSite (scaleUp 2 1 (wideLu R)),
      t ≤ (y 0).val → (y 0).val < t + 24 →
      y ∈ towerBj (wideTower R) 0 ∪ towerBj (wideTower R) 1 := by
    intro y h1 h2
    by_cases h : 2 * R + 4 ≤ (y 0).val ∧ (y 0).val < 10 * R + 12
    · right; simpa [towerBj, wideTower] using h
    · left; simp [towerBj, wideTower]; omega
  have hwit : ∃ u, t ≤ u ∧ u < t + 24 ∧
      ¬ (2 * R + 4 ≤ u ∧ u < 10 * R + 12) := by
    rcases hw with h | h
    · exact ⟨t, by omega, by omega, by omega⟩
    · exact ⟨t + 23, by omega, by omega, by omega⟩
  refine ⟨siteBox z 24, isClassCube_of (wide_admissible hR).1
    ⟨by omega, ⟨z, hz, rfl⟩, ?_, ?_⟩, ?_⟩
  · intro y hy
    have := (hbox y).mp hy
    exact hreg y this.1 this.2
  · obtain ⟨u, hut, htu, hu⟩ := hwit
    let y : PeriodicLatticeSite (scaleUp 2 1 (wideLu R)) := fun μ =>
      ⟨if μ = 0 then u else 0, by rw [wide_fine_size]; split_ifs <;> omega⟩
    have hy : (y 0).val = u := by simp [y]
    refine ⟨y, (hbox y).mpr (by rw [hy]; omega), ?_⟩
    simp [towerBj, wideTower]; rw [hy]; omega
  · intro y h1 h2; exact (hbox y).mpr ⟨h1, h2⟩

theorem wide_cube_neighborhood_all {R : ℕ} (hR : 2 ∣ R) (hR2 : 2 ≤ R)
    (x : PeriodicLatticeSite (scaleUp 2 1 (wideLu R))) (hx : x ∈ (wideTower R).Om 0) :
    ∃ sites j, IsClassCube 2 2 12 1 (wideTower R) sites j ∧
      ∀ y : PeriodicLatticeSite (scaleUp 2 1 (wideLu R)),
        (x 0).val ≤ (y 0).val → (y 0).val ≤ (x 0).val + 1 →
        y ∈ (wideTower R).Om 0 → y ∈ sites := by
  by_cases hR6 : 6 ≤ R
  · exact wide_cube_neighborhood hR hR6 x hx
  have hcases : R = 2 ∨ R = 4 := by omega
  rcases hcases with rfl | rfl
  · change (4 ≤ (x 0).val ∧ (x 0).val < 36) at hx
    by_cases hl : (x 0).val < 27
    · obtain ⟨sites, hc, hall⟩ := wide_zero_cube (R := 2) (t := 4)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      refine ⟨sites, 0, hc, ?_⟩
      intro y h1 h2 _; exact hall y (by omega) (by omega)
    · obtain ⟨sites, hc, hall⟩ := wide_zero_cube (R := 2) (t := 12)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      refine ⟨sites, 0, hc, ?_⟩
      intro y h1 h2 hy
      change (4 ≤ (y 0).val ∧ (y 0).val < 36) at hy
      exact hall y (by omega) hy.2
  · change (4 ≤ (x 0).val ∧ (x 0).val < 60) at hx
    by_cases h1 : (x 0).val < 27
    · obtain ⟨sites, hc, hall⟩ := wide_zero_cube (R := 4) (t := 4)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      refine ⟨sites, 0, hc, ?_⟩
      intro y hy1 hy2 _; exact hall y (by omega) (by omega)
    · by_cases h2 : (x 0).val < 33
      · obtain ⟨sites, hc, hall⟩ := wide_zero_cube (R := 4) (t := 10)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        refine ⟨sites, 0, hc, ?_⟩
        intro y hy1 hy2 _; exact hall y (by omega) (by omega)
      · by_cases h3 : (x 0).val < 53
        · obtain ⟨sites, hc, hall⟩ := wide_zero_cube (R := 4) (t := 30)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          refine ⟨sites, 0, hc, ?_⟩
          intro y hy1 hy2 _; exact hall y (by omega) (by omega)
        · obtain ⟨sites, hc, hall⟩ := wide_zero_cube (R := 4) (t := 36)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          refine ⟨sites, 0, hc, ?_⟩
          intro y hy1 hy2 hy
          change (4 ≤ (y 0).val ∧ (y 0).val < 60) at hy
          exact hall y (by omega) hy.2

theorem wide_shift_zero (R : ℕ)
    (x : PeriodicLatticeSite (scaleUp 2 1 (wideLu R))) (μ : Fin 3) :
    ((periodicLatticeShift x μ) 0).val =
      if μ = 0 then ((x 0).val + 1) % (12 * R + 16) else (x 0).val := by
  by_cases h : μ = 0
  · subst μ
    simp only [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one',
      wide_fine_size, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega : 1 < 12 * R + 16)]
  · simp [periodicLatticeShift, Function.update_of_ne (Ne.symm h), h]

/-- Both frozen coverage clauses hold for every even R at least two. -/
theorem wide_coverage {R : ℕ} (hR : 2 ∣ R) (hR2 : 2 ≤ R) :
    CoversOm0p 2 2 12 1 (wideTower R) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨sites, j, hc, hall⟩ := wide_cube_neighborhood_all hR hR2 x hx
    exact ⟨sites, j, hc, hall x le_rfl (by omega) hx⟩
  · intro p hp
    have hmem : ∀ e : PeriodicLatticeEdge (scaleUp 2 1 (wideLu R)),
        e ∈ periodicPlaquetteBoundaryEdges p ↔
        e = (p.1, p.2.1.1) ∨ e = (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∨
        e = (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∨ e = (p.1, p.2.1.2) := by
      intro e; simp [periodicPlaquetteBoundaryEdges]
    have hx := (hp _ ((hmem _).mpr (Or.inl rfl))).1
    obtain ⟨sites, j, hc, hall⟩ := wide_cube_neighborhood_all hR hR2 p.1 hx
    have hxb : (p.1 0).val + 2 < 12 * R + 16 := by
      change (4 ≤ (p.1 0).val ∧ (p.1 0).val < 12 * R + 12) at hx; omega
    have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
    have ha (μ : Fin 3) :
        (p.1 0).val ≤ ((periodicLatticeShift p.1 μ) 0).val ∧
        ((periodicLatticeShift p.1 μ) 0).val ≤ (p.1 0).val + 1 := by
      rw [wide_shift_zero]; split_ifs
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
      · omega
    have hab (μ ν : Fin 3) (hne : μ ≠ ν) :
        (p.1 0).val ≤ ((periodicLatticeShift (periodicLatticeShift p.1 μ) ν) 0).val ∧
        ((periodicLatticeShift (periodicLatticeShift p.1 μ) ν) 0).val ≤ (p.1 0).val + 1 := by
      rw [wide_shift_zero, wide_shift_zero]
      split_ifs <;> simp_all only [Nat.mod_eq_of_lt (by omega : (p.1 0).val + 1 < 12 * R + 16)] <;> omega
    refine ⟨sites, j, hc, ?_⟩
    intro e he
    obtain ⟨h1,h2⟩ := hp e he
    rcases (hmem e).mp he with rfl | rfl | rfl | rfl
    · exact ⟨hall p.1 le_rfl (Nat.le_succ _) h1, hall _ (ha _).1 (ha _).2 h2⟩
    · exact ⟨hall _ (ha _).1 (ha _).2 h1, hall _ (hab _ _ hne).1 (hab _ _ hne).2 h2⟩
    · exact ⟨hall _ (ha _).1 (ha _).2 h1, hall _ (hab _ _ hne.symm).1 (hab _ _ hne.symm).2 h2⟩
    · exact ⟨hall p.1 le_rfl (Nat.le_succ _) h1, hall _ (ha _).1 (ha _).2 h2⟩

#print axioms wide_box
#print axioms wide_region_cube
#print axioms wide_cube_neighborhood
#print axioms wide_zero_cube
#print axioms wide_cube_neighborhood_all
#print axioms wide_shift_zero
#print axioms wide_coverage
#print axioms AdalyFormal.NonVac.clamp1D
#print axioms AdalyFormal.NonVac.coord_box_in
#print axioms AdalyFormal.NonVac.coord_box_sub
#print axioms AdalyFormal.NonVac.isClassCube_of

/-- The single-defect profile used in the new Fourier-sector probe, repeated
with transverse period two on the lifted torus. -/
def widePattern (R : ℕ) (e : Bond (scaleUp 2 1 (wideLu R))) : Prop :=
  (e.1 0).val = 2 * R + 4 ∧ (e.1 1).val % 2 = 0 ∧ (e.1 2).val % 2 = 0 ∧ e.2 = 1

open Classical in
noncomputable def wideU (R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (wideLu R))) :
    LinkCfg (scaleUp 2 1 (wideLu R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((wideTower R).Om 0) then V e
    else Ug (if widePattern R e then ε else 0)

/-- Regularity constrains the interior amplitude but not the exterior links. -/
theorem wide_regular {R : ℕ} (hR : 2 ∣ R) {α ε : ℝ} (hα : 0 < α)
    (hε : |ε| ≤ α / 80) (V : LinkCfg (scaleUp 2 1 (wideLu R))) :
    PerCubeRegular2 2 2 12 1 (wideTower R) α ((2 : ℝ) ^ 1)⁻¹ (wideU R ε V) := by
  classical
  let χ : Bond (scaleUp 2 1 (wideLu R)) → ℝ := fun e => if widePattern R e then 2 * ε else 0
  have hχ : ∀ e, |χ e| ≤ α * (((2 : ℝ) ^ 1)⁻¹) ^ 2 / 10 := by
    intro e
    dsimp [χ]
    split_ifs
    · rw [abs_mul]; norm_num; linarith
    · norm_num; positivity
  apply perCubeRegular2_congr (wide_admissible hR).1 (U := Ufield (((2 : ℝ) ^ 1)⁻¹) χ)
  · intro e he
    have hz : e ∉ AdalyFormal.D1Literal.Zb ((wideTower R).Om 0) := fun h => h.1 he.1
    simp only [wideU, if_neg hz, Ufield, χ]
    split_ifs <;> congr 1 <;> norm_num
    ring
  · exact ufield_perCubeRegular2 (by norm_num) (by norm_num) (by norm_num) _ hα χ hχ

def wideDefectSite (R : ℕ) : PeriodicLatticeSite (scaleUp 2 1 (wideLu R)) :=
  fun μ => ⟨if μ = 0 then 2 * R + 4 else 0, by rw [wide_fine_size]; split_ifs <;> omega⟩

theorem wideU_nonflat (R : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (V : LinkCfg (scaleUp 2 1 (wideLu R))) :
    ∃ e : Bond (scaleUp 2 1 (wideLu R)), e.1 ∈ (wideTower R).Om 0 ∧ wideU R ε V e ≠ 1 := by
  let e : Bond (scaleUp 2 1 (wideLu R)) := (wideDefectSite R, 1)
  have he : e.1 ∈ (wideTower R).Om 0 := by
    change 4 ≤ _ ∧ _ < 12 * R + 12
    simp [e, wideDefectSite]; omega
  have hz : e ∉ AdalyFormal.D1Literal.Zb ((wideTower R).Om 0) := fun h => h.1 he
  have hp : widePattern R e := by
    simp [widePattern, e, wideDefectSite, show (2 : Fin 3) ≠ 0 by decide]
  refine ⟨e, he, ?_⟩
  simpa only [wideU, if_neg hz, if_pos hp] using Ug_ne_one hε0 hε1

/-- Complete class, geometry, cap, competitor and base-nonidentity certificate
for the single-defect family. No unit or singularity condition is asserted. -/
theorem wide_in_class_nonflat_competitor {R : ℕ} (hR : 2 ∣ R) (hR2 : 2 ≤ R)
    {a₀ : ℝ} (ha₀ : 0 < a₀) (V : LinkCfg (scaleUp 2 1 (wideLu R))) :
    ∃ α ε : ℝ, 0 < α ∧ (12 : ℝ) * 2 * α ≤ a₀ ∧ 0 < ε ∧ ε < 1 ∧
      TorusOK 2 2 (wideLu R) ∧ Admissible 2 2 R 1 (wideTower R) ∧
      LambdaOK2 2 2 R 1 (wideTower R) (wideLam R) ∧
      ClassCoupled 2 2 12 1 (wideTower R) α ((2 : ℝ) ^ 1)⁻¹ (wideU R ε V) ∧
      OnLambdaTildeIn (wideLam R) 2 (wideBt R) ∧ OnLambdaT (wideLam R) (wideBt R) ∧
      0 < bondEnergy (wideBt R) ∧
      ∃ e : Bond (scaleUp 2 1 (wideLu R)), e.1 ∈ (wideTower R).Om 0 ∧ wideU R ε V e ≠ 1 := by
  let α : ℝ := min (a₀ / 24) 1 / 2
  have hα : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 / 2 := by dsimp [α]; linarith [min_le_right (a₀ / 24) 1]
  have hcap : (12 : ℝ) * 2 * α ≤ a₀ := by
    dsimp [α]; linarith [min_le_left (a₀ / 24) 1]
  have hε0 : 0 < α / 160 := by positivity
  have hε1 : α / 160 < 1 := by linarith
  have heps : |α / 160| ≤ α / 80 := by rw [abs_of_pos hε0]; linarith
  obtain ⟨hB1, hB2, hE⟩ := wide_competitor hR
  exact ⟨α, α / 160, hα, hcap, hε0, hε1, wide_torus R, wide_admissible hR,
    wide_lambda hR, ⟨wide_coverage hR hR2, wide_regular hR hα heps V⟩,
    hB1, hB2, hE, wideU_nonflat R hε0 hε1 V⟩

#print axioms widePattern
#print axioms wideU
#print axioms wide_regular
#print axioms wideDefectSite
#print axioms wideU_nonflat
#print axioms wide_in_class_nonflat_competitor
#print axioms AdalyFormal.StatementLaneG.perCubeRegular2_congr
#print axioms AdalyFormal.StatementLane2.ufield_perCubeRegular2
#print axioms AdalyFormal.StatementLane2.Ug_ne_one
#print axioms AdalyFormal.StatementLane2.Ug
#print axioms AdalyFormal.StatementLane2.Ufield
#print axioms AdalyFormal.D1Literal.Zb

end AdalyFormal.Round3.Guarded.RefuteR3
