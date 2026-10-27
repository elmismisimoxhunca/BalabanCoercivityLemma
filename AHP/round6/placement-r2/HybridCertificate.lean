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

/-!
Round 4: dilation of the round-3 single-defect family. The scale q is positive,
M = 2*q, ell = 2, k = 1. This section proves nonspectral obligations only.
-/
namespace AdalyFormal.Round4.Guarded.RefuteR1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round3.Guarded.RefuteR2 (zero_coord_le_pdist)
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

theorem dil_torus {q : ℕ} (hq : 0 < q) (R : ℕ) : TorusOK 2 (2*q) (dilLu q R) := by
  have hd : ∀ μ : Fin 3, 2*q ∣ dilLu q R μ + 1 := by
    intro μ
    rw [dil_unit_size hq]
    by_cases h : μ = 0
    · rw [if_pos h]; exact ⟨3*R+4, by ring⟩
    · rw [if_neg h]; exact ⟨2, by ring⟩
  refine ⟨fun μ => dvd_trans (dvd_mul_right 2 q) (hd μ), ?_, hd⟩
  intro μ
  rw [dil_unit_size hq]
  split_ifs <;> omega

theorem dil_admissible {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) :
    Admissible 2 (2*q) R 1 (dilTower q R) := by
  have hp : 4*q ∣ 2*(R*q)+4*q := by
    obtain ⟨t, rfl⟩ := hR; exact ⟨t+1, by ring⟩
  have hq' : 4*q ∣ 10*(R*q)+12*q := by
    obtain ⟨t, rfl⟩ := hR; exact ⟨5*t+3, by ring⟩
  have hlo : 2*q ∣ 4*q := ⟨2, by ring⟩
  have hhi : 2*q ∣ 12*(R*q)+12*q := ⟨6*R+6, by ring⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases h0 : j = 0
    · subst j
      change (2*(R*q)+4*q ≤ (x 0).val ∧ (x 0).val < 10*(R*q)+12*q) at hx
      change 4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q
      omega
    · simp [dilTower, h0] at hx
  · intro j hj
    simp [dilTower, show j ≠ 0 by omega, show j ≠ 1 by omega]
  · intro j hj μ
    rw [dil_fine_size hq]
    interval_cases j <;> by_cases hμ : μ = 0 <;> simp only [bigSide, pow_zero, pow_one, mul_one, hμ, ↓reduceIte]
    · exact ⟨6*R+8, by ring⟩
    · exact ⟨4, by ring⟩
    · exact ⟨3*R+4, by ring⟩
    · exact ⟨2, by ring⟩
  · intro j hj x hx y hy
    interval_cases j
    · change (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) at hx
      change 4*q ≤ (y 0).val ∧ (y 0).val < 12*(R*q)+12*q
      apply iv_block (by omega : 0 < 2*q) hlo hhi _ hx
      simpa [bigSide] using hy 0
    · change (2*(R*q)+4*q ≤ (x 0).val ∧ (x 0).val < 10*(R*q)+12*q) at hx
      change 2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q
      apply iv_block (by omega : 0 < 4*q) hp hq' _ hx
      simpa [bigSide, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hy 0
  · intro j hj x hx y hy
    interval_cases j
    · change ¬ (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) at hx
      change (2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q) at hy
      have hxb := dil_fine_bound hq R x
      have hpd := zero_coord_le_pdist x y
      simp only [dil_fine_size hq, ↓reduceIte] at hpd
      have hcoord : 2*(R*q) < pcd (12*(R*q)+16*q) (x 0).val (y 0).val := by
        unfold pcd; split_ifs <;> omega
      have heq : R * bigSide (2*q) 2 0 = 2*(R*q) := by simp [bigSide]; ring
      rw [heq]; exact lt_of_lt_of_le hcoord hpd
    · simp [dilTower] at hy
  · intro x
    change (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) ↔ _
    have hrm : R*(2*q) = 2*(R*q) := by ring
    constructor
    · intro hx
      let v := if (x 0).val < 2*(R*q)+4*q then 2*(R*q)+4*q
        else if (x 0).val < 10*(R*q)+12*q then (x 0).val else 10*(R*q)+12*q-1
      have hv : v < scaleUp 2 1 (dilLu q R) 0 + 1 := by
        rw [dil_fine_size hq, if_pos rfl]
        dsimp [v]; split_ifs <;> omega
      refine ⟨Function.update x 0 ⟨v, hv⟩, ?_, x, fun μ => rfl, ?_⟩
      · change 2*(R*q)+4*q ≤ v ∧ v < 10*(R*q)+12*q
        dsimp [v]; split_ifs <;> omega
      · unfold pdist
        rw [Finset.sum_eq_single (0 : Fin 3)]
        · simp only [Function.update_self, dil_fine_size hq, ↓reduceIte, hrm]
          have hc := pcd_clamp (N := 12*(R*q)+16*q) (a := (x 0).val)
            (lo := 2*(R*q)+4*q) (hi := 10*(R*q)+12*q) (D := 2*(R*q))
            (by omega) (by omega) (dil_fine_bound hq R x) (by omega)
          simpa [v] using hc
        · intro μ _ hμ; rw [Function.update_of_ne hμ, pcd_self']
        · intro h; exact (h (Finset.mem_univ _)).elim
    · rintro ⟨y, hy, z, hz, hd⟩
      change (2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q) at hy
      have hcoord := le_trans (zero_coord_le_pdist z y) hd
      simp only [dil_fine_size hq, ↓reduceIte, hrm] at hcoord
      have hn := pcd_near (dil_fine_bound hq R z) hy
        (show 2*(R*q) ≤ 2*(R*q)+4*q by omega)
        (show 10*(R*q)+12*q+2*(R*q) ≤ 12*(R*q)+16*q by omega) hcoord
      have hzmem : 4*q ≤ (z 0).val ∧ (z 0).val < 12*(R*q)+12*q := by omega
      exact iv_block (by omega : 0 < 2*q) hlo hhi (hz 0).symm hzmem

def dilEmb {q : ℕ} (hq : 0 < q) (R : ℕ) (y : PeriodicLatticeSite (dilLu q R)) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  fun μ => ⟨2 * (y μ).val, by
    have h := (y μ).isLt
    simp only [dil_unit_size hq] at h
    rw [dil_fine_size hq]
    split_ifs at * <;> omega⟩

theorem dil_lambda {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) :
    LambdaOK2 2 (2*q) R 1 (dilTower q R) (dilLam q R) := by
  have hp : 2*q ∣ 3*(R*q)+4*q := by obtain ⟨t, rfl⟩ := hR; exact ⟨3*t+2, by ring⟩
  have hq' : 2*q ∣ 3*(R*q)+6*q := by obtain ⟨t, rfl⟩ := hR; exact ⟨3*t+3, by ring⟩
  have hblock : BlockClosed (2*q) (dilLam q R) := by
    intro x hx y hy; exact iv_block (by omega) hp hq' (hy 0) hx
  have hblock2 : BlockClosed 2 (dilLam q R) := by
    intro x hx y hy
    exact iv_block (by omega) (dvd_trans (dvd_mul_right 2 q) hp)
      (dvd_trans (dvd_mul_right 2 q) hq') (hy 0) hx
  refine ⟨⟨hblock, dilEmb hq R, fun y μ => rfl, ?_, ?_⟩, ?_⟩
  · intro y hy
    change 2*(R*q)+4*q ≤ 2*(y 0).val ∧ 2*(y 0).val < 10*(R*q)+12*q
    change (3*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 3*(R*q)+6*q) at hy
    omega
  · intro y hy z hz
    change (3*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 3*(R*q)+6*q) at hy
    change ¬ (2*(R*q)+4*q ≤ 2*(z 0).val ∧ 2*(z 0).val < 10*(R*q)+12*q) at hz
    have hzb := (z 0).isLt
    simp only [dil_unit_size hq, ↓reduceIte] at hzb
    have hcoord : 2*(R*q) < pcd (6*(R*q)+8*q) (y 0).val (z 0).val := by
      unfold pcd; split_ifs <;> omega
    have hpd := zero_coord_le_pdist y z
    simp only [dil_unit_size hq, ↓reduceIte] at hpd
    have hrm : R*(2*q) = 2*(R*q) := by ring
    rw [hrm]; exact lt_of_lt_of_le hcoord hpd
  · intro x hx
    let y : PeriodicLatticeSite (dilLu q R) := fun μ =>
      ⟨2*((x μ).val/2), lt_of_le_of_lt (Nat.mul_div_le _ _) (x μ).isLt⟩
    have hy : ∀ μ, (y μ).val = 2*((x μ).val/2) := fun μ => rfl
    refine ⟨y, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_CoarseLattice]; intro μ; rw [hy]; omega
    · intro z hz
      apply hblock2 x hx z
      rw [mem_blockOf] at hz
      intro μ; have hh := hz μ; rw [hy] at hh; omega
    · rw [mem_blockOf]; intro μ; rw [hy]; omega

def dilSeed {q : ℕ} (hq : 0 < q) (R : ℕ) : PeriodicLatticeSite (dilLu q R) :=
  fun μ => ⟨if μ = 0 then 3*(R*q)+4*q else 0, by
    rw [dil_unit_size hq]; split_ifs <;> omega⟩

noncomputable def dilBt {q : ℕ} (hq : 0 < q) (R : ℕ) : Bond (dilLu q R) → SuTwo :=
  Pi.single (freeBond 2 (dilSeed hq R)) suTwoWitness

theorem dil_competitor {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) :
    OnLambdaTildeIn (dilLam q R) 2 (dilBt hq R) ∧
      OnLambdaT (dilLam q R) (dilBt hq R) ∧ 0 < bondEnergy (dilBt hq R) := by
  have hdvd := (dil_torus hq R).1
  have hy : dilSeed hq R ∈ CoarseLattice (dilLu q R) 2 := by
    rw [mem_CoarseLattice]; intro μ
    by_cases hμ : μ = 0
    · subst μ
      change (3*(R*q)+4*q) % 2 = 0
      apply Nat.mod_eq_zero_of_dvd
      obtain ⟨t, rfl⟩ := hR
      exact ⟨3*t*q+2*q, by ring⟩
    · simp [dilSeed, hμ]
  have hoff : ∀ b, b ≠ freeBond 2 (dilSeed hq R) → dilBt hq R b = 0 :=
    fun b hb => Pi.single_eq_of_ne hb _
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro y hy' x hx b hb
    apply hoff; rintro rfl
    exact freeBond_not_mem_staircase (by norm_num) hdvd (dilSeed hq R) hy y hy'.1 x hx hb
  · intro b hb
    apply hoff; rintro rfl
    obtain ⟨c, _, hc⟩ := hb
    exact freeBond_not_dropped (by norm_num) hdvd (dilSeed hq R) hy ⟨c, hc⟩
  · intro b hb
    by_cases hbe : b = freeBond 2 (dilSeed hq R)
    · exfalso; apply hb; subst b; left
      have hfit : ((dilSeed hq R) 0).val + 2 ≤ dilLu q R 0 + 1 := by
        simp only [dilSeed, ↓reduceIte, dil_unit_size hq]; omega
      have hc := freeBond_coord_zero (dilSeed hq R) hfit (by norm_num : 2 ≤ 2)
      change 3*(R*q)+4*q ≤ _ ∧ _ < 3*(R*q)+6*q
      simp only [dilSeed, ↓reduceIte] at hc
      omega
    · exact hoff b hbe
  · have hne : 0 < ‖dilBt hq R (freeBond 2 (dilSeed hq R))‖ ^ 2 := by
      have hsingle : dilBt hq R (freeBond 2 (dilSeed hq R)) = suTwoWitness := Pi.single_eq_same _ _
      rw [hsingle]; have := suTwoWitness_ne_zero; positivity
    have hs := Finset.single_le_sum (f := fun b : Bond (dilLu q R) => ‖dilBt hq R b‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ (freeBond 2 (dilSeed hq R)))
    exact lt_of_lt_of_le hne hs

#print axioms dilLu
#print axioms dilTower
#print axioms dilLam
#print axioms dil_unit_size
#print axioms dil_fine_size
#print axioms dil_fine_bound
#print axioms dil_torus
#print axioms dil_admissible
#print axioms dilEmb
#print axioms dil_lambda
#print axioms dilSeed
#print axioms dilBt
#print axioms dil_competitor

end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round4.Guarded.RefuteR1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.NonVac (clamp1D coord_box_sub coord_box_in isClassCube_of)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- The transverse circumference is shorter than every class box. -/
theorem dil_box {q R s t : ℕ} (hq : 0 < q) (hqs : q ≤ s) (ht : s ∣ t)
    (hfit : t + 12*s ≤ 12*(R*q)+16*q) :
    ∃ z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)), GridCorner s z ∧
      ∀ y, y ∈ siteBox z (12*s) ↔ t ≤ (y 0).val ∧ (y 0).val < t + 12*s := by
  let z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) := fun μ =>
    ⟨if μ = 0 then t else 0, by rw [dil_fine_size hq]; split_ifs <;> omega⟩
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
      simp only [dil_fine_size hq, ↓reduceIte, hz0] at hy0
      exact coord_box_sub hfit (dil_fine_bound hq R y) hy0
    · intro hy μ
      by_cases hμ : μ = 0
      · subst μ
        simp only [dil_fine_size hq, ↓reduceIte, hz0]
        exact coord_box_in hfit hy.1 hy.2
      · have hz : (z μ).val = 0 := by simp [z, hμ]
        simp only [dil_fine_size hq, if_neg hμ, hz]
        have hm := Nat.mod_lt ((y μ).val + 8*q - 0) (by omega : 0 < 8*q)
        omega

theorem dil_region_cube {q R j lo hi v w : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hj : j ≤ 1)
    (hlo : bigSide (2*q) 2 j ∣ lo) (hhi : bigSide (2*q) 2 j ∣ hi)
    (hwid : lo + 12*bigSide (2*q) 2 j ≤ hi) (hhiN : hi ≤ 12*(R*q)+16*q)
    (hvlo : lo ≤ v) (hvw : v ≤ w) (hw1 : w ≤ v + 1) (hwhi : w < hi)
    (hreg : ∀ y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
      lo ≤ (y 0).val → (y 0).val < hi →
      y ∈ towerBj (dilTower q R) j ∪ towerBj (dilTower q R) (j+1))
    (hwit : ∃ u, v ≤ u ∧ u ≤ w ∧ ∀ y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
      (y 0).val = u → y ∈ towerBj (dilTower q R) j) :
    ∃ sites, IsClassCube 2 (2*q) 12 1 (dilTower q R) sites j ∧
      ∀ y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
        v ≤ (y 0).val → (y 0).val ≤ w → y ∈ sites := by
  have hs : 0 < bigSide (2*q) 2 j := by dsimp [bigSide]; positivity
  have hqs : q ≤ bigSide (2*q) 2 j := by interval_cases j <;> simp [bigSide] <;> omega
  obtain ⟨t, ht, hlot, hthi, htv, hwt⟩ := clamp1D hs hlo hhi hwid hvlo hvw hw1 hwhi
  obtain ⟨z, hz, hbox⟩ := dil_box hq hqs ht (by omega : t + 12*bigSide (2*q) 2 j ≤ 12*(R*q)+16*q)
  refine ⟨siteBox z (12*bigSide (2*q) 2 j), isClassCube_of (dil_admissible hq hR).1
    ⟨hj, ⟨z, hz, rfl⟩, ?_, ?_⟩, ?_⟩
  · intro y hy
    have := (hbox y).mp hy
    exact hreg y (by omega) (by omega)
  · obtain ⟨u, hvu, huw, hu⟩ := hwit
    let y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) := fun μ =>
      ⟨if μ = 0 then u else 0, by rw [dil_fine_size hq]; split_ifs <;> omega⟩
    have hy : (y 0).val = u := by simp [y]
    exact ⟨y, (hbox y).mpr (by rw [hy]; omega), hu y hy⟩
  · intro y hy1 hy2
    exact (hbox y).mpr (by omega)

theorem dil_cube_neighborhood {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (hx : x ∈ (dilTower q R).Om 0) :
    ∃ sites j, IsClassCube 2 (2*q) 12 1 (dilTower q R) sites j ∧
      ∀ y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
        (x 0).val ≤ (y 0).val → (y 0).val ≤ (x 0).val + 1 →
        y ∈ (dilTower q R).Om 0 → y ∈ sites := by
  change (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) at hx
  have hRq : 6*q ≤ R*q := Nat.mul_le_mul_right q hR6
  have hp : bigSide (2*q) 2 1 ∣ 2*(R*q)+4*q := by
    obtain ⟨t, rfl⟩ := hR; exact ⟨t+1, by simp [bigSide]; ring⟩
  have hq' : bigSide (2*q) 2 1 ∣ 10*(R*q)+12*q := by
    obtain ⟨t, rfl⟩ := hR; exact ⟨5*t+3, by simp [bigSide]; ring⟩
  by_cases hcore : 2*(R*q)+4*q ≤ (x 0).val ∧ (x 0).val+1 < 10*(R*q)+12*q
  · obtain ⟨sites, hc, hall⟩ := dil_region_cube (j := 1) (lo := 2*(R*q)+4*q)
      (hi := 10*(R*q)+12*q) (v := (x 0).val) (w := (x 0).val+1)
      hq hR (by omega) hp hq' (by dsimp [bigSide]; omega) (by omega)
      hcore.1 (by omega) le_rfl hcore.2
      (by intro y hy1 hy2; left; simp [towerBj, dilTower]; omega)
      ⟨(x 0).val, le_rfl, by omega, by intro y hy; simp [towerBj, dilTower]; omega⟩
    exact ⟨sites, 1, hc, fun y hy1 hy2 _ => hall y hy1 hy2⟩
  · have hreg : ∀ y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
        4*q ≤ (y 0).val → (y 0).val < 12*(R*q)+12*q →
        y ∈ towerBj (dilTower q R) 0 ∪ towerBj (dilTower q R) 1 := by
      intro y hy1 hy2
      by_cases h : 2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q
      · right; simpa [towerBj, dilTower] using h
      · left; simp [towerBj, dilTower]; omega
    have hwit : ∃ u, (x 0).val ≤ u ∧ u ≤ min ((x 0).val+1) (12*(R*q)+12*q-1) ∧
        ∀ y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)), (y 0).val = u →
          y ∈ towerBj (dilTower q R) 0 := by
      by_cases hleft : (x 0).val < 2*(R*q)+4*q
      · refine ⟨(x 0).val, le_rfl, by omega, ?_⟩
        intro y hy; simp [towerBj, dilTower]; omega
      · refine ⟨max (x 0).val (10*(R*q)+12*q), by omega, by omega, ?_⟩
        intro y hy; simp [towerBj, dilTower]; omega
    have hlo : bigSide (2*q) 2 0 ∣ 4*q := ⟨2, by simp [bigSide]; ring⟩
    have hhi : bigSide (2*q) 2 0 ∣ 12*(R*q)+12*q := ⟨6*R+6, by simp [bigSide]; ring⟩
    obtain ⟨sites, hc, hall⟩ := dil_region_cube (j := 0) (lo := 4*q)
      (hi := 12*(R*q)+12*q) (v := (x 0).val) (w := min ((x 0).val+1) (12*(R*q)+12*q-1))
      hq hR (by omega) hlo hhi
      (by dsimp [bigSide]; omega) (by omega) hx.1 (by omega) (by omega) (by omega)
      hreg hwit
    refine ⟨sites, 0, hc, ?_⟩
    intro y hy1 hy2 hy
    change (4*q ≤ (y 0).val ∧ (y 0).val < 12*(R*q)+12*q) at hy
    exact hall y hy1 (by omega)

theorem dil_shift_zero {q : ℕ} (hq : 0 < q) (R : ℕ)
    (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (μ : Fin 3) :
    ((periodicLatticeShift x μ) 0).val =
      if μ = 0 then ((x 0).val+1) % (12*(R*q)+16*q) else (x 0).val := by
  by_cases h : μ = 0
  · subst μ
    simp only [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one',
      dil_fine_size hq, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega : 1 < 12*(R*q)+16*q)]
  · simp [periodicLatticeShift, Function.update_of_ne (Ne.symm h), h]

theorem dil_coverage {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R) :
    CoversOm0p 2 (2*q) 12 1 (dilTower q R) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨sites, j, hc, hall⟩ := dil_cube_neighborhood hq hR hR6 x hx
    exact ⟨sites, j, hc, hall x le_rfl (by omega) hx⟩
  · intro p hp
    have hmem : ∀ e : PeriodicLatticeEdge (scaleUp 2 1 (dilLu q R)),
        e ∈ periodicPlaquetteBoundaryEdges p ↔
        e = (p.1, p.2.1.1) ∨ e = (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∨
        e = (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∨ e = (p.1, p.2.1.2) := by
      intro e; simp [periodicPlaquetteBoundaryEdges]
    have hx := (hp _ ((hmem _).mpr (Or.inl rfl))).1
    obtain ⟨sites, j, hc, hall⟩ := dil_cube_neighborhood hq hR hR6 p.1 hx
    have hxb : (p.1 0).val+2 < 12*(R*q)+16*q := by
      change (4*q ≤ (p.1 0).val ∧ (p.1 0).val < 12*(R*q)+12*q) at hx; omega
    have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
    have ha (μ : Fin 3) :
        (p.1 0).val ≤ ((periodicLatticeShift p.1 μ) 0).val ∧
        ((periodicLatticeShift p.1 μ) 0).val ≤ (p.1 0).val+1 := by
      rw [dil_shift_zero hq]; split_ifs
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
      · omega
    have hab (μ ν : Fin 3) (hne : μ ≠ ν) :
        (p.1 0).val ≤ ((periodicLatticeShift (periodicLatticeShift p.1 μ) ν) 0).val ∧
        ((periodicLatticeShift (periodicLatticeShift p.1 μ) ν) 0).val ≤ (p.1 0).val+1 := by
      rw [dil_shift_zero hq, dil_shift_zero hq]
      split_ifs <;> simp_all only [Nat.mod_eq_of_lt (by omega : (p.1 0).val+1 < 12*(R*q)+16*q)] <;> omega
    refine ⟨sites, j, hc, ?_⟩
    intro e he
    obtain ⟨h1, h2⟩ := hp e he
    rcases (hmem e).mp he with rfl | rfl | rfl | rfl
    · exact ⟨hall p.1 le_rfl (Nat.le_succ _) h1, hall _ (ha _).1 (ha _).2 h2⟩
    · exact ⟨hall _ (ha _).1 (ha _).2 h1, hall _ (hab _ _ hne).1 (hab _ _ hne).2 h2⟩
    · exact ⟨hall _ (ha _).1 (ha _).2 h1, hall _ (hab _ _ hne.symm).1 (hab _ _ hne.symm).2 h2⟩
    · exact ⟨hall p.1 le_rfl (Nat.le_succ _) h1, hall _ (ha _).1 (ha _).2 h2⟩

def dilPattern (q R : ℕ) (e : Bond (scaleUp 2 1 (dilLu q R))) : Prop :=
  (e.1 0).val = 2*(R*q)+4*q ∧ (e.1 1).val % 2 = 0 ∧ (e.1 2).val % 2 = 0 ∧ e.2 = 1

open Classical in
noncomputable def dilU (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then V e
    else Ug (if dilPattern q R e then ε else 0)

theorem dil_regular {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) {α ε : ℝ} (hα : 0 < α)
    (hε : |ε| ≤ α/80) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    PerCubeRegular2 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (dilU q R ε V) := by
  classical
  let χ : Bond (scaleUp 2 1 (dilLu q R)) → ℝ := fun e => if dilPattern q R e then 2*ε else 0
  have hχ : ∀ e, |χ e| ≤ α * (((2 : ℝ)^1)⁻¹)^2/10 := by
    intro e; dsimp [χ]; split_ifs
    · rw [abs_mul]; norm_num; linarith
    · norm_num; positivity
  apply perCubeRegular2_congr (dil_admissible hq hR).1 (U := Ufield (((2 : ℝ)^1)⁻¹) χ)
  · intro e he
    have hz : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) := fun h => h.1 he.1
    simp only [dilU, if_neg hz, Ufield, χ]
    split_ifs <;> congr 1 <;> norm_num
    ring
  · exact ufield_perCubeRegular2 (by norm_num) (by omega) (by norm_num) _ hα χ hχ

def dilDefectSite {q : ℕ} (hq : 0 < q) (R : ℕ) : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  fun μ => ⟨if μ = 0 then 2*(R*q)+4*q else 0, by rw [dil_fine_size hq]; split_ifs <;> omega⟩

theorem dilU_nonflat {q : ℕ} (hq : 0 < q) (R : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    ∃ e : Bond (scaleUp 2 1 (dilLu q R)), e.1 ∈ (dilTower q R).Om 0 ∧ dilU q R ε V e ≠ 1 := by
  let e : Bond (scaleUp 2 1 (dilLu q R)) := (dilDefectSite hq R, 1)
  have he : e.1 ∈ (dilTower q R).Om 0 := by
    change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
    simp [e, dilDefectSite]; omega
  have hz : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) := fun h => h.1 he
  have hp : dilPattern q R e := by
    simp [dilPattern, e, dilDefectSite, show (2 : Fin 3) ≠ 0 by decide]
  refine ⟨e, he, ?_⟩
  simpa only [dilU, if_neg hz, if_pos hp] using Ug_ne_one hε0 hε1

/-- Every positive scale, every even R at least six, every positive cap.
The exterior configuration remains free. No spectral conclusion is included. -/
theorem dil_in_class_nonflat_competitor {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    {a₀ : ℝ} (ha₀ : 0 < a₀) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    ∃ α ε : ℝ, 0 < α ∧ (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ ∧ 0 < ε ∧ ε < 1 ∧
      TorusOK 2 (2*q) (dilLu q R) ∧ Admissible 2 (2*q) R 1 (dilTower q R) ∧
      LambdaOK2 2 (2*q) R 1 (dilTower q R) (dilLam q R) ∧
      ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (dilU q R ε V) ∧
      OnLambdaTildeIn (dilLam q R) 2 (dilBt hq R) ∧ OnLambdaT (dilLam q R) (dilBt hq R) ∧
      0 < bondEnergy (dilBt hq R) ∧
      ∃ e : Bond (scaleUp 2 1 (dilLu q R)), e.1 ∈ (dilTower q R).Om 0 ∧ dilU q R ε V e ≠ 1 := by
  let α : ℝ := min (a₀/(24*q)) 1/2
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hα : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1/2 := by dsimp [α]; linarith [min_le_right (a₀/(24*q)) 1]
  have hcap : (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ := by
    have hm : α ≤ a₀/(24*q) := by
      have hp : 0 < min (a₀/(24*q)) 1 := by positivity
      dsimp [α]; linarith [min_le_left (a₀/(24*q)) 1]
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 24*q)).mp hm
    push_cast; nlinarith
  have hε0 : 0 < α/160 := by positivity
  have hε1 : α/160 < 1 := by linarith
  have heps : |α/160| ≤ α/80 := by rw [abs_of_pos hε0]; linarith
  obtain ⟨hB1, hB2, hE⟩ := dil_competitor hq hR
  exact ⟨α, α/160, hα, hcap, hε0, hε1, dil_torus hq R, dil_admissible hq hR,
    dil_lambda hq hR, ⟨dil_coverage hq hR hR6, dil_regular hq hR hα heps V⟩,
    hB1, hB2, hE, dilU_nonflat hq R hε0 hε1 V⟩

#print axioms dil_box
#print axioms dil_region_cube
#print axioms dil_cube_neighborhood
#print axioms dil_shift_zero
#print axioms dil_coverage
#print axioms dilPattern
#print axioms dilU
#print axioms dil_regular
#print axioms dilDefectSite
#print axioms dilU_nonflat
#print axioms dil_in_class_nonflat_competitor

end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round4.Guarded.RefuteR1

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

def dilDefectPlaquette {q : ℕ} (hq : 0 < q) (R : ℕ) :
    PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)) :=
  (dilDefectSite hq R, ⟨(0, 1), by decide⟩)

open Classical in
theorem dilU_on_base {q R : ℕ} (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R)))
    (e : Bond (scaleUp 2 1 (dilLu q R))) (he : e.1 ∈ (dilTower q R).Om 0) :
    dilU q R ε V e = Ug (if dilPattern q R e then ε else 0) := by
  have hz : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) := fun h => h.1 he
  simp only [dilU, if_neg hz]

/-- An exact holonomy computation, not merely a nonidentity bond. -/
theorem dil_holonomy {q : ℕ} (hq : 0 < q) (R : ℕ) (ε : ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    periodicPlaquetteHolonomy (dilU q R ε V) (dilDefectPlaquette hq R) = (Ug ε)⁻¹ := by
  let x := dilDefectSite hq R
  have hx : (x 0).val = 2*(R*q)+4*q := by simp [x, dilDefectSite]
  have hxmem : x ∈ (dilTower q R).Om 0 := by
    change 4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q
    rw [hx]; omega
  have hxs : ((periodicLatticeShift x 0) 0).val = 2*(R*q)+4*q+1 := by
    rw [dil_shift_zero hq, if_pos rfl, hx, Nat.mod_eq_of_lt (by omega)]
  have hxt : ((periodicLatticeShift x 1) 0).val = 2*(R*q)+4*q := by
    rw [dil_shift_zero hq, if_neg (by decide), hx]
  have hsmem : periodicLatticeShift x 0 ∈ (dilTower q R).Om 0 := by
    change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
    rw [hxs]; omega
  have htmem : periodicLatticeShift x 1 ∈ (dilTower q R).Om 0 := by
    change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
    rw [hxt]; omega
  have hp0 : ¬ dilPattern q R (x, 0) := by simp [dilPattern]
  have hp1 : ¬ dilPattern q R (periodicLatticeShift x 0, 1) := by
    intro h
    have hh : ((periodicLatticeShift x 0) 0).val = 2*(R*q)+4*q := h.1
    rw [hxs] at hh
    omega
  have hp2 : ¬ dilPattern q R (periodicLatticeShift x 1, 0) := by simp [dilPattern]
  have hp3 : dilPattern q R (x, 1) := by
    simp [dilPattern, x, dilDefectSite, show (2 : Fin 3) ≠ 0 by decide]
  change dilU q R ε V (x, 0) * dilU q R ε V (periodicLatticeShift x 0, 1) *
    (dilU q R ε V (periodicLatticeShift x 1, 0))⁻¹ * (dilU q R ε V (x, 1))⁻¹ = _
  rw [dilU_on_base ε V _ hxmem, dilU_on_base ε V _ hsmem,
    dilU_on_base ε V _ htmem, dilU_on_base ε V _ hxmem]
  simp [hp0, hp1, hp2, hp3, Ug_zero]

theorem dil_plaq_in {q : ℕ} (hq : 0 < q) (R : ℕ) :
    dilDefectPlaquette hq R ∈ plaqIn ((dilTower q R).Om 0) := by
  let x := dilDefectSite hq R
  have hx : (x 0).val = 2*(R*q)+4*q := by simp [x, dilDefectSite]
  have hs0 : ((periodicLatticeShift x 0) 0).val = 2*(R*q)+4*q+1 := by
    rw [dil_shift_zero hq, if_pos rfl, hx, Nat.mod_eq_of_lt (by omega)]
  have hs1 : ((periodicLatticeShift x 1) 0).val = 2*(R*q)+4*q := by
    rw [dil_shift_zero hq, if_neg (by decide), hx]
  have hs01 : ((periodicLatticeShift (periodicLatticeShift x 0) 1) 0).val = 2*(R*q)+4*q+1 := by
    rw [dil_shift_zero hq, if_neg (by decide), hs0]
  have hs10 : ((periodicLatticeShift (periodicLatticeShift x 1) 0) 0).val = 2*(R*q)+4*q+1 := by
    rw [dil_shift_zero hq, if_pos rfl, hs1, Nat.mod_eq_of_lt (by omega)]
  intro e he
  have he' : e = (x, 0) ∨ e = (periodicLatticeShift x 0, 1) ∨
      e = (periodicLatticeShift x 1, 0) ∨ e = (x, 1) := by
    simpa [dilDefectPlaquette, periodicPlaquetteBoundaryEdges, x] using he
  rcases he' with rfl | rfl | rfl | rfl
  · change (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) ∧
      (4*q ≤ ((periodicLatticeShift x 0) 0).val ∧ ((periodicLatticeShift x 0) 0).val < 12*(R*q)+12*q)
    rw [hx, hs0]; omega
  · change (4*q ≤ ((periodicLatticeShift x 0) 0).val ∧ ((periodicLatticeShift x 0) 0).val < 12*(R*q)+12*q) ∧
      (4*q ≤ ((periodicLatticeShift (periodicLatticeShift x 0) 1) 0).val ∧
        ((periodicLatticeShift (periodicLatticeShift x 0) 1) 0).val < 12*(R*q)+12*q)
    rw [hs0, hs01]; omega
  · change (4*q ≤ ((periodicLatticeShift x 1) 0).val ∧ ((periodicLatticeShift x 1) 0).val < 12*(R*q)+12*q) ∧
      (4*q ≤ ((periodicLatticeShift (periodicLatticeShift x 1) 0) 0).val ∧
        ((periodicLatticeShift (periodicLatticeShift x 1) 0) 0).val < 12*(R*q)+12*q)
    rw [hs1, hs10]; omega
  · change (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) ∧
      (4*q ≤ ((periodicLatticeShift x 1) 0).val ∧ ((periodicLatticeShift x 1) 0).val < 12*(R*q)+12*q)
    rw [hx, hs1]; omega

theorem dilU_curved {q : ℕ} (hq : 0 < q) (R : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    ∃ p ∈ plaqIn ((dilTower q R).Om 0), periodicPlaquetteHolonomy (dilU q R ε V) p ≠ 1 := by
  refine ⟨dilDefectPlaquette hq R, dil_plaq_in hq R, ?_⟩
  rw [dil_holonomy hq R ε V, inv_ne_one]
  exact Ug_ne_one hε0 hε1

theorem dilU_not_pure_gauge {q : ℕ} (hq : 0 < q) (R : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    ¬ ∃ g : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) → G2,
      periodicGaugeTransform g (dilU q R ε V) = fun _ => (1 : G2) := by
  rintro ⟨g, hg⟩
  have hp := plaq_gauge g (dilU q R ε V) (dilDefectSite hq R)
  have hw : plaq (dilU q R ε V) (dilDefectSite hq R) = (Ug ε)⁻¹ :=
    dil_holonomy hq R ε V
  rw [hg, hw] at hp
  have htriv : plaq (fun _ => (1 : G2)) (dilDefectSite hq R) = 1 := by simp [plaq]
  rw [htriv] at hp
  have hinv : (Ug ε)⁻¹ = 1 := by
    have hh := congrArg (fun t => (g (dilDefectSite hq R))⁻¹ * t * g (dilDefectSite hq R)) hp
    simpa [mul_assoc] using hh.symm
  exact Ug_ne_one hε0 hε1 (inv_eq_one.mp hinv)

#print axioms dilDefectPlaquette
#print axioms dilU_on_base
#print axioms dil_holonomy
#print axioms dil_plaq_in
#print axioms dilU_curved
#print axioms dilU_not_pure_gauge

end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round4.Guarded.RefuteR1

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- The nonspectral part of the pinned cofinal failure certificate, including
room, an interior plaquette with nontrivial holonomy, and absence of a global flattening gauge. This is not a failure certificate:
no carrier unit, corrected kernel, or negative goal follows from this theorem. -/
theorem cofinal_in_class_curved_competitor :
    ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ 1 ≤ m ∧
      ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 17*2 ≤ R*(2^m) ∧
        ∀ a₀ : ℝ, 0 < a₀ →
          ∃ (k : ℕ) (_ : 1 ≤ k) (Lu : PeriodicLatticeExtent) (α₀ : ℝ)
            (_ : 0 < α₀) (_ : (12 : ℝ)*(2^m : ℕ)*α₀ ≤ a₀)
            (_ : TorusOK 2 (2^m) Lu)
            (S : Tower (scaleUp 2 k Lu)) (_ : Admissible 2 (2^m) R k S)
            (Lam : Set (PeriodicLatticeSite Lu)) (_ : LambdaOK2 2 (2^m) R k S Lam)
            (U : LinkCfg (scaleUp 2 k Lu))
            (_ : ClassCoupled 2 (2^m) 12 k S α₀ ((2 : ℝ)^k)⁻¹ U)
            (Bt : Bond Lu → SuTwo),
            OnLambdaTildeIn Lam 2 Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧
            (∃ e : Bond (scaleUp 2 k Lu), e.1 ∈ S.Om 0 ∧ U e ≠ 1) ∧
            (∃ p ∈ plaqIn (S.Om 0), periodicPlaquetteHolonomy U p ≠ 1) ∧
            (¬ ∃ g : PeriodicLatticeSite (scaleUp 2 k Lu) → G2,
              periodicGaugeTransform g U = fun _ => (1 : G2)) := by
  intro m₀
  refine ⟨m₀+1, by omega, by omega, ?_⟩
  intro R₀
  let R := 2*(R₀+18)
  let q := 2^m₀
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(m₀+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  have hR : 2 ∣ R := ⟨R₀+18, rfl⟩
  have hR6 : 6 ≤ R := by dsimp [R]; omega
  have hroom : 17*2 ≤ R*(2^(m₀+1)) := by
    rw [hpow]; have hR36 : 36 ≤ R := by dsimp [R]; omega
    nlinarith
  refine ⟨R, by dsimp [R]; omega, hroom, ?_⟩
  intro a₀ ha₀
  obtain ⟨α, ε, hα, hcap, hε0, hε1, hT, hS, hL, hU, hBt1, hBt2, hE, hnon⟩ :=
    dil_in_class_nonflat_competitor hq hR hR6 ha₀ (fun _ => 1)
  rw [hpow]
  exact ⟨1, by omega, dilLu q R, α, hα, hcap, hT, dilTower q R, hS,
    dilLam q R, hL, dilU q R ε (fun _ => 1), hU, dilBt hq R, hBt1, hBt2, hE, hnon,
    dilU_curved hq R hε0 hε1 _, dilU_not_pure_gauge hq R hε0 hε1 _⟩

#print axioms cofinal_in_class_curved_competitor

end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round5.Guarded.IVTR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.D1Literal (PSD)

open Classical in
noncomputable def maskedU (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then V e else Ug (f e)

theorem masked_regular {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) {α : ℝ} (hα : 0 < α)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (hf : ∀ e, |f e| ≤ α/80)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    PerCubeRegular2 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (maskedU q R f V) := by
  classical
  let χ : Bond (scaleUp 2 1 (dilLu q R)) → ℝ := fun e => 2*f e
  have hχ : ∀ e, |χ e| ≤ α * (((2 : ℝ)^1)⁻¹)^2/10 := by
    intro e
    dsimp [χ]
    rw [abs_mul]
    norm_num
    linarith [hf e]
  apply perCubeRegular2_congr (dil_admissible hq hR).1 (U := Ufield (((2 : ℝ)^1)⁻¹) χ)
  · intro e he
    have hz : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) := fun h => h.1 he.1
    simp only [maskedU, if_neg hz, Ufield, χ]
    congr 1
    norm_num
    ring
  · exact ufield_perCubeRegular2 (by norm_num) (by omega) (by norm_num) _ hα χ hχ

/-- One positive cap allocation works for every bounded mask and every
exterior field. This supplies all nonspectral class/competitor obligations,
including a two-sided defect, without an operator-scaling assertion. -/
theorem uniform_masked_class_family {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ α δ : ℝ, 0 < α ∧ (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ ∧ 0 < δ ∧
      TorusOK 2 (2*q) (dilLu q R) ∧ Admissible 2 (2*q) R 1 (dilTower q R) ∧
      LambdaOK2 2 (2*q) R 1 (dilTower q R) (dilLam q R) ∧
      OnLambdaTildeIn (dilLam q R) 2 (dilBt hq R) ∧ OnLambdaT (dilLam q R) (dilBt hq R) ∧
      0 < bondEnergy (dilBt hq R) ∧
      ∀ (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ), (∀ e, |f e| ≤ δ) →
        ∀ V : LinkCfg (scaleUp 2 1 (dilLu q R)),
          ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (maskedU q R f V) := by
  let α : ℝ := min (a₀/(24*q)) 1/2
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ := by
    have hm : α ≤ a₀/(24*q) := by
      have hp : 0 < min (a₀/(24*q)) 1 := by positivity
      dsimp [α]; linarith [min_le_left (a₀/(24*q)) 1]
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 24*q)).mp hm
    push_cast; nlinarith
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR
  refine ⟨α, α/160, hα, hcap, by positivity, dil_torus hq R, dil_admissible hq hR,
    dil_lambda hq hR, hBt1, hBt2, hE, ?_⟩
  intro f hf V
  refine ⟨dil_coverage hq hR hR6, masked_regular hq hR hα f ?_ V⟩
  intro e
  linarith [hf e]

#print axioms maskedU
#print axioms masked_regular
#print axioms uniform_masked_class_family

end AdalyFormal.Round5.Guarded.IVTR2

namespace AdalyFormal.Round6.Guarded.PlacementR1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2 (maskedU masked_regular)
open AdalyFormal.Round3.Guarded.RefuteR2 (zero_coord_le_pdist)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- A local no-go theorem, with no unit or smallness premise. It permits
arbitrary curvature away from the three-neighborhood of Omega1. -/
theorem correction_zero_of_flat_near_top (sD sJ : PlaqSel) (P : IngrBParams)
    {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell)
    (hflat : ∀ e : Bond P.Lf,
      (∃ w ∈ P.S.Om 1, pdist e.1 w ≤ 3) → P.U e = 1) :
    (dataS sD sJ P).Delta2 (dataS_laws sD sJ P) = 0 := by
  have hJ : ∀ b : Bond P.Lf, b ∈ bondsOm0 P.G → b ∉ bondsLam P.G 0 →
      (WithLp.ofLp (JfS sJ P)) b = 0 := by
    intro b hb0 hb1
    have hz : AdalyFormal.IngredientFamily.JfieldLoc (sJ _ P.G) P.U b.1 b.2 = 0 := by
      apply AdalyFormal.D1Guarded.JfieldLoc_zero_of_flat _ _
        {z | ∃ w ∈ P.S.Om 1, pdist z w ≤ 3} hflat
      intro z hz
      rcases AdalyFormal.D1Guarded.endpoint_om1 hell hS b hb0 hb1 with hw | hw
      · exact ⟨b.1, hw, by omega⟩
      · refine ⟨periodicLatticeShift b.1 b.2, hw, ?_⟩
        have htri := AdalyFormal.StatementLaneR8.pdist_triangle z b.1
          (periodicLatticeShift b.1 b.2)
        have hshift := AdalyFormal.StatementLaneR8.pdist_shift_le b.1 b.2
        omega
    unfold JfS AdalyFormal.IngredientFamily.JSU2Loc
    apply Subtype.ext
    simp [hz]
  exact AdalyFormal.D1Guarded.Delta2_eq_zero (dataS sD sJ P) (dataS_laws sD sJ P)
    (AdalyFormal.D1Guarded.level0 P.G (JfS sJ P))
    (AdalyFormal.D1Guarded.dataS_J_eq_Qs sD sJ P hJ)
    (fun A => AdalyFormal.D1Guarded.C2full_level0_inner P.G P.U _ _)

/-- The two-fine-site offset does not grow with q or R. -/
def placementPattern (q R : ℕ) (e : Bond (scaleUp 2 1 (dilLu q R))) : Prop :=
  (e.1 0).val = 4*q+2 ∧ (e.1 1).val % 2 = 0 ∧ (e.1 2).val % 2 = 0 ∧ e.2 = 1

open Classical in
noncomputable def placementU (q R : ℕ) (ε : ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then V e
    else Ug (if placementPattern q R e then ε else 0)

theorem placement_regular {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) {α ε : ℝ}
    (hα : 0 < α) (hε : |ε| ≤ α/80) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    PerCubeRegular2 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹
      (placementU q R ε V) := by
  classical
  exact masked_regular hq hR hα (fun e => if placementPattern q R e then ε else 0)
    (fun e => by
      split_ifs
      · exact hε
      · simp only [abs_zero]; positivity) V

/-- Every source read on a non-level-zero carrier bond is far from this
boundary placement, for all admissible scales and radii in the family. -/
theorem placement_flat_near_top {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R)))
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : ∃ w ∈ (dilTower q R).Om 1, pdist e.1 w ≤ 3) :
    placementU q R ε V e = 1 := by
  classical
  obtain ⟨w, hw, hd⟩ := he
  have hRq : 6*q ≤ R*q := Nat.mul_le_mul_right q hR6
  have hroom : 3 ≤ R*(2*q) := by nlinarith
  have he0 : e.1 ∈ (dilTower q R).Om 0 :=
    AdalyFormal.D1Guarded.near_om1 (dil_admissible hq hR) hw (le_trans hd hroom) (by omega)
  have hez : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) := fun h => h.1 he0
  have hp : ¬ placementPattern q R e := by
    intro hp
    have hc := le_trans (zero_coord_le_pdist e.1 w) hd
    simp only [dil_fine_size hq, ↓reduceIte] at hc
    change 2*(R*q)+4*q ≤ (w 0).val ∧ (w 0).val < 10*(R*q)+12*q at hw
    have hx : (e.1 0).val = 4*q+2 := hp.1
    rw [hx] at hc
    unfold pcd at hc
    split_ifs at hc <;> omega
  simp [placementU, hez, hp, Ug_zero]

noncomputable def placementP (q R : ℕ) (ε a : ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (placementU q R ε V) a (dilLam q R)

/-- Exact genuine correction vanishes, even at nonunit localized data.
This is not a failure of numerical resolution. -/
theorem placement_correction_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    (ε a : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    (dataS selIn selIn (placementP q R ε a V)).Delta2
      (dataS_laws selIn selIn _) = 0 := by
  exact correction_zero_of_flat_near_top selIn selIn (placementP q R ε a V)
    (dil_admissible hq hR) (by change 0 < 2; norm_num) (placement_flat_near_top hq hR hR6 ε V)

/-- The variant cannot separate the guarded carrier from the corrected
pencil, for ANY amplitude, exterior field, or mass. No global goal follows. -/
theorem placement_guard_iff_pencil {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    (ε a : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    CPen 2 1 (dilLu q R) (by norm_num) (dilTower q R) (placementU q R ε V) a (dilLam q R) ↔
      IsUnit (dataS selAll selAll (placementP q R ε a V)).Ginv := by
  change IsUnit ((dataS selAll selAll (placementP q R ε a V)).Ginv -
    (dataS selIn selIn (placementP q R ε a V)).Delta2 (dataS_laws selIn selIn _)) ↔ _
  rw [placement_correction_zero hq hR hR6 ε a V, sub_zero]

#print axioms correction_zero_of_flat_near_top
#print axioms placementPattern
#print axioms placementU
#print axioms placement_regular
#print axioms placement_flat_near_top
#print axioms placementP
#print axioms placement_correction_zero
#print axioms placement_guard_iff_pencil

/-! Geometry and cap certificates for this NEW placement. The tower, Lambda,
and positive-energy competitor are unchanged, not silently replaced. -/
def placementDefectSite {q : ℕ} (hq : 0 < q) (R : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  fun μ => ⟨if μ = 0 then 4*q+2 else 0, by rw [dil_fine_size hq]; split_ifs <;> omega⟩

def placementDefectPlaquette {q : ℕ} (hq : 0 < q) (R : ℕ) :
    PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)) :=
  (placementDefectSite hq R, ⟨(0, 1), by decide⟩)

open Classical in
theorem placementU_on_base {q R : ℕ} (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R)))
    (e : Bond (scaleUp 2 1 (dilLu q R))) (he : e.1 ∈ (dilTower q R).Om 0) :
    placementU q R ε V e = Ug (if placementPattern q R e then ε else 0) := by
  have hz : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) := fun h => h.1 he
  simp only [placementU, if_neg hz]

/-- Adaptation of the original four-link proof to x=4q+2. -/
theorem placement_holonomy {q : ℕ} (hq : 0 < q) (R : ℕ) (ε : ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    periodicPlaquetteHolonomy (placementU q R ε V) (placementDefectPlaquette hq R) = (Ug ε)⁻¹ := by
  let x := placementDefectSite hq R
  have hx : (x 0).val = 4*q+2 := by simp [x, placementDefectSite]
  have hxmem : x ∈ (dilTower q R).Om 0 := by
    change 4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q
    rw [hx]; omega
  have hxs : ((periodicLatticeShift x 0) 0).val = 4*q+2+1 := by
    rw [dil_shift_zero hq, if_pos rfl, hx, Nat.mod_eq_of_lt (by omega)]
  have hxt : ((periodicLatticeShift x 1) 0).val = 4*q+2 := by
    rw [dil_shift_zero hq, if_neg (by decide), hx]
  have hsmem : periodicLatticeShift x 0 ∈ (dilTower q R).Om 0 := by
    change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
    rw [hxs]; omega
  have htmem : periodicLatticeShift x 1 ∈ (dilTower q R).Om 0 := by
    change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
    rw [hxt]; omega
  have hp0 : ¬ placementPattern q R (x, 0) := by simp [placementPattern]
  have hp1 : ¬ placementPattern q R (periodicLatticeShift x 0, 1) := by
    intro h
    have hh : ((periodicLatticeShift x 0) 0).val = 4*q+2 := h.1
    rw [hxs] at hh
    omega
  have hp2 : ¬ placementPattern q R (periodicLatticeShift x 1, 0) := by simp [placementPattern]
  have hp3 : placementPattern q R (x, 1) := by
    simp [placementPattern, x, placementDefectSite, show (2 : Fin 3) ≠ 0 by decide]
  change placementU q R ε V (x, 0) * placementU q R ε V (periodicLatticeShift x 0, 1) *
    (placementU q R ε V (periodicLatticeShift x 1, 0))⁻¹ * (placementU q R ε V (x, 1))⁻¹ = _
  rw [placementU_on_base ε V _ hxmem, placementU_on_base ε V _ hsmem,
    placementU_on_base ε V _ htmem, placementU_on_base ε V _ hxmem]
  simp [hp0, hp1, hp2, hp3, Ug_zero]

/-- The curved plaquette is completely in the level-zero collar, not at
Omega1 and not among the omitted exterior plaquettes. -/
theorem placement_plaq_level0 {q R : ℕ} (hq : 0 < q) (hR6 : 6 ≤ R) :
    placementDefectPlaquette hq R ∈ plaqIn (towerBj (dilTower q R) 0) := by
  let x := placementDefectSite hq R
  have hRq : 6*q ≤ R*q := Nat.mul_le_mul_right q hR6
  have hx : (x 0).val = 4*q+2 := by simp [x, placementDefectSite]
  have hs0 : ((periodicLatticeShift x 0) 0).val = 4*q+3 := by
    rw [dil_shift_zero hq, if_pos rfl, hx, Nat.mod_eq_of_lt (by omega)]
  have hs1 : ((periodicLatticeShift x 1) 0).val = 4*q+2 := by
    rw [dil_shift_zero hq, if_neg (by decide), hx]
  have hs01 : ((periodicLatticeShift (periodicLatticeShift x 0) 1) 0).val = 4*q+3 := by
    rw [dil_shift_zero hq, if_neg (by decide), hs0]
  have hs10 : ((periodicLatticeShift (periodicLatticeShift x 1) 0) 0).val = 4*q+3 := by
    rw [dil_shift_zero hq, if_pos rfl, hs1, Nat.mod_eq_of_lt (by omega)]
  have hmem (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
      (hz : (z 0).val = 4*q+2 ∨ (z 0).val = 4*q+3) : z ∈ towerBj (dilTower q R) 0 := by
    change (4*q ≤ (z 0).val ∧ (z 0).val < 12*(R*q)+12*q) ∧
      ¬ (2*(R*q)+4*q ≤ (z 0).val ∧ (z 0).val < 10*(R*q)+12*q)
    omega
  intro e he
  have he' : e = (x, 0) ∨ e = (periodicLatticeShift x 0, 1) ∨
      e = (periodicLatticeShift x 1, 0) ∨ e = (x, 1) := by
    simpa [placementDefectPlaquette, periodicPlaquetteBoundaryEdges, x] using he
  rcases he' with rfl | rfl | rfl | rfl
  · exact ⟨hmem x (Or.inl hx), hmem _ (Or.inr hs0)⟩
  · exact ⟨hmem _ (Or.inr hs0), hmem _ (Or.inr hs01)⟩
  · exact ⟨hmem _ (Or.inl hs1), hmem _ (Or.inr hs10)⟩
  · exact ⟨hmem x (Or.inl hx), hmem _ (Or.inl hs1)⟩

theorem placement_plaq_in {q R : ℕ} (hq : 0 < q) (hR6 : 6 ≤ R) :
    placementDefectPlaquette hq R ∈ plaqIn ((dilTower q R).Om 0) := by
  intro e he
  have h := placement_plaq_level0 hq hR6 e he
  exact ⟨h.1.1, h.2.1⟩

theorem placementU_curved {q R : ℕ} (hq : 0 < q) (hR6 : 6 ≤ R) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    ∃ p ∈ plaqIn ((dilTower q R).Om 0), periodicPlaquetteHolonomy (placementU q R ε V) p ≠ 1 := by
  refine ⟨placementDefectPlaquette hq R, placement_plaq_in hq hR6, ?_⟩
  rw [placement_holonomy hq R ε V, inv_ne_one]
  exact Ug_ne_one hε0 hε1

/-- Nontrivial bond, in addition to the actual nontrivial holonomy above. -/
theorem placementU_nonflat {q : ℕ} (hq : 0 < q) (R : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    ∃ e : Bond (scaleUp 2 1 (dilLu q R)), e.1 ∈ (dilTower q R).Om 0 ∧ placementU q R ε V e ≠ 1 := by
  let e : Bond (scaleUp 2 1 (dilLu q R)) := (placementDefectSite hq R, 1)
  have he : e.1 ∈ (dilTower q R).Om 0 := by
    change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
    simp [e, placementDefectSite]; omega
  have hp : placementPattern q R e := by
    simp [placementPattern, e, placementDefectSite, show (2 : Fin 3) ≠ 0 by decide]
  refine ⟨e, he, ?_⟩
  rw [placementU_on_base ε V e he, if_pos hp]
  exact Ug_ne_one hε0 hε1

theorem placementU_not_pure_gauge {q : ℕ} (hq : 0 < q) (R : ℕ) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    ¬ ∃ g : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) → G2,
      periodicGaugeTransform g (placementU q R ε V) = fun _ => (1 : G2) := by
  rintro ⟨g, hg⟩
  have hp := plaq_gauge g (placementU q R ε V) (placementDefectSite hq R)
  have hw : plaq (placementU q R ε V) (placementDefectSite hq R) = (Ug ε)⁻¹ :=
    placement_holonomy hq R ε V
  rw [hg, hw] at hp
  have htriv : plaq (fun _ => (1 : G2)) (placementDefectSite hq R) = 1 := by simp [plaq]
  rw [htriv] at hp
  have hinv : (Ug ε)⁻¹ = 1 := by
    have hh := congrArg (fun t => (g (placementDefectSite hq R))⁻¹ * t * g (placementDefectSite hq R)) hp
    simpa [mul_assoc] using hh.symm
  exact Ug_ne_one hε0 hε1 (inv_eq_one.mp hinv)

/-- One amplitude allocation works before every exterior field. All class,
coverage, cap, admissibility, Lambda and competitor obligations are present. -/
theorem uniform_placement_class_family {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ α ε : ℝ, 0 < α ∧ (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ ∧ 0 < ε ∧ ε < 1 ∧
      TorusOK 2 (2*q) (dilLu q R) ∧ Admissible 2 (2*q) R 1 (dilTower q R) ∧
      LambdaOK2 2 (2*q) R 1 (dilTower q R) (dilLam q R) ∧
      OnLambdaTildeIn (dilLam q R) 2 (dilBt hq R) ∧ OnLambdaT (dilLam q R) (dilBt hq R) ∧
      0 < bondEnergy (dilBt hq R) ∧
      ∀ V : LinkCfg (scaleUp 2 1 (dilLu q R)),
        ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (placementU q R ε V) ∧
        (∃ e : Bond (scaleUp 2 1 (dilLu q R)), e.1 ∈ (dilTower q R).Om 0 ∧ placementU q R ε V e ≠ 1) ∧
        (∃ p ∈ plaqIn ((dilTower q R).Om 0), periodicPlaquetteHolonomy (placementU q R ε V) p ≠ 1) ∧
        (¬ ∃ g : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) → G2,
          periodicGaugeTransform g (placementU q R ε V) = fun _ => (1 : G2)) := by
  let α : ℝ := min (a₀/(24*q)) 1/2
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hα : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1/2 := by dsimp [α]; linarith [min_le_right (a₀/(24*q)) 1]
  have hcap : (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ := by
    have hm : α ≤ a₀/(24*q) := by
      have hp : 0 < min (a₀/(24*q)) 1 := by positivity
      dsimp [α]; linarith [min_le_left (a₀/(24*q)) 1]
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 24*q)).mp hm
    push_cast; nlinarith
  have hε0 : 0 < α/160 := by positivity
  have hε1 : α/160 < 1 := by linarith
  have heps : |α/160| ≤ α/80 := by rw [abs_of_pos hε0]; linarith
  obtain ⟨hB1, hB2, hE⟩ := dil_competitor hq hR
  refine ⟨α, α/160, hα, hcap, hε0, hε1, dil_torus hq R, dil_admissible hq hR,
    dil_lambda hq hR, hB1, hB2, hE, ?_⟩
  intro V
  exact ⟨⟨dil_coverage hq hR hR6, placement_regular hq hR hα heps V⟩,
    placementU_nonflat hq R hε0 hε1 V, placementU_curved hq hR6 hε0 hε1 V,
    placementU_not_pure_gauge hq R hε0 hε1 V⟩

/-- Cofinal curved boundary placements really exist in the pinned class.
R is selected before the cap. The last conjunct proves this family is NOT a
separating family; it does not prove either positive pinned goal. -/
theorem cofinal_curved_placement_no_separation :
    ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ 1 ≤ m ∧
      ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 17*2 ≤ R*(2^m) ∧
        ∀ a₀ : ℝ, 0 < a₀ →
          ∃ (k : ℕ) (_ : 1 ≤ k) (Lu : PeriodicLatticeExtent) (α₀ : ℝ)
            (_ : 0 < α₀) (_ : (12 : ℝ)*(2^m : ℕ)*α₀ ≤ a₀)
            (_ : TorusOK 2 (2^m) Lu)
            (S : Tower (scaleUp 2 k Lu)) (_ : Admissible 2 (2^m) R k S)
            (Lam : Set (PeriodicLatticeSite Lu)) (_ : LambdaOK2 2 (2^m) R k S Lam)
            (U : LinkCfg (scaleUp 2 k Lu))
            (_ : ClassCoupled 2 (2^m) 12 k S α₀ ((2 : ℝ)^k)⁻¹ U)
            (Bt : Bond Lu → SuTwo),
            OnLambdaTildeIn Lam 2 Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧
            (∃ e : Bond (scaleUp 2 k Lu), e.1 ∈ S.Om 0 ∧ U e ≠ 1) ∧
            (∃ p ∈ plaqIn (S.Om 0), periodicPlaquetteHolonomy U p ≠ 1) ∧
            (¬ ∃ g : PeriodicLatticeSite (scaleUp 2 k Lu) → G2,
              periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
            ∀ a : ℝ, CPen 2 k Lu (by norm_num) S U a Lam ↔
              IsUnit (dataS selAll selAll (gparams 2 k Lu (by norm_num) S U a Lam)).Ginv := by
  intro m₀
  refine ⟨m₀+1, by omega, by omega, ?_⟩
  intro R₀
  let R := 2*(R₀+18)
  let q := 2^m₀
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(m₀+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  have hR : 2 ∣ R := ⟨R₀+18, rfl⟩
  have hR6 : 6 ≤ R := by dsimp [R]; omega
  have hroom : 17*2 ≤ R*(2^(m₀+1)) := by
    rw [hpow]; have hR36 : 36 ≤ R := by dsimp [R]; omega
    nlinarith
  refine ⟨R, by dsimp [R]; omega, hroom, ?_⟩
  intro a₀ ha₀
  obtain ⟨α, ε, hα, hcap, _, _, hT, hS, hL, hBt1, hBt2, hE, hall⟩ :=
    uniform_placement_class_family hq hR hR6 ha₀
  obtain ⟨hU, hnon, hcurved, hnongauge⟩ := hall (fun _ => 1)
  rw [hpow]
  exact ⟨1, by omega, dilLu q R, α, hα, hcap, hT, dilTower q R, hS,
    dilLam q R, hL, placementU q R ε (fun _ => 1), hU, dilBt hq R,
    hBt1, hBt2, hE, hnon, hcurved, hnongauge,
    fun a => placement_guard_iff_pencil hq hR hR6 ε a _⟩

#print axioms placementDefectSite
#print axioms placementDefectPlaquette
#print axioms placementU_on_base
#print axioms placement_holonomy
#print axioms placement_plaq_level0
#print axioms placement_plaq_in
#print axioms placementU_curved
#print axioms placementU_nonflat
#print axioms placementU_not_pure_gauge
#print axioms uniform_placement_class_family
#print axioms cofinal_curved_placement_no_separation

/-- The obstruction applies to EVERY bounded-mask placement in two exterior
boundary strips of width d, not only the particular period-two defect.
The strip is separated from Omega1's source-read neighborhood by hgap.
There is no smallness, invertibility, Fourier, or source-sign assumption. -/
theorem boundary_strip_correction_zero {q R d : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hgap : d+3 ≤ 2*(R*q))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (hf : ∀ e, 4*q+d ≤ (e.1 0).val → (e.1 0).val+d < 12*(R*q)+12*q → f e = 0)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) (a : ℝ) :
    let P := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (maskedU q R f V) a (dilLam q R)
    (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) = 0 := by
  dsimp only
  apply correction_zero_of_flat_near_top selIn selIn _ (dil_admissible hq hR)
    (by change 0 < 2; norm_num)
  intro e he
  obtain ⟨w, hw, hd⟩ := he
  change w ∈ (dilTower q R).Om 1 at hw
  have hroom : 3 ≤ R*(2*q) := by nlinarith
  have he0 : e.1 ∈ (dilTower q R).Om 0 :=
    AdalyFormal.D1Guarded.near_om1 (dil_admissible hq hR) hw (le_trans hd hroom) (by omega)
  have hz : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) := fun h => h.1 he0
  have hc := le_trans (zero_coord_le_pdist e.1 w) hd
  simp only [dil_fine_size hq, ↓reduceIte] at hc
  change 2*(R*q)+4*q ≤ (w 0).val ∧ (w 0).val < 10*(R*q)+12*q at hw
  have hn := AdalyFormal.NonVac.pcd_near (dil_fine_bound hq R e.1) hw
    (by omega : 3 ≤ 2*(R*q)+4*q)
    (by omega : 10*(R*q)+12*q+3 ≤ 12*(R*q)+16*q) hc
  have hfe : f e = 0 := hf e (by omega) (by omega)
  change maskedU q R f V e = 1
  simp [maskedU, hz, hfe, Ug_zero]

/-- Thus every such boundary-only mask has the same carrier and corrected
pencil. Full-class small masks are already provided by the copied
uniform_masked_class_family theorem. -/
theorem boundary_strip_guard_iff_pencil {q R d : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hgap : d+3 ≤ 2*(R*q))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (hf : ∀ e, 4*q+d ≤ (e.1 0).val → (e.1 0).val+d < 12*(R*q)+12*q → f e = 0)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) (a : ℝ) :
    CPen 2 1 (dilLu q R) (by norm_num) (dilTower q R) (maskedU q R f V) a (dilLam q R) ↔
      IsUnit (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num)
        (dilTower q R) (maskedU q R f V) a (dilLam q R))).Ginv := by
  unfold CPen
  rw [boundary_strip_correction_zero hq hR hgap f hf V a, sub_zero]

/-- No vector, kernel or otherwise, has a positive correction pairing for
the chosen placement. This is unconditional in epsilon and in the twist. -/
theorem placement_pairing_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    (ε a : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R)))
    (v : ↥(bondSupp (placementP q R ε a V).G)) :
    ⟪v, (dataS selIn selIn (placementP q R ε a V)).Delta2
      (dataS_laws selIn selIn _) v⟫ = 0 := by
  rw [placement_correction_zero hq hR hR6 ε a V]
  simp

#print axioms boundary_strip_correction_zero
#print axioms boundary_strip_guard_iff_pencil
#print axioms placement_pairing_zero

end AdalyFormal.Round6.Guarded.PlacementR1


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

namespace AdalyFormal.Round6.Guarded.PlacementR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2 (maskedU masked_regular uniform_masked_class_family)
open AdalyFormal.Round6.Guarded.PlacementR1
open AdalyFormal.Round3.Guarded.RefuteR2 (zero_coord_le_pdist)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

open Classical in
noncomputable def hybridMask (q R : ℕ) (β ε : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R))) : ℝ :=
  if placementPattern q R e then β else if dilPattern q R e then ε else 0

noncomputable def hybridU (q R : ℕ) (β ε : ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  maskedU q R (hybridMask q R β ε) V

noncomputable def hybridP (q R : ℕ) (β ε a : ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (hybridU q R β ε V) a (dilLam q R)

theorem hybridMask_bound (q R : ℕ) {β ε δ : ℝ} (hδ : 0 ≤ δ)
    (hβ : |β| ≤ δ) (hε : |ε| ≤ δ) : ∀ e, |hybridMask q R β ε e| ≤ δ := by
  classical
  intro e
  unfold hybridMask
  split_ifs <;> simp_all

theorem hybrid_regular {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) {α β ε : ℝ}
    (hα : 0 < α) (hβ : |β| ≤ α/80) (hε : |ε| ≤ α/80)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    PerCubeRegular2 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (hybridU q R β ε V) :=
  masked_regular hq hR hα _ (hybridMask_bound q R (by positivity) hβ hε) V

/-- The boundary defect has no effect on links in the source-read
neighborhood of Omega1. The retained core need NOT be flat. -/
theorem hybrid_agrees_near_top {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    (β ε : ℝ) (V V' : LinkCfg (scaleUp 2 1 (dilLu q R)))
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : ∃ w ∈ (dilTower q R).Om 1, pdist e.1 w ≤ 3) :
    hybridU q R β ε V e = dilU q R ε V' e := by
  classical
  obtain ⟨w, hw, hd⟩ := he
  have hRq : 6*q ≤ R*q := Nat.mul_le_mul_right q hR6
  have hroom : 3 ≤ R*(2*q) := by nlinarith
  have he0 : e.1 ∈ (dilTower q R).Om 0 :=
    AdalyFormal.D1Guarded.near_om1 (dil_admissible hq hR) hw (le_trans hd hroom) (by omega)
  have hez : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) := fun h => h.1 he0
  have hp : ¬ placementPattern q R e := by
    intro hp
    have hc := le_trans (zero_coord_le_pdist e.1 w) hd
    simp only [dil_fine_size hq, ↓reduceIte] at hc
    change 2*(R*q)+4*q ≤ (w 0).val ∧ (w 0).val < 10*(R*q)+12*q at hw
    have hx : (e.1 0).val = 4*q+2 := hp.1
    rw [hx] at hc
    unfold pcd at hc
    split_ifs at hc <;> omega
  simp [hybridU, maskedU, hybridMask, dilU, hez, hp]

/-- Adding a core defect does not erase the level-zero boundary holonomy. -/
theorem hybrid_boundary_holonomy {q R : ℕ} (hq : 0 < q) (hR6 : 6 ≤ R)
    (β ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    periodicPlaquetteHolonomy (hybridU q R β ε V) (placementDefectPlaquette hq R) = (Ug β)⁻¹ := by
  classical
  rw [← placement_holonomy hq R β V]
  apply AdalyFormal.StatementLaneR6.holonomy_congr
  intro e he
  have hRq : 6*q ≤ R*q := Nat.mul_le_mul_right q hR6
  have hx : (e.1 0).val = 4*q+2 ∨ (e.1 0).val = 4*q+3 := by
    rcases (AdalyFormal.StatementLaneR6.edge_mem _ _).mp he with rfl | rfl | rfl | rfl
    · exact Or.inl (by simp [placementDefectPlaquette, placementDefectSite])
    · right
      change ((periodicLatticeShift (placementDefectSite hq R) 0) 0).val = _
      rw [dil_shift_zero hq, if_pos rfl]
      simp only [placementDefectSite, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (by omega)]
    · left
      change ((periodicLatticeShift (placementDefectSite hq R) 1) 0).val = _
      rw [dil_shift_zero hq, if_neg (by decide)]
      simp [placementDefectSite]
    · exact Or.inl (by simp [placementDefectPlaquette, placementDefectSite])
  have hnot : ¬ dilPattern q R e := by intro h; have := h.1; omega
  simp [hybridU, maskedU, hybridMask, placementU, hnot]

/-- The original core plaquette retains its exact holonomy as well; the
hybrid has not silently removed the nonlinear-constraint defect. -/
theorem hybrid_core_holonomy {q R : ℕ} (hq : 0 < q) (hR6 : 6 ≤ R)
    (β ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    periodicPlaquetteHolonomy (hybridU q R β ε V) (dilDefectPlaquette hq R) = (Ug ε)⁻¹ := by
  classical
  rw [← dil_holonomy hq R ε V]
  apply AdalyFormal.StatementLaneR6.holonomy_congr
  intro e he
  have hRq : 6*q ≤ R*q := Nat.mul_le_mul_right q hR6
  have hx : (e.1 0).val = 2*(R*q)+4*q ∨ (e.1 0).val = 2*(R*q)+4*q+1 := by
    rcases (AdalyFormal.StatementLaneR6.edge_mem _ _).mp he with rfl | rfl | rfl | rfl
    · exact Or.inl (by simp [dilDefectPlaquette, dilDefectSite])
    · right
      change ((periodicLatticeShift (dilDefectSite hq R) 0) 0).val = _
      rw [dil_shift_zero hq, if_pos rfl]
      simp only [dilDefectSite, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (by omega)]
    · left
      change ((periodicLatticeShift (dilDefectSite hq R) 1) 0).val = _
      rw [dil_shift_zero hq, if_neg (by decide)]
      simp [dilDefectSite]
    · exact Or.inl (by simp [dilDefectPlaquette, dilDefectSite])
  have hnot : ¬ placementPattern q R e := by intro h; have := h.1; omega
  simp [hybridU, maskedU, hybridMask, dilU, hnot]

#print axioms hybrid_core_holonomy

/-- Uniform independent boundary/core amplitudes, including negative core.
The exact original torus, tower, Lambda and positive-energy competitor remain. -/
theorem uniform_hybrid_class_family {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ α δ : ℝ, 0 < α ∧ (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ ∧ 0 < δ ∧ δ < 1 ∧
      TorusOK 2 (2*q) (dilLu q R) ∧ Admissible 2 (2*q) R 1 (dilTower q R) ∧
      LambdaOK2 2 (2*q) R 1 (dilTower q R) (dilLam q R) ∧
      OnLambdaTildeIn (dilLam q R) 2 (dilBt hq R) ∧ OnLambdaT (dilLam q R) (dilBt hq R) ∧
      0 < bondEnergy (dilBt hq R) ∧
      ∀ β ε : ℝ, |β| ≤ δ → |ε| ≤ δ →
        ∀ V : LinkCfg (scaleUp 2 1 (dilLu q R)),
          ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (hybridU q R β ε V) ∧
          (0 < β → ∃ p ∈ plaqIn ((dilTower q R).Om 0),
            periodicPlaquetteHolonomy (hybridU q R β ε V) p ≠ 1) := by
  obtain ⟨α, δ₀, hα, hcap, hδ₀, hT, hS, hL, hBt1, hBt2, hE, hclass⟩ :=
    uniform_masked_class_family hq hR hR6 ha₀
  let δ : ℝ := min δ₀ (1/2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ₀' : δ ≤ δ₀ := min_le_left _ _
  have hδ1 : δ < 1 := by have := min_le_right δ₀ (1/2 : ℝ); dsimp [δ]; linarith
  refine ⟨α, δ, hα, hcap, hδ, hδ1, hT, hS, hL, hBt1, hBt2, hE, ?_⟩
  intro β ε hβ hε V
  refine ⟨hclass _ (hybridMask_bound q R (le_of_lt hδ₀) (le_trans hβ hδ₀')
    (le_trans hε hδ₀')) V, ?_⟩
  intro hβ0
  refine ⟨placementDefectPlaquette hq R, placement_plaq_in hq hR6, ?_⟩
  rw [hybrid_boundary_holonomy hq hR6, inv_ne_one]
  exact Ug_ne_one hβ0 (lt_of_le_of_lt (le_trans (le_abs_self β) hβ) hδ1)

#print axioms hybridMask
#print axioms hybridU
#print axioms hybridP
#print axioms hybridMask_bound
#print axioms hybrid_regular
#print axioms hybrid_agrees_near_top
#print axioms hybrid_boundary_holonomy
#print axioms uniform_hybrid_class_family

/-- Actual active-source equality for the hybrid family: independent of the
boundary amplitude beta and both arbitrary exterior configurations. -/
theorem hybrid_activeSource_independent {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    (β ε a : ℝ) (V V' : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    activeSource selIn (hybridP q R β ε a V) =
      activeSource selIn (gparams 2 1 (dilLu q R) (by norm_num)
        (dilTower q R) (dilU q R ε V') a (dilLam q R)) := by
  exact activeSource_congr_near_top selIn 2 1 (2*q) R (dilLu q R) (by norm_num)
    (dilTower q R) (dil_admissible hq hR) (hybridU q R β ε V) (dilU q R ε V') a
    (dilLam q R) (hybrid_agrees_near_top hq hR hR6 β ε V V')

/-- Furthest exact hybrid reduction. The new boundary curvature contributes
no additional effective source; any improvement would have to come from
its change to H and the W-dressed second jet. Those are NOT held fixed. -/
theorem hybrid_correction_formula {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    (β ε a : ℝ) (V V' : LinkCfg (scaleUp 2 1 (dilLu q R)))
    (v : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    let P := hybridP q R β ε a V
    let P' := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (dilU q R ε V') a (dilLam q R)
    ⟪v, (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) v⟫ =
      2 * ⟪(dataS selIn selIn P).H ((dataS selIn selIn P).C2 v), activeSource selIn P'⟫ := by
  exact boundary_modification_correction_formula selIn selIn 2 1 (2*q) R
    (dilLu q R) (by norm_num) (dilTower q R) (dil_admissible hq hR)
    (hybridU q R β ε V) (dilU q R ε V') a (dilLam q R)
    (hybrid_agrees_near_top hq hR hR6 β ε V V') v

/-- The old no-go is recovered exactly when the retained core is switched
 off. The statement includes every amplitude, mass and exterior field. -/
theorem hybrid_zero_core_correction_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    (β a : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    (dataS selIn selIn (hybridP q R β 0 a V)).Delta2 (dataS_laws selIn selIn _) = 0 := by
  apply correction_zero_of_flat_near_top selIn selIn (hybridP q R β 0 a V)
    (dil_admissible hq hR) (by change 0 < 2; norm_num)
  intro e he
  change hybridU q R β 0 V e = 1
  rw [hybrid_agrees_near_top hq hR hR6 β 0 V (fun _ => 1) e he]
  simp [dilU, Ug_zero]

/-- Cofinal geometry and arbitrary caps for the actual hybrid. The radius
is selected before the cap; all exterior fields and all signed core
amplitudes in the chosen interval are admitted. No spectral conclusion. -/
theorem cofinal_hybrid_class_family :
    ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ 1 ≤ m ∧
      ∃ q : ℕ, 0 < q ∧ 2^m = 2*q ∧
        ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ 17*2 ≤ R*(2^m) ∧
          ∀ a₀ : ℝ, 0 < a₀ → ∃ α δ : ℝ,
            0 < α ∧ (12 : ℝ)*(2^m : ℕ)*α ≤ a₀ ∧ 0 < δ ∧ δ < 1 ∧
            TorusOK 2 (2^m) (dilLu q R) ∧ Admissible 2 (2^m) R 1 (dilTower q R) ∧
            LambdaOK2 2 (2^m) R 1 (dilTower q R) (dilLam q R) ∧
            ∃ Bt : Bond (dilLu q R) → SuTwo,
              OnLambdaTildeIn (dilLam q R) 2 Bt ∧ OnLambdaT (dilLam q R) Bt ∧
              0 < bondEnergy Bt ∧
              ∀ ε : ℝ, |ε| ≤ δ → ∀ V : LinkCfg (scaleUp 2 1 (dilLu q R)),
                ClassCoupled 2 (2^m) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (hybridU q R δ ε V) ∧
                ∃ p ∈ plaqIn ((dilTower q R).Om 0),
                  periodicPlaquetteHolonomy (hybridU q R δ ε V) p ≠ 1 := by
  intro m₀
  let q := 2^m₀
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(m₀+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  refine ⟨m₀+1, by omega, by omega, q, hq, hpow, ?_⟩
  intro R₀
  let R := 2*(R₀+18)
  have hR : 2 ∣ R := ⟨R₀+18, rfl⟩
  have hR18 : 18 ≤ R := by dsimp [R]; omega
  have hroom : 17*2 ≤ R*(2^(m₀+1)) := by
    rw [hpow]; have hR36 : 36 ≤ R := by dsimp [R]; omega
    nlinarith
  refine ⟨R, by dsimp [R]; omega, hR, hR18, hroom, ?_⟩
  intro a₀ ha₀
  obtain ⟨α, δ, hα, hcap, hδ, hδ1, hT, hS, hL, hBt1, hBt2, hE, hall⟩ :=
    uniform_hybrid_class_family hq hR (by omega) ha₀
  rw [hpow]
  refine ⟨α, δ, hα, hcap, hδ, hδ1, hT, hS, hL, dilBt hq R, hBt1, hBt2, hE, ?_⟩
  intro ε hε V
  obtain ⟨hclass, hcurv⟩ := hall δ ε (by rw [abs_of_pos hδ]) hε V
  exact ⟨hclass, hcurv hδ⟩

#print axioms hybrid_activeSource_independent
#print axioms hybrid_correction_formula
#print axioms hybrid_zero_core_correction_zero
#print axioms cofinal_hybrid_class_family

end AdalyFormal.Round6.Guarded.PlacementR2
