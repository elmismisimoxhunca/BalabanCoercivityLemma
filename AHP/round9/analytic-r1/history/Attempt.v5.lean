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

/-!
Round 5: the curved exterior-twist family and its exact IVT criterion.
All spectral sign/unit hypotheses below remain explicit. None is a pinned goal.
-/
namespace AdalyFormal.Round5.Guarded.IVTR1

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

section Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- A positive correction on a carrier kernel at the first crossing suffices.
No quantitative lower bound independent of curvature, radius or cap is needed. -/
theorem guarded_separation_of_kernel_positive
    (A : ℝ → E →L[ℝ] E) (D : E →L[ℝ] E) (hc : Continuous A)
    (hsA : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫)
    (hsD : ∀ x y, ⟪D x, y⟫ = ⟪x, D y⟫)
    (h0 : AdalyFormal.D1Literal.PSD (A 0 - D))
    (T : ℝ) (hT : 0 < T)
    (hguard : ∀ t, 0 ≤ t → t < T → IsUnit (A t))
    (v : E) (hker : A T v = 0) (hpositive : 0 < ⟪v, D v⟫) :
    ∃ t : ℝ, 0 ≤ t ∧ t < T ∧ IsUnit (A t) ∧ ¬ IsUnit (A t - D) := by
  have hs : ∀ t x y, ⟪(A t - D) x, y⟫ = ⟪x, (A t - D) y⟫ := by
    intro t x y
    simp only [sub_apply, inner_sub_left, inner_sub_right, hsA, hsD]
  have hn : ⟪v, (A T - D) v⟫ < 0 := by
    simp only [sub_apply, inner_sub_right, hker, inner_zero_right]
    linarith
  obtain ⟨t, ht0, htT, hnu⟩ := AdalyFormal.D1Literal.exists_nonunit_path
    (fun t => A t - D) (hc.sub continuous_const) hs h0 T hT v hn
  exact ⟨t, ht0, htT, hguard t ht0 htT, hnu⟩

/-- The full positive-definite guard may be supplied without a numeric gap. -/
theorem unit_of_strict_quadratic (A : E →L[ℝ] E)
    (hpos : ∀ v : E, v ≠ 0 → 0 < ⟪v, A v⟫) : IsUnit A := by
  have hi : Function.Injective A := (injective_iff_map_eq_zero A).mpr (by
    intro v hv
    by_contra hn
    have h := hpos v hn
    rw [hv, inner_zero_right] at h
    exact (lt_irrefl 0) h)
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi, (LinearMap.injective_iff_surjective
      (f := (show E →ₗ[ℝ] E from A))).mp hi⟩

#print axioms guarded_separation_of_kernel_positive
#print axioms unit_of_strict_quadratic
end Abstract

/-- Exactly the round-4 dilU, with the frozen Uth exterior. -/
noncomputable def twistU (q R : ℕ) (ε t : ℝ) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  dilU q R ε (AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t)

noncomputable def twistP (q R : ℕ) (ε a t : ℝ) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (twistU q R ε t) a (dilLam q R)

noncomputable def twistA (q R : ℕ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selAll selAll (twistP q R ε a t)).Ginv

noncomputable def twistD (q R : ℕ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selIn selIn (twistP q R ε a t)).Delta2 (dataS_laws selIn selIn _)

theorem twist_agrees (q R : ℕ) (ε s t : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)) :
    twistU q R ε s e = twistU q R ε t e := by
  classical
  simp only [twistU, dilU, if_neg he]

theorem twist_cont (q R : ℕ) (ε : ℝ) : AdalyFormal.D1Literal.ContFam (twistU q R ε) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [twistU, dilU, if_pos he]
    exact AdalyFormal.D1Literal.contFam_Uth _ e
  · simp only [twistU, dilU, if_neg he]
    exact continuous_const

/-- Localized data are constant even though the fixed interior is curved. -/
theorem twist_data_constant {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (ε a t : ℝ) :
    dataS selIn selIn (twistP q R ε a t) = dataS selIn selIn (twistP q R ε a 0) := by
  change (twistP q R ε a t).data = (twistP q R ε a 0).data
  exact AdalyFormal.M1IMS.data_congr_U (by norm_num) (dil_admissible hq hR)
    (by norm_num) hroom (twistU q R ε 0) (twistU q R ε t) a (dilLam q R)
    (fun e he => twist_agrees q R ε 0 t e (fun hz => hz.1 he.1))

theorem twistD_constant {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (ε a t : ℝ) :
    twistD q R ε a t = twistD q R ε a 0 := by
  have hd := twist_data_constant hq hR hroom ε a t
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

/-- The amplitudes are chosen once before EVERY exterior configuration.
This is stronger than choosing new amplitudes separately for each angle. -/
theorem uniform_curved_family {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ α ε : ℝ, 0 < α ∧ (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ ∧ 0 < ε ∧ ε < 1 ∧
      TorusOK 2 (2*q) (dilLu q R) ∧ Admissible 2 (2*q) R 1 (dilTower q R) ∧
      LambdaOK2 2 (2*q) R 1 (dilTower q R) (dilLam q R) ∧
      OnLambdaTildeIn (dilLam q R) 2 (dilBt hq R) ∧ OnLambdaT (dilLam q R) (dilBt hq R) ∧
      0 < bondEnergy (dilBt hq R) ∧
      ∀ V : LinkCfg (scaleUp 2 1 (dilLu q R)),
        ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (dilU q R ε V) ∧
        ∃ p ∈ plaqIn ((dilTower q R).Om 0), periodicPlaquetteHolonomy (dilU q R ε V) p ≠ 1 := by
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
  exact ⟨⟨dil_coverage hq hR hR6, dil_regular hq hR hα heps V⟩,
    dilU_curved hq R hε0 hε1 V⟩


section ExteriorPath
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
  {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
  (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
  (U : ℝ → Cfg (scaleUp ell k Lu))
  (hUU : ∀ (t : ℝ) (e : Bond (scaleUp ell k Lu)),
    e ∉ AdalyFormal.D1Literal.Zb (S.Om 0) → U t e = U 0 e)
include hS hell hroom hUU in
/-- The proof is the frozen DrPath1.Ginv_lit_path proof with the pin's
verbatim selector definitions and qualified frozen locality references. -/
theorem exterior_carrier_path (sJ : PlaqSel) (t : ℝ) :
    (dataS selAll sJ (gparams ell k Lu hell0 S (U t) a Lam)).Ginv =
      (dataS selAll sJ (gparams ell k Lu hell0 S (U 0) a Lam)).Ginv +
      (pE (geomOf ell k S)).comp (((ContinuousLinearMap.adjoint (Wop (geomOf ell k S) (U 0) a)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (U t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (U 0) Set.univ)).comp
          (Wop (geomOf ell k S) (U 0) a))).comp (iE (geomOf ell k S))) := by
  have hBoth : ∀ e : Bond (scaleUp ell k Lu), BothIn (S.Om 0) e → U t e = U 0 e :=
    fun e he => hUU t e (fun hz => hz.1 he.1)
  have hW := AdalyFormal.D1Literal.Wop_congr_Z hS hell hroom (hUU t) a
  have hT := AdalyFormal.StatementLaneR8.Tfull_congr hS hell hroom hBoth
  have hsec := AdalyFormal.StatementLaneR8.sector_congr hS hell hroom hBoth
  unfold BaseDataS.Ginv dataS
  simp only [gparams, IngrBParams.G, IngrBParams.sector, baseData, DpiFullS, DeltaS, selAll, hW, hT, hsec]
  ext1 y
  simp only [add_apply, ContinuousLinearMap.comp_apply, sub_apply, map_sub]
  abel
end ExteriorPath

/-- Actual carrier continuity for a fixed curved interior: no continuity
of a totalized inverse across a nonunit is asserted or used. -/
theorem twistA_continuous {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (ε a : ℝ) : Continuous (twistA q R ε a) := by
  let G := geomOf 2 1 (dilTower q R)
  let U := twistU q R ε
  have h : twistA q R ε a = fun t => twistA q R ε a 0 +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wop G (U 0) a)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (U t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (U 0) Set.univ)).comp
          (Wop G (U 0) a))).comp (iE G)) := by
    funext t
    exact exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      a (dilLam q R) U (fun s e he => twist_agrees q R ε s 0 e he) selAll t
  rw [h]
  have hd : Continuous fun t => AdalyFormal.StatementLaneR6.deltaKLocCLM (U t)
      (Set.univ : Set (PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)))) :=
    AdalyFormal.D1Literal.cont_deltaKLocCLM (twist_cont q R ε) _
  refine continuous_const.add (Continuous.clm_comp continuous_const (Continuous.clm_comp ?_ continuous_const))
  exact Continuous.clm_comp continuous_const (Continuous.clm_comp (hd.sub continuous_const) continuous_const)

#print axioms exterior_carrier_path
#print axioms twistA_continuous

/-- Conditional separation of the actual pinned assemblies. Initial PSD,
an interval guard and the kernel/correction sign are NOT asserted here. -/
theorem twist_separation_of_kernel_positive {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (ε a : ℝ)
    (h0 : AdalyFormal.D1Literal.PSD (twistA q R ε a 0 - twistD q R ε a 0))
    (T : ℝ) (hT : 0 < T)
    (hguard : ∀ t, 0 ≤ t → t < T → IsUnit (twistA q R ε a t))
    (v : ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (hker : twistA q R ε a T v = 0) (hpositive : 0 < ⟪v, twistD q R ε a 0 v⟫) :
    ∃ t : ℝ, 0 ≤ t ∧ t < T ∧
      IsUnit (dataS selAll selAll (twistP q R ε a t)).Ginv ∧
      ¬ CPen 2 1 (dilLu q R) (by norm_num) (dilTower q R) (twistU q R ε t) a (dilLam q R) := by
  have hsA : ∀ t x y, ⟪twistA q R ε a t x, y⟫ = ⟪x, twistA q R ε a t y⟫ := by
    intro t x y
    exact (dataS selAll selAll (twistP q R ε a t)).Ginv_symm (dataS_laws selAll selAll _) x y
  have hsD : ∀ x y, ⟪twistD q R ε a 0 x, y⟫ = ⟪x, twistD q R ε a 0 y⟫ := by
    intro x y
    exact ((dataS selIn selIn (twistP q R ε a 0)).Delta2_spec (dataS_laws selIn selIn _)).1 x y
  obtain ⟨t, ht0, htT, hu, hnu⟩ := guarded_separation_of_kernel_positive
    (twistA q R ε a) (twistD q R ε a 0) (twistA_continuous hq hR hroom ε a) hsA hsD h0 T hT hguard v hker hpositive
  refine ⟨t, ht0, htT, hu, ?_⟩
  change ¬ IsUnit (twistA q R ε a t - twistD q R ε a t)
  rwa [twistD_constant hq hR hroom ε a t]

#print axioms twistU
#print axioms twistP
#print axioms twistA
#print axioms twistD
#print axioms twist_agrees
#print axioms twist_cont
#print axioms twist_data_constant
#print axioms twistD_constant
#print axioms uniform_curved_family
#print axioms twist_separation_of_kernel_positive

/-- The remaining spectral obligation on the actual curved-twist family,
with mass parameter a=1. This proposition is not proved in this file. -/
def KernelPositiveCrossing (q R : ℕ) (ε : ℝ) : Prop :=
  AdalyFormal.D1Literal.PSD (twistA q R ε 1 0 - twistD q R ε 1 0) ∧
  ∃ T : ℝ, 0 < T ∧
    (∀ t : ℝ, 0 ≤ t → t < T → IsUnit (twistA q R ε 1 t)) ∧
    ∃ v : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      twistA q R ε 1 T v = 0 ∧ 0 < ⟪v, twistD q R ε 1 0 v⟫

/-- The full cofinal and arbitrary-cap bookkeeping for this IVT route.
The sole additional premise is an arbitrarily small actual spectral crossing;
no numerical sample or curvature theorem supplies that premise. -/
theorem goalNeg2_of_twist_crossings
    (hcross : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ KernelPositiveCrossing q R ε) :
    GoalNeg2 := by
  apply cofinalPencilFailure_implies_goalNeg2
  refine ⟨2, by norm_num, 1, by norm_num, ?_⟩
  intro m₀
  refine ⟨m₀+1, by omega, by omega, ?_⟩
  intro R₀
  let R := 2*(R₀+18)
  let q := 2^m₀
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(m₀+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  have hR : 2 ∣ R := ⟨R₀+18, rfl⟩
  have hR18 : 18 ≤ R := by dsimp [R]; omega
  have hroom : 17*2 ≤ R*(2*q) := by nlinarith
  refine ⟨R, by dsimp [R]; omega, ?_⟩
  intro a₀ ha₀
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let δ : ℝ := min (a₀/(3840*q)) 1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ε, hε0, hεδ, hc⟩ := hcross q hq R hR hR18 δ hδ
  let α : ℝ := 160*ε
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ := by
    have he : ε < a₀/(3840*q) := lt_of_lt_of_le hεδ (min_le_left _ _)
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3840*q)).mp he
    dsimp [α]; push_cast; nlinarith
  have heps : |ε| ≤ α/80 := by rw [abs_of_pos hε0]; dsimp [α]; linarith
  obtain ⟨h0, T, hT, hguard, v, hker, hsign⟩ := hc
  obtain ⟨t, _, _, hu, hnu⟩ := twist_separation_of_kernel_positive hq hR hroom ε 1
    h0 T hT hguard v hker hsign
  have hclass : ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹
      (twistU q R ε t) :=
    ⟨dil_coverage hq hR (by omega), dil_regular hq hR hα heps _⟩
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR
  rw [hpow]
  exact ⟨1, by norm_num, dilLu q R, α, hα, hcap, dil_torus hq R,
    dilTower q R, dil_admissible hq hR, dilLam q R, dil_lambda hq hR,
    twistU q R ε t, hclass, dilBt hq R, hBt1, hBt2, hE, hu, hnu⟩

#print axioms KernelPositiveCrossing
#print axioms goalNeg2_of_twist_crossings

end AdalyFormal.Round5.Guarded.IVTR1

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open Set
open AdalyFormal.D1Literal (PSD)

section Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- A continuous finite-dimensional carrier has a FIRST nonunit after an
initial unit and before a negative endpoint. Its preceding carriers are PSD
and units, and the first nonunit is PSD. No spectral gap is assumed. -/
theorem first_carrier_crossing
    (A : ℝ → E →L[ℝ] E) (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫)
    (hp0 : PSD (A 0)) (hu0 : IsUnit (A 0))
    (T : ℝ) (hT : 0 < T) (z : E) (hz : ⟪z, A T z⟫ < 0) :
    ∃ t : ℝ, 0 < t ∧ t < T ∧ PSD (A t) ∧ ¬ IsUnit (A t) ∧
      (∀ s : ℝ, 0 ≤ s → s < t → PSD (A s) ∧ IsUnit (A s)) ∧
      ∃ v : E, v ≠ 0 ∧ A t v = 0 := by
  obtain ⟨r, hr0, hrT, hrnu⟩ :=
    AdalyFormal.D1Literal.exists_nonunit_path A hc hs hp0 T hT z hz
  let K : Set ℝ := Icc 0 r ∩ {t | ¬ IsUnit (A t)}
  have hcl : IsClosed {t : ℝ | ¬ IsUnit (A t)} := by
    exact (Units.isOpen.preimage hc).isClosed_compl
  have hK : IsCompact K := isCompact_Icc.inter_right hcl
  have hrK : r ∈ K := ⟨⟨hr0, le_rfl⟩, hrnu⟩
  obtain ⟨t, htK, htmin⟩ := hK.exists_isLeast ⟨r, hrK⟩
  have htpos : 0 < t := by
    refine lt_of_le_of_ne htK.1.1 ?_
    intro ht
    exact htK.2 (ht ▸ hu0)
  have htT : t < T := lt_of_le_of_lt htK.1.2 hrT
  have hguard : ∀ s : ℝ, 0 ≤ s → s < t → IsUnit (A s) := by
    intro s hs0 hst
    by_contra hnu
    have hsK : s ∈ K := ⟨⟨hs0, le_trans hst.le htK.1.2⟩, hnu⟩
    exact (not_lt_of_ge (htmin hsK)) hst
  have hpsd : ∀ s : ℝ, 0 ≤ s → s ≤ t → PSD (A s) := by
    intro s hs0 hst w
    by_contra hneg
    have hw : ⟪w, A s w⟫ < 0 := lt_of_not_ge hneg
    have hspos : 0 < s := by
      rcases hs0.lt_or_eq with h | h
      · exact h
      · subst s
        exact False.elim ((not_lt_of_ge (hp0 w)) hw)
    obtain ⟨u, hu0, hus, hnu⟩ :=
      AdalyFormal.D1Literal.exists_nonunit_path A hc hs hp0 s hspos w hw
    exact hnu (hguard u hu0 (lt_of_lt_of_le hus hst))
  have hni : ¬ Function.Injective (A t) := by
    intro hi
    apply htK.2
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hi, (LinearMap.injective_iff_surjective (f := (A t).toLinearMap)).mp hi⟩
  have hk : ∃ v : E, v ≠ 0 ∧ A t v = 0 := by
    by_contra h
    apply hni
    apply (injective_iff_map_eq_zero (A t)).mpr
    intro v hv
    by_contra hv0
    exact h ⟨v, hv0, hv⟩
  exact ⟨t, htpos, htT, hpsd t htpos.le le_rfl, htK.2,
    fun s hs0 hst => ⟨hpsd s hs0 hst.le, hguard s hs0 hst⟩, hk⟩

#print axioms first_carrier_crossing

omit [FiniteDimensional ℝ E] in
/-- Error tolerance for a correction pairing, without assuming D is positive
on the ambient space. This is needed when approximate modes form a cluster. -/
theorem correction_pairing_error (D : E →L[ℝ] E) (v w : E) :
    |⟪v, D v⟫ - ⟪w, D w⟫| ≤ ‖D‖ * ‖v - w‖ * (‖v‖ + ‖w‖) := by
  have he : ⟪v, D v⟫ - ⟪w, D w⟫ =
      ⟪v - w, D v⟫ + ⟪w, D (v - w)⟫ := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [he]
  calc
    |⟪v - w, D v⟫ + ⟪w, D (v - w)⟫| ≤
        |⟪v - w, D v⟫| + |⟪w, D (v - w)⟫| := abs_add_le _ _
    _ ≤ ‖v - w‖ * ‖D v‖ + ‖w‖ * ‖D (v - w)‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ ‖v - w‖ * (‖D‖ * ‖v‖) + ‖w‖ * (‖D‖ * ‖v - w‖) := by
      gcongr
      · exact D.le_opNorm v
      · exact D.le_opNorm (v - w)
    _ = ‖D‖ * ‖v - w‖ * (‖v‖ + ‖w‖) := by ring

omit [FiniteDimensional ℝ E] in
/-- A proved approximation radius plus a strict error margin transfers the
sign to an exact vector. Small carrier residual alone is not such a radius. -/
theorem correction_positive_of_error_margin (D : E →L[ℝ] E) (v w : E)
    (h : ‖D‖ * ‖v - w‖ * (‖v‖ + ‖w‖) < ⟪w, D w⟫) :
    0 < ⟪v, D v⟫ := by
  have he := (abs_le.mp (correction_pairing_error D v w)).1
  linarith

#print axioms correction_pairing_error
#print axioms correction_positive_of_error_margin

end Abstract
end AdalyFormal.Round5.Guarded.IVTR2


namespace AdalyFormal.Round5.Guarded.IVTR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.D1Literal (PSD)

/-- First crossing for the ACTUAL curved carrier. Only endpoint statements
remain premises; the whole preceding full-carrier guard is now a conclusion. -/
theorem twist_first_carrier_crossing {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (ε a : ℝ)
    (hp0 : PSD (twistA q R ε a 0)) (hu0 : IsUnit (twistA q R ε a 0))
    (z : ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (hz : ⟪z, twistA q R ε a Real.pi z⟫ < 0) :
    ∃ t : ℝ, 0 < t ∧ t < Real.pi ∧ PSD (twistA q R ε a t) ∧
      ¬ IsUnit (twistA q R ε a t) ∧
      (∀ s : ℝ, 0 ≤ s → s < t →
        PSD (twistA q R ε a s) ∧ IsUnit (twistA q R ε a s)) ∧
      ∃ v : ↥(bondSupp (geomOf 2 1 (dilTower q R))), v ≠ 0 ∧ twistA q R ε a t v = 0 := by
  apply first_carrier_crossing (twistA q R ε a) (twistA_continuous hq hR hroom ε a)
      _ hp0 hu0 Real.pi Real.pi_pos z hz
  intro t x y
  exact (dataS selAll selAll (twistP q R ε a t)).Ginv_symm (dataS_laws selAll selAll _) x y

/-- Remaining endpoint and kernel sign obligations, NOT an established fact.
Requiring the sign at every PSD singular point is sufficient, not asserted
necessary. Unlike KernelPositiveCrossing, no interval-unit assumption occurs. -/
def EndpointSignControl (q R : ℕ) (ε : ℝ) : Prop :=
  PSD (twistA q R ε 1 0) ∧ IsUnit (twistA q R ε 1 0) ∧
  PSD (twistA q R ε 1 0 - twistD q R ε 1 0) ∧
  (∃ z : ↥(bondSupp (geomOf 2 1 (dilTower q R))), ⟪z, twistA q R ε 1 Real.pi z⟫ < 0) ∧
  ∀ t : ℝ, 0 < t → t < Real.pi → PSD (twistA q R ε 1 t) →
    ¬ IsUnit (twistA q R ε 1 t) →
    ∃ v : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      twistA q R ε 1 t v = 0 ∧ 0 < ⟪v, twistD q R ε 1 0 v⟫

theorem kernelPositiveCrossing_of_endpoint_signs {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {ε : ℝ} (h : EndpointSignControl q R ε) :
    KernelPositiveCrossing q R ε := by
  obtain ⟨hp0, hu0, hC0, ⟨z, hz⟩, hsign⟩ := h
  obtain ⟨t, ht0, htpi, hpt, hnut, hprev, _⟩ :=
    twist_first_carrier_crossing hq hR hroom ε 1 hp0 hu0 z hz
  obtain ⟨v, hv, hD⟩ := hsign t ht0 htpi hpt hnut
  exact ⟨hC0, t, ht0, fun s hs0 hst => (hprev s hs0 hst).2, v, hv, hD⟩

/-- Conditional cofinal theorem. The endpoint/kernel-sign premise is not
proved by this file, and no pinned goal is claimed closed. -/
theorem goalNeg2_of_endpoint_signs
    (hsigns : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ EndpointSignControl q R ε) :
    GoalNeg2 := by
  apply goalNeg2_of_twist_crossings
  intro q hq R hR hR18 δ hδ
  obtain ⟨ε, hε, hεδ, hsigns⟩ := hsigns q hq R hR hR18 δ hδ
  refine ⟨ε, hε, hεδ, kernelPositiveCrossing_of_endpoint_signs hq hR ?_ hsigns⟩
  nlinarith

#print axioms twist_first_carrier_crossing
#print axioms EndpointSignControl
#print axioms kernelPositiveCrossing_of_endpoint_signs
#print axioms goalNeg2_of_endpoint_signs

/-! A second defect can eliminate an unobserved cluster direction numerically.
The following permits arbitrary bounded amplitude masks with the ACTUAL frozen
class and unchanged tower. It establishes no spectral property for any mask. -/
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

namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.D1Literal (BdPt sing P1 P2)

/-- Right outgoing boundary bond of the actual dilated tower. -/
def rightSite {q : ℕ} (hq : 0 < q) (R : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  fun μ => ⟨if μ = 0 then 12*(R*q)+12*q-1 else 0,
    by rw [dil_fine_size hq]; split_ifs <;> omega⟩

theorem rightSite_bd {q : ℕ} (hq : 0 < q) (R : ℕ) :
    BdPt ((dilTower q R).Om 0) (rightSite hq R) := by
  have hv : ((rightSite hq R) 0).val = 12*(R*q)+12*q-1 := by simp [rightSite]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
    rw [hv]; omega
  · change ¬ (4*q ≤ _ ∧ _ < 12*(R*q)+12*q)
    rw [dil_shift_zero hq R, if_pos rfl, hv, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro z ν hν
    change (4*q ≤ _ ∧ _ < 12*(R*q)+12*q) ↔ (4*q ≤ _ ∧ _ < 12*(R*q)+12*q)
    rw [dil_shift_zero hq R, if_neg hν]
  · intro ν heq
    have hn : 1 < scaleUp 2 1 (dilLu q R) ν + 1 := by
      rw [dil_fine_size hq]; split_ifs <;> omega
    have hh := congrArg (fun y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) => (y ν).val) heq
    simp only [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one'] at hh
    rw [Nat.mod_eq_of_lt hn] at hh
    have hw := ((rightSite hq R) ν).isLt
    rcases Nat.lt_or_ge (((rightSite hq R) ν).val+1) (scaleUp 2 1 (dilLu q R) ν+1) with h | h
    · rw [Nat.mod_eq_of_lt h] at hh; omega
    · have he : ((rightSite hq R) ν).val+1 = scaleUp 2 1 (dilLu q R) ν+1 := by omega
      rw [he, Nat.mod_self] at hh; omega

theorem twist_eq_Uth_off_defect {q R : ℕ} (ε t : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : (e.1 0).val ≠ 2*(R*q)+4*q) :
    twistU q R ε t e = AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t e := by
  classical
  have hp : ¬ dilPattern q R e := fun h => he h.1
  unfold twistU dilU
  split_ifs with hz
  · rfl
  · rw [Ug_zero]
    simp [AdalyFormal.D1Literal.Uth, hz]

/-- Every link around a plaquette based at the right face agrees exactly
with the old flat-interior exterior twist. Curvature lies far to its left. -/
theorem right_face_agrees {q R : ℕ} (hq : 0 < q) (ε t : ℝ)
    (p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)))
    (hp : (p.1 0).val = 12*(R*q)+12*q-1) :
    ∀ e ∈ periodicPlaquetteBoundaryEdges p,
      twistU q R ε t e = AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t e := by
  have hn : (p.1 0).val ≠ 2*(R*q)+4*q := by omega
  have hns (μ : Fin 3) : ((periodicLatticeShift p.1 μ) 0).val ≠ 2*(R*q)+4*q := by
    rw [dil_shift_zero hq R, hp]
    split_ifs
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · omega
  intro e he
  rcases (AdalyFormal.StatementLaneR6.edge_mem p e).mp he with rfl | rfl | rfl | rfl
  · exact twist_eq_Uth_off_defect ε t _ hn
  · exact twist_eq_Uth_off_defect ε t _ (hns _)
  · exact twist_eq_Uth_off_defect ε t _ (hns _)
  · exact twist_eq_Uth_off_defect ε t _ hn

/-- The actual curved family's boundary test still has the exact -4 form. -/
theorem twist_delta_pi {q R : ℕ} (hq : 0 < q) (ε : ℝ) (X : SuTwo) :
    ⟪sing (rightSite hq R, (0 : Fin 3)) X,
      AdalyFormal.StatementLaneR6.deltaKLocCLM (twistU q R ε Real.pi) Set.univ
        (sing (rightSite hq R, (0 : Fin 3)) X)⟫ = -4 * hsInner X X := by
  have hbd := rightSite_bd hq R
  have hback (ν : {ν : Fin 3 // 0 < ν}) :
      ((periodicLatticeShiftBack (rightSite hq R) ν.1) 0).val = 12*(R*q)+12*q-1 := by
    have hh := congrArg (fun y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) => (y 0).val)
      (periodicLatticeShift_shiftBack (rightSite hq R) ν.1)
    rw [dil_shift_zero hq R, if_neg (ne_of_gt ν.2)] at hh
    simpa [rightSite] using hh
  apply AdalyFormal.D1Literal.delta_value _ _ X hbd.side
  · intro ν
    rw [AdalyFormal.StatementLaneR6.holonomyElem_congr
      (right_face_agrees hq ε Real.pi (AdalyFormal.D1Literal.P1 (rightSite hq R) ν) (by simp [AdalyFormal.D1Literal.P1, rightSite]))]
    rw [hbd.holonomy1]
    exact AdalyFormal.D1Literal.uθ_pi_coe
  · intro ν
    rw [AdalyFormal.StatementLaneR6.holonomyElem_congr
      (right_face_agrees hq ε Real.pi (P2 (rightSite hq R) ν) (hback ν))]
    rw [hbd.holonomy2]
    exact AdalyFormal.D1Literal.uθ_pi_coe
  · intro ν
    rw [twist_eq_Uth_off_defect ε Real.pi _ (by have := hback ν; dsimp; omega)]
    exact hbd.hU2 Real.pi ν

/-- A negative endpoint for the genuine curved carrier at every dilated scale.
No smallness, numerical sign, or first-crossing guard is assumed here. -/
theorem twistA_pi_negative {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (ε : ℝ) :
    ∃ v : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      ⟪v, twistA q R ε 1 Real.pi v⟫ < 0 := by
  let x := rightSite hq R
  let X := AdalyFormal.Balaban.CovariantOperators.suTwoWitness
  have hX : X ≠ 0 := AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero
  have hbd := rightSite_bd hq R
  have hS := dil_admissible hq hR
  have hRM : 3 ≤ R*(2*q) := by omega
  have h9 : 9*2 ≤ R*(2*q) := by omega
  have hmem : sing (x, (0 : Fin 3)) X ∈ bondSupp (geomOf 2 1 (dilTower q R)) :=
    AdalyFormal.D1Literal.sing_mem_bondSupp _ hbd.hx X
  let v : ↥(bondSupp (twistP q R ε 1 Real.pi).G) := ⟨sing (x, (0 : Fin 3)) X, hmem⟩
  have hn : 0 < hsInner X X := real_inner_self_pos.mpr hX
  refine ⟨v, ?_⟩
  change ⟪v, (dataS selAll selAll (twistP q R ε 1 Real.pi)).Ginv v⟫ < 0
  rw [BaseDataS.inner_Ginv]
  have hDpi : ⟪v, (dataS selAll selAll (twistP q R ε 1 Real.pi)).Dpi v⟫ = -4*hsInner X X := by
    have he := AdalyFormal.D1Literal.E0_Dpi_inner AdalyFormal.D1Literal.selAll
      (geomOf 2 1 (dilTower q R)) (twistU q R ε Real.pi) 1 v
    refine he.trans ?_
    have hW : Wop (geomOf 2 1 (dilTower q R)) (twistU q R ε Real.pi) 1
        (iE (geomOf 2 1 (dilTower q R)) v) = sing (x, (0 : Fin 3)) X :=
      AdalyFormal.D1Literal.Wop_sing hS hRM hbd _ 1 X
    rw [hW]
    exact twist_delta_pi hq ε X
  have hT : (dataS selAll selAll (twistP q R ε 1 Real.pi)).T v = 0 := by
    exact AdalyFormal.D1Literal.Tfull_sing_zero hS hRM hbd _ X
  have hM : ⟪v, (dataS selAll selAll (twistP q R ε 1 Real.pi)).Mass v⟫ ≤ hsInner X X := by
    have he : ⟪v, (dataS selAll selAll (twistP q R ε 1 Real.pi)).Mass v⟫ =
        ⟪sing (x, (0 : Fin 3)) X,
          MassFull (geomOf 2 1 (dilTower q R)) 1
            (bondSectorOf (geomOf 2 1 (dilTower q R)) (twistU q R ε Real.pi))
            (sing (x, (0 : Fin 3)) X)⟫ := by
      change ⟪v, ((pE _).comp ((MassFull _ _ _).comp (iE _))) v⟫ = _
      simp only [ContinuousLinearMap.comp_apply]
      rw [pE_inner_right]
      rfl
    rw [he]
    simpa only [one_mul] using AdalyFormal.D1Literal.Mass_sing_le hS (by norm_num) h9 hbd
      (twistU q R ε Real.pi) 1 zero_le_one X
  rw [hDpi, hT]
  simp only [norm_zero]
  nlinarith

#print axioms rightSite
#print axioms rightSite_bd
#print axioms twist_eq_Uth_off_defect
#print axioms right_face_agrees
#print axioms twist_delta_pi
#print axioms twistA_pi_negative

end AdalyFormal.Round5.Guarded.IVTR2

namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.D1Literal (PSD)

/-- No endpoint-negative premise remains for the actual curved family. -/
theorem twist_first_crossing_of_initial {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (ε : ℝ)
    (hp0 : PSD (twistA q R ε 1 0)) (hu0 : IsUnit (twistA q R ε 1 0)) :
    ∃ t : ℝ, 0 < t ∧ t < Real.pi ∧ PSD (twistA q R ε 1 t) ∧
      ¬ IsUnit (twistA q R ε 1 t) ∧
      (∀ s : ℝ, 0 ≤ s → s < t →
        PSD (twistA q R ε 1 s) ∧ IsUnit (twistA q R ε 1 s)) ∧
      ∃ v : ↥(bondSupp (geomOf 2 1 (dilTower q R))), v ≠ 0 ∧ twistA q R ε 1 t v = 0 := by
  obtain ⟨z, hz⟩ := twistA_pi_negative hq hR hroom ε
  exact twist_first_carrier_crossing hq hR hroom ε 1 hp0 hu0 z hz

/-- These are the remaining hypotheses, not a replacement goal and not a
proved class theorem. The kernel sign requirement is sufficient, not necessary. -/
def InitialKernelControl (q R : ℕ) (ε : ℝ) : Prop :=
  PSD (twistA q R ε 1 0) ∧ IsUnit (twistA q R ε 1 0) ∧
  PSD (twistA q R ε 1 0 - twistD q R ε 1 0) ∧
  ∀ t : ℝ, 0 < t → t < Real.pi → PSD (twistA q R ε 1 t) →
    ¬ IsUnit (twistA q R ε 1 t) →
    ∃ v : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      twistA q R ε 1 t v = 0 ∧ 0 < ⟪v, twistD q R ε 1 0 v⟫

theorem endpoint_control_of_initial_kernel {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {ε : ℝ} (h : InitialKernelControl q R ε) :
    EndpointSignControl q R ε :=
  ⟨h.1, h.2.1, h.2.2.1, twistA_pi_negative hq hR hroom ε, h.2.2.2⟩

/-- The remaining cofinal premise is unproved. All goals retain their exact pin. -/
theorem goalNeg2_of_initial_kernel_control
    (hcontrol : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ InitialKernelControl q R ε) :
    GoalNeg2 := by
  apply goalNeg2_of_endpoint_signs
  intro q hq R hR hR18 δ hδ
  obtain ⟨ε, hε, hεδ, hc⟩ := hcontrol q hq R hR hR18 δ hδ
  exact ⟨ε, hε, hεδ, endpoint_control_of_initial_kernel hq hR (by nlinarith) hc⟩

#print axioms twist_first_crossing_of_initial
#print axioms InitialKernelControl
#print axioms endpoint_control_of_initial_kernel
#print axioms goalNeg2_of_initial_kernel_control

end AdalyFormal.Round5.Guarded.IVTR2

/-!
Round 8: sign-free separation.

The carrier guard asks only that the all-plaquette carrier A be a UNIT; it does
not ask that A be positive semidefinite.  Along the exterior twist the carrier
passes its first crossing and stays an indefinite unit until the next one,
and every such angle is in the class.  Consequently the sign of the correction
on the crossing kernel is irrelevant for separation: a positive pairing makes
A-D singular before the crossing (where A is PSD), a negative pairing makes
A-D singular after it (where A is an indefinite unit).  The round-5 bridge
needed the positive sign; the premises below need neither sign.

Nothing here proves a pinned goal.  The family premises are explicit,
unproved hypotheses; the abstract lemmas are finite-dimensional facts.
-/
namespace AdalyFormal.Round8.Guarded.SignFree

open scoped RealInnerProductSpace
open Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.D1Literal (PSD)

section Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Sign-free separation.  If the carrier path stays a unit on `[t₀,t₁]` while
the corrected path goes from PSD to having a negative direction, some angle in
`[t₀,t₁)` has a unit carrier and a non-unit corrected carrier.  The carrier may
be indefinite on the whole interval. -/
theorem separation_of_sign_change
    (A : ℝ → E →L[ℝ] E) (D : E →L[ℝ] E) (hc : Continuous A)
    (hsA : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫)
    (hsD : ∀ x y, ⟪D x, y⟫ = ⟪x, D y⟫)
    (t₀ t₁ : ℝ) (h01 : t₀ ≤ t₁)
    (hguard : ∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (A t))
    (h₀ : PSD (A t₀ - D)) (w : E) (h₁ : ⟪w, (A t₁ - D) w⟫ < 0) :
    ∃ t : ℝ, t₀ ≤ t ∧ t < t₁ ∧ IsUnit (A t) ∧ ¬ IsUnit (A t - D) := by
  have hlt : t₀ < t₁ := by
    rcases h01.lt_or_eq with h | h
    · exact h
    · exfalso
      have := h₀ w
      rw [h] at this
      linarith
  let F : ℝ → E →L[ℝ] E := fun s => A (t₀ + s) - D
  have hFc : Continuous F :=
    (hc.comp (continuous_const.add continuous_id)).sub continuous_const
  have hFs : ∀ s x y, ⟪F s x, y⟫ = ⟪x, F s y⟫ := by
    intro s x y
    simp only [F, sub_apply, inner_sub_left, inner_sub_right, hsA, hsD]
  have hF0 : PSD (F 0) := by
    intro v
    simpa [F] using h₀ v
  have hFT : ⟪w, F (t₁ - t₀) w⟫ < 0 := by
    simpa [F] using h₁
  obtain ⟨s, hs0, hsT, hnu⟩ := AdalyFormal.D1Literal.exists_nonunit_path F hFc hFs hF0
    (t₁ - t₀) (by linarith) w hFT
  refine ⟨t₀ + s, by linarith, by linarith, hguard _ (by linarith) (by linarith), ?_⟩
  simpa [F] using hnu

omit [FiniteDimensional ℝ E] in
/-- The round-5 positive-kernel data produce a sign-change interval, so the
sign-free premise is implied by the old one (it is weaker, not stronger). -/
theorem sign_change_of_kernel_positive
    (A : ℝ → E →L[ℝ] E) (D : E →L[ℝ] E) (hc : Continuous A)
    (T : ℝ) (hT : 0 < T)
    (hguard : ∀ t, 0 ≤ t → t < T → IsUnit (A t))
    (v : E) (hker : A T v = 0) (hpositive : 0 < ⟪v, D v⟫) :
    ∃ t₁ : ℝ, 0 ≤ t₁ ∧ t₁ < T ∧ (∀ t, 0 ≤ t → t ≤ t₁ → IsUnit (A t)) ∧
      ⟪v, (A t₁ - D) v⟫ < 0 := by
  let f : ℝ → ℝ := fun t => ⟪v, (A t - D) v⟫
  have hf : Continuous f := by
    have : Continuous fun t => (A t - D) v :=
      (hc.sub continuous_const).clm_apply continuous_const
    exact continuous_const.inner this
  have hfT : f T < 0 := by
    simp only [f, sub_apply, hker, zero_sub, inner_neg_right]
    linarith
  have hev : ∀ᶠ t in nhds T, f t < 0 :=
    Filter.Tendsto.eventually (hf.tendsto T) (gt_mem_nhds hfT)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let t₁ : ℝ := max 0 (T - δ/2)
  have ht₁0 : 0 ≤ t₁ := le_max_left _ _
  have ht₁T : t₁ < T := max_lt hT (by linarith)
  have hdist : dist t₁ T < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor
    · have : T - δ/2 ≤ t₁ := le_max_right _ _
      linarith
    · linarith
  refine ⟨t₁, ht₁0, ht₁T, fun t ht0 ht1 => hguard t ht0 (lt_of_le_of_lt ht1 ht₁T), ?_⟩
  exact hball hdist

omit [FiniteDimensional ℝ E] in
/-- In the post-crossing regime the separating interval starts at an
INDEFINITE carrier unit, and the correction is negative on the witness. -/
theorem post_crossing_witness (X D : E →L[ℝ] E) (h₀ : PSD (X - D))
    (x : E) (hx : ⟪x, X x⟫ < 0) : ¬ PSD X ∧ ⟪x, D x⟫ < 0 := by
  refine ⟨fun hp => (not_lt_of_ge (hp x)) hx, ?_⟩
  have := h₀ x
  simp only [sub_apply, inner_sub_right] at this
  linarith

#print axioms separation_of_sign_change
#print axioms sign_change_of_kernel_positive
#print axioms post_crossing_witness

end Abstract

/-! Certificates for the interval guard.  On the post-crossing interval the
carrier is indefinite, so positivity cannot certify the guard.  A symmetric
operator that is negative definite on one subspace and positive definite on
another of complementary dimension is a unit (no spectral theorem needed), and
along the exterior sine/cosine pencil the rescaled carrier `A t / sin t` is
Loewner-nonincreasing on `(0, pi/2]` once its constant and cosine parts are
PSD.  Together these reduce the interval guard to two endpoint certificates. -/
section Certificates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem unit_of_definite_complements (X : E →L[ℝ] E)
    (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (U V : Submodule ℝ E)
    (hU : ∀ x ∈ U, x ≠ 0 → ⟪x, X x⟫ < 0)
    (hV : ∀ x ∈ V, x ≠ 0 → 0 < ⟪x, X x⟫)
    (hdim : Module.finrank ℝ E ≤ Module.finrank ℝ U + Module.finrank ℝ V) :
    IsUnit X := by
  have hinj : Function.Injective X := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have hxU : x ∉ U := by
      intro hm
      have h := hU x hm hx0
      rw [hx, inner_zero_right] at h
      exact lt_irrefl 0 h
    let U' : Submodule ℝ E := U ⊔ Submodule.span ℝ {x}
    have hneg : ∀ y ∈ U', ⟪y, X y⟫ ≤ 0 := by
      intro y hy
      obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hcross : ⟪c • x, X u⟫ = 0 := by
        rw [real_inner_smul_left, ← hs x u, hx, inner_zero_left, mul_zero]
      have heq : ⟪u + c • x, X (u + c • x)⟫ = ⟪u, X u⟫ := by
        rw [map_add, map_smul, hx, smul_zero, add_zero, inner_add_left, hcross, add_zero]
      rw [heq]
      by_cases hu0 : u = 0
      · rw [hu0, map_zero, inner_zero_right]
      · exact (hU u hu hu0).le
    have hlt : U < U' := SetLike.lt_iff_le_and_exists.mpr
      ⟨le_sup_left, x, Submodule.mem_sup_right (Submodule.mem_span_singleton_self x), hxU⟩
    have hrk : Module.finrank ℝ U < Module.finrank ℝ U' := Submodule.finrank_lt_finrank_of_lt hlt
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq U' V
    have hle : Module.finrank ℝ ↥(U' ⊔ V) ≤ Module.finrank ℝ E := Submodule.finrank_le _
    have hpos : Module.finrank ℝ ↥(U' ⊓ V) ≠ 0 := by omega
    have hne : U' ⊓ V ≠ ⊥ := fun h => hpos (Submodule.finrank_eq_zero.mpr h)
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have h1 := hneg y (Submodule.mem_inf.mp hy).1
    have h2 := hV y (Submodule.mem_inf.mp hy).2 hy0
    linarith
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (X : E →ₗ[ℝ] E))).mp hinj⟩

/-- A positively rescaled Loewner-nonincreasing path: a negative-definite
subspace at the left end and a positive-definite subspace at the right end,
of complementary dimension, certify a unit at every intermediate point. -/
theorem units_of_scaled_certificates (A : ℝ → E →L[ℝ] E) (g : ℝ → ℝ)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫) (t₀ t₁ : ℝ)
    (hg : ∀ t, t₀ ≤ t → t ≤ t₁ → 0 < g t)
    (hmono : ∀ s t, t₀ ≤ s → s ≤ t → t ≤ t₁ → ∀ x, ⟪x, A t x⟫ / g t ≤ ⟪x, A s x⟫ / g s)
    (U V : Submodule ℝ E)
    (hU : ∀ x ∈ U, x ≠ 0 → ⟪x, A t₀ x⟫ < 0)
    (hV : ∀ x ∈ V, x ≠ 0 → 0 < ⟪x, A t₁ x⟫)
    (hdim : Module.finrank ℝ E ≤ Module.finrank ℝ U + Module.finrank ℝ V) :
    ∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (A t) := by
  intro t ht0 ht1
  have h01 : t₀ ≤ t₁ := le_trans ht0 ht1
  have hgt := hg t ht0 ht1
  refine unit_of_definite_complements (A t) (hs t) U V ?_ ?_ hdim
  · intro x hx hx0
    have hn : ⟪x, A t₀ x⟫ / g t₀ < 0 := div_neg_of_neg_of_pos (hU x hx hx0) (hg t₀ le_rfl h01)
    have hq : ⟪x, A t x⟫ / g t < 0 := lt_of_le_of_lt (hmono t₀ t le_rfl ht0 ht1 x) hn
    have := mul_neg_of_neg_of_pos hq hgt
    rwa [div_mul_cancel₀ _ hgt.ne'] at this
  · intro x hx hx0
    have hp : 0 < ⟪x, A t₁ x⟫ / g t₁ := div_pos (hV x hx hx0) (hg t₁ h01 le_rfl)
    have hq : 0 < ⟪x, A t x⟫ / g t := lt_of_lt_of_le hp (hmono t t₁ ht0 ht1 le_rfl x)
    have := mul_pos hq hgt
    rwa [div_mul_cancel₀ _ hgt.ne'] at this

omit [FiniteDimensional ℝ E] in
/-- The exterior sine/cosine pencil, rescaled by `1/sin`, is nonincreasing on
`(0, pi/2]` when its constant part and its cosine part are PSD.  The sine part
is arbitrary (it is indefinite along the twist). -/
theorem pencil_rescaled_antitone (B Θ₀ Θ₁ : E →L[ℝ] E) (hB : PSD B) (hΘ : PSD Θ₀)
    {s t : ℝ} (hs0 : 0 < s) (hst : s ≤ t) (htπ : t ≤ Real.pi/2) (x : E) :
    ⟪x, (B + Real.cos t • Θ₀ + Real.sin t • Θ₁) x⟫ / Real.sin t ≤
      ⟪x, (B + Real.cos s • Θ₀ + Real.sin s • Θ₁) x⟫ / Real.sin s := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsin_s : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0 (by linarith)
  have hsin_t : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsin_le : Real.sin s ≤ Real.sin t :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) htπ hst
  have hcos_le : Real.cos t ≤ Real.cos s :=
    Real.cos_le_cos_of_nonneg_of_le_pi hs0.le (by linarith) hst
  have hcos_t : 0 ≤ Real.cos t := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) htπ
  have hb := hB x
  have hθ := hΘ x
  have expand : ∀ r : ℝ, ⟪x, (B + Real.cos r • Θ₀ + Real.sin r • Θ₁) x⟫ =
      ⟪x, B x⟫ + Real.cos r * ⟪x, Θ₀ x⟫ + Real.sin r * ⟪x, Θ₁ x⟫ := by
    intro r
    simp only [add_apply, smul_apply, inner_add_right,
      real_inner_smul_right]
  rw [expand t, expand s, div_le_div_iff₀ hsin_t hsin_s]
  have h1 : ⟪x, B x⟫ * Real.sin s ≤ ⟪x, B x⟫ * Real.sin t := mul_le_mul_of_nonneg_left hsin_le hb
  have h2 : Real.cos t * Real.sin s ≤ Real.cos s * Real.sin t :=
    mul_le_mul hcos_le hsin_le hsin_s.le (le_trans hcos_t hcos_le)
  have h3 := mul_le_mul_of_nonneg_left h2 hθ
  nlinarith [h1, h3]

/-- Pencil form plus two endpoint certificates give the whole interval guard. -/
theorem pencil_units_of_certificates (A : ℝ → E →L[ℝ] E) (B Θ₀ Θ₁ : E →L[ℝ] E)
    (hA : ∀ t, A t = B + Real.cos t • Θ₀ + Real.sin t • Θ₁)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫)
    (hB : PSD B) (hΘ : PSD Θ₀) (t₀ t₁ : ℝ) (h0 : 0 < t₀) (h1 : t₁ ≤ Real.pi/2)
    (U V : Submodule ℝ E)
    (hU : ∀ x ∈ U, x ≠ 0 → ⟪x, A t₀ x⟫ < 0)
    (hV : ∀ x ∈ V, x ≠ 0 → 0 < ⟪x, A t₁ x⟫)
    (hdim : Module.finrank ℝ E ≤ Module.finrank ℝ U + Module.finrank ℝ V) :
    ∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (A t) := by
  refine units_of_scaled_certificates A Real.sin hs t₀ t₁ ?_ ?_ U V hU hV hdim
  · intro t ht0 ht1
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  · intro s t hs0 hst ht1 x
    rw [hA s, hA t]
    exact pencil_rescaled_antitone B Θ₀ Θ₁ hB hΘ (by linarith) hst (le_trans ht1 h1) x

#print axioms unit_of_definite_complements
#print axioms units_of_scaled_certificates
#print axioms pencil_rescaled_antitone
#print axioms pencil_units_of_certificates

end Certificates

/-- The weakest premise along the actual curved twist family (mass a = 1):
some exterior angle has a unit carrier and a non-unit corrected carrier. -/
def TwistSeparation (q R : ℕ) (ε : ℝ) : Prop :=
  ∃ t : ℝ, IsUnit (twistA q R ε 1 t) ∧ ¬ IsUnit (twistA q R ε 1 t - twistD q R ε 1 t)

/-- Sign-free spectral premise on the actual curved family.  It asks for an
interval of carrier units on which the corrected form passes from PSD to a
negative direction.  No sign of the kernel correction and no positivity of the
carrier on the interval is required.  This proposition is NOT proved here. -/
def SignChangeControl (q R : ℕ) (ε : ℝ) : Prop :=
  ∃ t₀ t₁ : ℝ, t₀ ≤ t₁ ∧
    (∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (twistA q R ε 1 t)) ∧
    PSD (twistA q R ε 1 t₀ - twistD q R ε 1 0) ∧
    ∃ w : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      ⟪w, (twistA q R ε 1 t₁ - twistD q R ε 1 0) w⟫ < 0

theorem twistSeparation_of_signChange {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {ε : ℝ} (h : SignChangeControl q R ε) :
    TwistSeparation q R ε := by
  obtain ⟨t₀, t₁, h01, hguard, h₀, w, h₁⟩ := h
  have hsA : ∀ t x y, ⟪twistA q R ε 1 t x, y⟫ = ⟪x, twistA q R ε 1 t y⟫ := by
    intro t x y
    exact (dataS selAll selAll (twistP q R ε 1 t)).Ginv_symm (dataS_laws selAll selAll _) x y
  have hsD : ∀ x y, ⟪twistD q R ε 1 0 x, y⟫ = ⟪x, twistD q R ε 1 0 y⟫ := by
    intro x y
    exact ((dataS selIn selIn (twistP q R ε 1 0)).Delta2_spec (dataS_laws selIn selIn _)).1 x y
  obtain ⟨t, -, -, hu, hnu⟩ := separation_of_sign_change (twistA q R ε 1) (twistD q R ε 1 0)
    (twistA_continuous hq hR hroom ε 1) hsA hsD t₀ t₁ h01 hguard h₀ w h₁
  refine ⟨t, hu, ?_⟩
  rwa [twistD_constant hq hR hroom ε 1 t]

/-- The round-5 kernel premise implies the sign-free premise. -/
theorem signChange_of_kernelPositiveCrossing {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {ε : ℝ} (h : KernelPositiveCrossing q R ε) :
    SignChangeControl q R ε := by
  obtain ⟨h0, T, hT, hguard, v, hker, hpos⟩ := h
  obtain ⟨t₁, ht₁0, _, hg, hneg⟩ := sign_change_of_kernel_positive (twistA q R ε 1)
    (twistD q R ε 1 0) (twistA_continuous hq hR hroom ε 1) T hT hguard v hker hpos
  exact ⟨0, t₁, ht₁0, fun t ht0 ht1 => hg t ht0 ht1, h0, v, hneg⟩

theorem signChange_of_initialKernelControl {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {ε : ℝ} (h : InitialKernelControl q R ε) :
    SignChangeControl q R ε :=
  signChange_of_kernelPositiveCrossing hq hR hroom
    (kernelPositiveCrossing_of_endpoint_signs hq hR hroom
      (endpoint_control_of_initial_kernel hq hR hroom h))

/-- Cofinal bookkeeping with the weakest family premise.  Same witnesses as
the round-5 bridge: m = m₀+1, q = 2^m₀, R = 2(R₀+18) chosen BEFORE the cap,
then ε below min(a₀/(3840 q), 1) and α = 160 ε. -/
theorem goalNeg2_of_twist_separation
    (hsep : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ TwistSeparation q R ε) :
    GoalNeg2 := by
  apply cofinalPencilFailure_implies_goalNeg2
  refine ⟨2, by norm_num, 1, by norm_num, ?_⟩
  intro m₀
  refine ⟨m₀+1, by omega, by omega, ?_⟩
  intro R₀
  let R := 2*(R₀+18)
  let q := 2^m₀
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(m₀+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  have hR : 2 ∣ R := ⟨R₀+18, rfl⟩
  have hR18 : 18 ≤ R := by dsimp [R]; omega
  refine ⟨R, by dsimp [R]; omega, ?_⟩
  intro a₀ ha₀
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let δ : ℝ := min (a₀/(3840*q)) 1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ε, hε0, hεδ, t, hu, hnu⟩ := hsep q hq R hR hR18 δ hδ
  let α : ℝ := 160*ε
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ := by
    have he : ε < a₀/(3840*q) := lt_of_lt_of_le hεδ (min_le_left _ _)
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3840*q)).mp he
    dsimp [α]; push_cast; nlinarith
  have heps : |ε| ≤ α/80 := by rw [abs_of_pos hε0]; dsimp [α]; linarith
  have hclass : ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹
      (twistU q R ε t) :=
    ⟨dil_coverage hq hR (by omega), dil_regular hq hR hα heps _⟩
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR
  rw [hpow]
  exact ⟨1, by norm_num, dilLu q R, α, hα, hcap, dil_torus hq R,
    dilTower q R, dil_admissible hq hR, dilLam q R, dil_lambda hq hR,
    twistU q R ε t, hclass, dilBt hq R, hBt1, hBt2, hE, hu, hnu⟩

theorem goalNeg1_of_twist_separation
    (hsep : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ TwistSeparation q R ε) :
    GoalNeg1 :=
  goalNeg1_iff_goalNeg2.mpr (goalNeg2_of_twist_separation hsep)

/-- Sign-free cofinal bridge.  Its premise is weaker than the round-5
`InitialKernelControl` premise (`signChange_of_initialKernelControl`), and it
is also met in the negative-sign (post-crossing) regime.  It is NOT proved. -/
theorem goalNeg2_of_sign_change_control
    (hcontrol : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ SignChangeControl q R ε) :
    GoalNeg2 := by
  apply goalNeg2_of_twist_separation
  intro q hq R hR hR18 δ hδ
  obtain ⟨ε, hε, hεδ, hc⟩ := hcontrol q hq R hR hR18 δ hδ
  exact ⟨ε, hε, hεδ, twistSeparation_of_signChange hq hR (by nlinarith) hc⟩

/-- What the positive reading demands of this family.  If `GoalPos1` holds
then, at every large scale and radius and every small enough curvature, NO
exterior angle separates: every crossing of A-D along the twist is a crossing
of A.  This is the contrapositive content of the bridge, stated directly. -/
theorem goalPos1_forces_no_twist_separation (h : GoalPos1) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ¬ TwistSeparation (2^(m-1)) R ε := by
  obtain ⟨m₀, hm₀, hm⟩ := h 2 le_rfl 1 one_pos
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR₀⟩ := hm m hm'
  refine ⟨R₀, fun R hR hR2 hR18 => ?_⟩
  obtain ⟨a₀, ha₀, hcpen⟩ := hR₀ R hR
  have hm1 : 1 ≤ m := le_trans hm₀ hm'
  let q := 2^(m-1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^m = 2*q := by
    dsimp [q]
    rw [← pow_succ', Nat.sub_add_cancel hm1]
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨min (a₀/(3840*q)) 1, by positivity, fun ε hε0 hεδ => ?_⟩
  rintro ⟨t, hu, hnu⟩
  let α : ℝ := 160*ε
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ)*((2^m : ℕ) : ℝ)*α ≤ a₀ := by
    have he : ε < a₀/(3840*q) := lt_of_lt_of_le hεδ (min_le_left _ _)
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3840*q)).mp he
    rw [hpow]
    dsimp [α]; push_cast; nlinarith
  have heps : |ε| ≤ α/80 := by rw [abs_of_pos hε0]; dsimp [α]; linarith
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR2
  have hT := dil_torus hq R
  have hS := dil_admissible hq hR2
  have hL := dil_lambda hq hR2
  have hcl : ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (twistU q R ε t) :=
    ⟨dil_coverage hq hR2 (by omega), dil_regular hq hR2 hα heps _⟩
  rw [← hpow] at hT hS hL hcl
  have key := hcpen 1 le_rfl (dilLu q R) α hα hcap hT (dilTower q R) hS (dilLam q R) hL
    (twistU q R ε t) hcl ⟨dilBt hq R, hBt1, hBt2, hE⟩ hu
  exact hnu key

/-- The exterior pencil identity on the actual family, with PSD constant and
cosine parts.  Checked numerically (round-6 path_identity.py at 80 digits;
sepcheck.py, error below 1e-400 at 400 digits) and algebraically derivable
from the plaquette formula; NOT proved here. -/
def TwistPencil (q R : ℕ) (ε : ℝ) : Prop :=
  ∃ B Θ₀ Θ₁ : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
    PSD B ∧ PSD Θ₀ ∧ ∀ t : ℝ, twistA q R ε 1 t = B + Real.cos t • Θ₀ + Real.sin t • Θ₁

/-- Pointwise data at two angles in `(0, pi/2]` that imply `SignChangeControl`:
the pencil identity, a negative-definite subspace of the carrier at `t₀`, a
positive-definite subspace at `t₁` of complementary dimension, the corrected
form PSD at `t₀` and negative somewhere at `t₁`.  NOT proved here. -/
def PencilCertificates (q R : ℕ) (ε : ℝ) : Prop :=
  TwistPencil q R ε ∧
  ∃ t₀ t₁ : ℝ, 0 < t₀ ∧ t₀ ≤ t₁ ∧ t₁ ≤ Real.pi/2 ∧
    (∃ U V : Submodule ℝ ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      (∀ x ∈ U, x ≠ 0 → ⟪x, twistA q R ε 1 t₀ x⟫ < 0) ∧
      (∀ x ∈ V, x ≠ 0 → 0 < ⟪x, twistA q R ε 1 t₁ x⟫) ∧
      Module.finrank ℝ ↥(bondSupp (geomOf 2 1 (dilTower q R))) ≤
        Module.finrank ℝ U + Module.finrank ℝ V) ∧
    PSD (twistA q R ε 1 t₀ - twistD q R ε 1 0) ∧
    ∃ w : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      ⟪w, (twistA q R ε 1 t₁ - twistD q R ε 1 0) w⟫ < 0

theorem signChange_of_pencilCertificates {q R : ℕ} {ε : ℝ} (h : PencilCertificates q R ε) :
    SignChangeControl q R ε := by
  obtain ⟨⟨B, Θ₀, Θ₁, hB, hΘ, hA⟩, t₀, t₁, h0, h01, h1, ⟨U, V, hU, hV, hdim⟩, hC0, w, hw⟩ := h
  have hs : ∀ t x y, ⟪twistA q R ε 1 t x, y⟫ = ⟪x, twistA q R ε 1 t y⟫ := by
    intro t x y
    exact (dataS selAll selAll (twistP q R ε 1 t)).Ginv_symm (dataS_laws selAll selAll _) x y
  exact ⟨t₀, t₁, h01, pencil_units_of_certificates (twistA q R ε 1) B Θ₀ Θ₁ hA hs hB hΘ
    t₀ t₁ h0 h1 U V hU hV hdim, hC0, w, hw⟩

theorem goalNeg2_of_pencil_certificates
    (hcert : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ PencilCertificates q R ε) :
    GoalNeg2 := by
  apply goalNeg2_of_sign_change_control
  intro q hq R hR hR18 δ hδ
  obtain ⟨ε, hε, hεδ, hc⟩ := hcert q hq R hR hR18 δ hδ
  exact ⟨ε, hε, hεδ, signChange_of_pencilCertificates hc⟩

/-- The weakest cofinal premise on the twist family, matching the pinned
quantifiers: infinitely many dyadic scales `q = 2^j`, for each of them
infinitely many even radii `R ≥ 18` (room condition included), and for each
such pair arbitrarily small curvature with a separating exterior angle.
NOT proved here. -/
def CofinalTwistSeparation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ TwistSeparation (2^j) R ε

/-- The same with the sign-free interval premise in place of the bare separation. -/
def CofinalSignChange : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ SignChangeControl (2^j) R ε

/-- Main bridge, with the weakest cofinal premise. -/
theorem goalNeg2_of_cofinalTwistSeparation (h : CofinalTwistSeparation) : GoalNeg2 := by
  apply cofinalPencilFailure_implies_goalNeg2
  refine ⟨2, by norm_num, 1, by norm_num, ?_⟩
  intro m₀
  obtain ⟨j, hj, hRs⟩ := h m₀
  refine ⟨j+1, by omega, by omega, ?_⟩
  intro R₀
  obtain ⟨R, hRR, hR, hR18, hsep⟩ := hRs R₀
  refine ⟨R, hRR, ?_⟩
  intro a₀ ha₀
  let q := 2^j
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(j+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let δ : ℝ := min (a₀/(3840*q)) 1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ε, hε0, hεδ, t, hu, hnu⟩ := hsep δ hδ
  let α : ℝ := 160*ε
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ := by
    have he : ε < a₀/(3840*q) := lt_of_lt_of_le hεδ (min_le_left _ _)
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3840*q)).mp he
    dsimp [α]; push_cast; nlinarith
  have heps : |ε| ≤ α/80 := by rw [abs_of_pos hε0]; dsimp [α]; linarith
  have hclass : ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹
      (twistU q R ε t) :=
    ⟨dil_coverage hq hR (by omega), dil_regular hq hR hα heps _⟩
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR
  rw [hpow]
  exact ⟨1, by norm_num, dilLu q R, α, hα, hcap, dil_torus hq R,
    dilTower q R, dil_admissible hq hR, dilLam q R, dil_lambda hq hR,
    twistU q R ε t, hclass, dilBt hq R, hBt1, hBt2, hE, hu, hnu⟩

/-- Restricted to this family the open question is exactly this proposition:
the positive pinned reading refutes it, and it refutes the positive reading. -/
theorem not_cofinalTwistSeparation_of_goalPos1 (h : GoalPos1) : ¬ CofinalTwistSeparation :=
  fun h' => goalNeg2_of_cofinalTwistSeparation h' (goalPos2_iff_goalPos1.mpr h)

theorem cofinalTwistSeparation_of_cofinalSignChange (h : CofinalSignChange) :
    CofinalTwistSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun δ hδ => ?_⟩
  obtain ⟨ε, hε, hεδ, hs⟩ := hc δ hδ
  have hq : 0 < 2^j := by positivity
  exact ⟨ε, hε, hεδ, twistSeparation_of_signChange hq hR (by nlinarith) hs⟩

theorem goalNeg2_of_cofinalSignChange (h : CofinalSignChange) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_cofinalSignChange h)

#print axioms TwistSeparation
#print axioms SignChangeControl
#print axioms twistSeparation_of_signChange
#print axioms signChange_of_kernelPositiveCrossing
#print axioms signChange_of_initialKernelControl
#print axioms goalNeg2_of_twist_separation
#print axioms goalNeg1_of_twist_separation
#print axioms goalNeg2_of_sign_change_control
#print axioms goalPos1_forces_no_twist_separation
#print axioms TwistPencil
#print axioms PencilCertificates
#print axioms signChange_of_pencilCertificates
#print axioms goalNeg2_of_pencil_certificates
#print axioms CofinalTwistSeparation
#print axioms CofinalSignChange
#print axioms goalNeg2_of_cofinalTwistSeparation
#print axioms not_cofinalTwistSeparation_of_goalPos1
#print axioms cofinalTwistSeparation_of_cofinalSignChange
#print axioms goalNeg2_of_cofinalSignChange

end AdalyFormal.Round8.Guarded.SignFree

/-!
Round 9 (analytic route, step 2): perturbation in the curvature.

The round-8 bridge needs, at arbitrarily small curvature `ε > 0`, an exterior angle
with a unit carrier and a non-unit corrected carrier.  This appendix reduces that to
data at ZERO curvature: a crossing `t₀` of the vacuum carrier `twistA q R 0 1`, with
negative angle-slope on its kernel, and a first-order correction coefficient `D₁`
(`twistD ε ≈ ε D₁`) that is definite of EITHER sign on that kernel, plus soft
regularity in `(ε, t)` at `ε = 0`.  The abstract part is a finite-dimensional theorem
proved with Schur complements onto the vacuum kernel: the carrier and the corrected
carrier are units iff their Schur complements are injective on the kernel, the vacuum
Schur complement has slope `P X' P`, and the corrected one differs from the carrier one
by `ε P D₁ P + o(ε)` uniformly near `t₀`.  No positivity of the carrier is assumed.

Nothing here proves a pinned goal.  `VacuumNondegeneracy` and its cofinal form are
explicit, unproved hypotheses about the actual operators.
-/
namespace AdalyFormal.Round9.Guarded.AnalyticR1

open scoped RealInnerProductSpace Topology
open Set Filter
open AdalyFormal.D1Literal (PSD psd_coercive psd_kernel)

section PathLemma
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The frozen `D1IVT.exists_nonunit_path`, with its proof copied verbatim, now also
returning that the non-unit found is PSD (the proof already establishes this: the
point is the supremum of the PSD initial segment). -/
theorem exists_psd_nonunit_path (F : ℝ → (E →L[ℝ] E)) (hc : Continuous F)
    (hs : ∀ t x y, ⟪F t x, y⟫ = ⟪x, F t y⟫) (h0 : PSD (F 0)) (T : ℝ) (hT : 0 < T) (v : E)
    (hv : ⟪v, F T v⟫ < 0) : ∃ t : ℝ, 0 ≤ t ∧ t < T ∧ PSD (F t) ∧ ¬ IsUnit (F t) := by
  set S : Set ℝ := {t | t ∈ Icc (0 : ℝ) T ∧ ∀ s ∈ Icc (0 : ℝ) t, PSD (F s)} with hS
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hT.le⟩, fun s hs' => by
    have : s = 0 := le_antisymm hs'.2 hs'.1
    rw [this]; exact h0⟩
  have hbdd : BddAbove S := ⟨T, fun t ht => ht.1.2⟩
  set ts := sSup S with hts
  have hts0 : 0 ≤ ts := le_csSup hbdd h0S
  have htsT : ts ≤ T := csSup_le ⟨0, h0S⟩ (fun t ht => ht.1.2)
  have hlt : ∀ s, 0 ≤ s → s < ts → PSD (F s) := by
    intro s hs0 hs1
    obtain ⟨t, ht, hst⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩ hs1
    exact ht.2 s ⟨hs0, hst.le⟩
  have hclosed : ∀ w : E, IsClosed {s : ℝ | 0 ≤ ⟪w, F s w⟫} := fun w =>
    isClosed_le continuous_const (by fun_prop)
  have hpsd_ts : PSD (F ts) := by
    intro w
    rcases hts0.lt_or_eq with h | h
    · have hsub : Ico (0 : ℝ) ts ⊆ {s : ℝ | 0 ≤ ⟪w, F s w⟫} := fun s hs' => hlt s hs'.1 hs'.2 w
      have := (hclosed w).closure_subset_iff.mpr hsub
      refine this ?_
      rw [closure_Ico h.ne]
      exact ⟨hts0, le_rfl⟩
    · rw [← h]; exact h0 w
  have hle : ∀ s, 0 ≤ s → s ≤ ts → PSD (F s) := by
    intro s hs0 hs1
    rcases hs1.lt_or_eq with h | h
    · exact hlt s hs0 h
    · rw [h]; exact hpsd_ts
  have htsT' : ts < T := by
    rcases htsT.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hpsd_ts v
      rw [h] at this
      linarith
  refine ⟨ts, hts0, htsT', hpsd_ts, fun hu => ?_⟩
  obtain ⟨m, hm, hmc⟩ := psd_coercive (F ts) (hs ts) hpsd_ts hu
  have hcts : ContinuousAt F ts := hc.continuousAt
  rw [Metric.continuousAt_iff] at hcts
  obtain ⟨δ, hδ, hF⟩ := hcts (m / 2) (by positivity)
  set t' := min (ts + δ / 2) T with ht'
  have ht'T : t' ≤ T := min_le_right _ _
  have ht'ts : ts < t' := lt_min (by linarith) htsT'
  have ht'S : t' ∈ S := by
    refine ⟨⟨by linarith, ht'T⟩, fun s hs' => ?_⟩
    rcases le_or_gt s ts with h | h
    · exact hle s hs'.1 h
    · intro w
      have hd : dist s ts < δ := by
        rw [Real.dist_eq, abs_lt]
        have : s ≤ ts + δ / 2 := le_trans hs'.2 (min_le_left _ _)
        constructor <;> linarith
      have hn := hF hd
      rw [dist_eq_norm] at hn
      have h1 : ⟪w, F s w⟫ = ⟪w, F ts w⟫ + ⟪w, (F s - F ts) w⟫ := by
        simp only [sub_apply, inner_sub_right]; ring
      have h2 : |⟪w, (F s - F ts) w⟫| ≤ ‖w‖ * (‖F s - F ts‖ * ‖w‖) := by
        calc |⟪w, (F s - F ts) w⟫| ≤ ‖w‖ * ‖(F s - F ts) w‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖w‖ * (‖F s - F ts‖ * ‖w‖) := by gcongr; exact (F s - F ts).le_opNorm w
      have h3 := hmc w
      have h4 : ‖w‖ * (‖F s - F ts‖ * ‖w‖) ≤ (m / 2) * ‖w‖ ^ 2 := by
        have : ‖F s - F ts‖ ≤ m / 2 := hn.le
        calc ‖w‖ * (‖F s - F ts‖ * ‖w‖) = ‖F s - F ts‖ * ‖w‖ ^ 2 := by ring
          _ ≤ (m / 2) * ‖w‖ ^ 2 := by gcongr
      have h5 := (abs_le.mp h2).1
      nlinarith [sq_nonneg ‖w‖]
  have := le_csSup hbdd ht'S
  linarith

/-- Strict positivity of a quadratic form on the range of an idempotent is uniform. -/
theorem exists_coercive_on_range (P M : E →L[ℝ] E)
    (h : ∀ x, P x = x → x ≠ 0 → 0 < ⟪x, M x⟫) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, P x = x → c * ‖x‖ ^ 2 ≤ ⟪x, M x⟫ := by
  set S1 : Set E := {x | P x = x} ∩ Metric.sphere (0 : E) 1 with hS1
  have hcpt : IsCompact S1 :=
    (isCompact_sphere (0 : E) 1).inter_left (isClosed_eq P.continuous continuous_id)
  have hcont : Continuous (fun v : E => ⟪v, M v⟫) := by fun_prop
  have hscale : ∀ x : E, x ≠ 0 → P x = x → (‖x‖⁻¹ • x) ∈ S1 ∧
      ⟪x, M x⟫ = ‖x‖ ^ 2 * ⟪‖x‖⁻¹ • x, M (‖x‖⁻¹ • x)⟫ := by
    intro x hx hPx
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hxn' : ‖x‖ ≠ 0 := hxn.ne'
    refine ⟨⟨by simp [map_smul, hPx], ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn']
    · simp only [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
      field_simp
      try ring
  rcases S1.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun x hPx => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    · exfalso
      have := (hscale x hx hPx).1
      rw [he] at this
      exact this
  · obtain ⟨x0, hx0, hmin⟩ := hcpt.exists_isMinOn hne hcont.continuousOn
    have hx0n : x0 ≠ 0 := by
      intro h0
      have := hx0.2
      rw [h0] at this
      simp at this
    refine ⟨⟪x0, M x0⟫, h x0 hx0.1 hx0n, fun x hPx => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    · obtain ⟨hmem, heq⟩ := hscale x hx hPx
      have hm : ⟪x0, M x0⟫ ≤ ⟪‖x‖⁻¹ • x, M (‖x‖⁻¹ • x)⟫ := hmin hmem
      rw [heq]
      nlinarith [sq_nonneg ‖x‖]

end PathLemma

section Schur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The complementary block `(1-P) Z (1-P)`, padded by `P` so that it is a unit of
the full operator ring exactly when the block is invertible on `ker P`. -/
noncomputable def schurC (P Z : E →L[ℝ] E) : E →L[ℝ] E := (1 - P) * Z * (1 - P) + P

/-- The Schur complement of `Z` onto the range of the idempotent `P`. -/
noncomputable def schurS (P Z : E →L[ℝ] E) : E →L[ℝ] E :=
  P * Z * P - P * Z * (1 - P) * Ring.inverse (schurC P Z) * ((1 - P) * Z * P)

omit [FiniteDimensional ℝ E] in
theorem inverse_symm (C : E →L[ℝ] E) (hC : ∀ x y, ⟪C x, y⟫ = ⟪x, C y⟫) (x y : E) :
    ⟪Ring.inverse C x, y⟫ = ⟪x, Ring.inverse C y⟫ := by
  by_cases hu : IsUnit C
  · have h1 : ∀ v, C (Ring.inverse C v) = v := fun v => by
      rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel C hu, one_apply_eq_self]
    calc ⟪Ring.inverse C x, y⟫ = ⟪Ring.inverse C x, C (Ring.inverse C y)⟫ := by rw [h1]
      _ = ⟪C (Ring.inverse C x), Ring.inverse C y⟫ := (hC _ _).symm
      _ = ⟪x, Ring.inverse C y⟫ := by rw [h1]
  · rw [Ring.inverse_non_unit C hu]
    simp

omit [FiniteDimensional ℝ E] in
theorem schurS_symm (P Z : E →L[ℝ] E) (hPs : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (hZs : ∀ x y, ⟪Z x, y⟫ = ⟪x, Z y⟫) (x y : E) :
    ⟪schurS P Z x, y⟫ = ⟪x, schurS P Z y⟫ := by
  set Q : E →L[ℝ] E := 1 - P with hQ
  have hQs : ∀ x y, ⟪Q x, y⟫ = ⟪x, Q y⟫ := by
    intro x y
    simp only [hQ, sub_apply, one_apply_eq_self, inner_sub_left, inner_sub_right, hPs]
  have hCs : ∀ x y, ⟪schurC P Z x, y⟫ = ⟪x, schurC P Z y⟫ := by
    intro x y
    simp only [schurC, ← hQ, add_apply, mul_apply_eq_comp, inner_add_left, inner_add_right]
    rw [hQs, hZs, hQs, hPs]
  have hCis := inverse_symm (schurC P Z) hCs
  simp only [schurS, ← hQ]
  rw [sub_apply, sub_apply, inner_sub_left, inner_sub_right]
  simp only [mul_apply_eq_comp]
  congr 1
  · rw [hPs, hZs, hPs]
  · rw [hPs, hZs, hQs, hCis, hQs, hZs, hPs]

omit [FiniteDimensional ℝ E] in
theorem schurS_left (P Z : E →L[ℝ] E) (hP : P * P = P) (v : E) :
    P (schurS P Z v) = schurS P Z v := by
  have hPv : ∀ u, P (P u) = P u := fun u => by rw [← mul_apply_eq_comp, hP]
  simp only [schurS, sub_apply, mul_apply_eq_comp, map_sub, hPv]

omit [FiniteDimensional ℝ E] in
theorem schurS_right (P Z : E →L[ℝ] E) (hP : P * P = P) (v : E) :
    schurS P Z (P v) = schurS P Z v := by
  have hPv : ∀ u, P (P u) = P u := fun u => by rw [← mul_apply_eq_comp, hP]
  simp only [schurS, sub_apply, mul_apply_eq_comp, hPv]

/-- Schur reduction: if the complementary block is invertible, `Z` is a unit iff its
Schur complement is injective on the range of `P`. -/
theorem schur_unit_iff {P Z : E →L[ℝ] E} (hP : P * P = P) (hC : IsUnit (schurC P Z)) :
    IsUnit Z ↔ ∀ x, P x = x → schurS P Z x = 0 → x = 0 := by
  set C := schurC P Z with hCdef
  set Ci := Ring.inverse C with hCi
  have hPv : ∀ u, P (P u) = P u := fun u => by rw [← mul_apply_eq_comp, hP]
  have hCv : ∀ u, C u = (Z (u - P u) - P (Z (u - P u))) + P u := by
    intro u
    simp only [hCdef, schurC, add_apply, mul_apply_eq_comp, sub_apply, one_apply_eq_self]
  have hCCi : ∀ u, C (Ci u) = u := fun u => by
    rw [← mul_apply_eq_comp, hCi, Ring.mul_inverse_cancel C hC, one_apply_eq_self]
  have hCiC : ∀ u, Ci (C u) = u := fun u => by
    rw [← mul_apply_eq_comp, hCi, Ring.inverse_mul_cancel C hC, one_apply_eq_self]
  have hPC : ∀ u, P (C u) = P u := by
    intro u; rw [hCv]; simp [map_add, map_sub, hPv]
  have hPCi : ∀ u, P (Ci u) = P u := by
    intro u
    have := hPC (Ci u)
    rw [hCCi] at this
    exact this.symm
  have hkey : ∀ u, Z (Ci u - P u) - P (Z (Ci u - P u)) = u - P u := by
    intro u
    have h := hCCi u
    rw [hCv, hPCi] at h
    exact eq_sub_of_add_eq h
  have hSv : ∀ x, schurS P Z x =
      P (Z (P x)) - P (Z (Ci (Z (P x) - P (Z (P x))) - P (Ci (Z (P x) - P (Z (P x)))))) := by
    intro x
    simp only [schurS, ← hCdef, ← hCi, sub_apply, mul_apply_eq_comp, one_apply_eq_self]
  constructor
  · intro hu x hPx hS
    have hinj : Function.Injective Z := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
    have hPr : P (Z x - P (Z x)) = 0 := by rw [map_sub, hPv, sub_self]
    have hPCir : P (Ci (Z x - P (Z x))) = 0 := by rw [hPCi, hPr]
    have hS' : P (Z x) - P (Z (Ci (Z x - P (Z x)))) = 0 := by
      have := hS
      rw [hSv, hPx, hPCir, sub_zero] at this
      exact this
    have hk := hkey (Z x - P (Z x))
    simp only [hPr, sub_zero] at hk
    have h2 : P (Z (Ci (Z x - P (Z x)))) = P (Z x) := (sub_eq_zero.mp hS').symm
    have hZy : Z (x - Ci (Z x - P (Z x))) = 0 := by
      rw [map_sub]
      have e : Z (Ci (Z x - P (Z x))) = Z x - P (Z x) + P (Z (Ci (Z x - P (Z x)))) :=
        eq_add_of_sub_eq hk
      rw [e, h2]; abel
    have hy0 : x - Ci (Z x - P (Z x)) = 0 := hinj (by rw [hZy, map_zero])
    have : P (x - Ci (Z x - P (Z x))) = x := by rw [map_sub, hPCir, hPx, sub_zero]
    rw [← this, hy0, map_zero]
  · intro h
    have hinj : Function.Injective Z := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      have hPm : P (y - P y) = 0 := by rw [map_sub, hPv, sub_self]
      have hsplit : P y + (y - P y) = y := by abel
      have hZy : Z (P y) + Z (y - P y) = 0 := by rw [← map_add, hsplit, hy]
      have hCm : C (y - P y) = -(Z (P y) - P (Z (P y))) := by
        rw [hCv, hPm, sub_zero, add_zero]
        have e : Z (y - P y) = -Z (P y) := eq_neg_of_add_eq_zero_right hZy
        rw [e, map_neg]; abel
      have hneg : Ci (-(Z (P y) - P (Z (P y)))) = -(Ci (Z (P y) - P (Z (P y)))) := map_neg Ci _
      have hm' : y - P y = -(Ci (Z (P y) - P (Z (P y)))) := by
        rw [← hneg, ← hCm, hCiC]
      have hPCr : P (Ci (Z (P y) - P (Z (P y)))) = 0 := by
        rw [hPCi, map_sub, hPv, sub_self]
      have hS0 : schurS P Z (P y) = 0 := by
        rw [hSv, hPv, hPCr, sub_zero]
        have e : Ci (Z (P y) - P (Z (P y))) = -(y - P y) := by rw [hm', neg_neg]
        rw [e, map_neg, map_neg, sub_neg_eq_add, ← map_add, hZy, map_zero]
      have hPy : P y = 0 := h (P y) (hPv y) hS0
      have hm0 : y - P y = 0 := by
        rw [hm']
        simp only [hPy, map_zero, sub_zero, neg_zero]
      rw [hPy, sub_zero] at hm0
      exact hm0
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hinj, (LinearMap.injective_iff_surjective (f := (Z : E →ₗ[ℝ] E))).mp hinj⟩

end Schur

section Perturbation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem tendsto_inverse_of_unit {α : Type*} {l : Filter α} {f : α → E →L[ℝ] E} {C : E →L[ℝ] E}
    (hC : IsUnit C) (hf : Tendsto f l (𝓝 C)) :
    Tendsto (fun a => Ring.inverse (f a)) l (𝓝 (Ring.inverse C)) := by
  have h := NormedRing.inverse_continuousAt hC.unit
  rw [hC.unit_spec] at h
  exact h.tendsto.comp hf

omit [FiniteDimensional ℝ E] in
theorem schurC_continuous (P : E →L[ℝ] E) : Continuous (schurC P) := by
  unfold schurC
  exact ((continuous_const.mul continuous_id).mul continuous_const).add continuous_const

theorem tendsto_schurS {α : Type*} {l : Filter α} (P : E →L[ℝ] E) {f : α → E →L[ℝ] E}
    {Z : E →L[ℝ] E} (hC : IsUnit (schurC P Z)) (hf : Tendsto f l (𝓝 Z)) :
    Tendsto (fun a => schurS P (f a)) l (𝓝 (schurS P Z)) := by
  have hCi := tendsto_inverse_of_unit hC (((schurC_continuous P).tendsto Z).comp hf)
  unfold schurS
  exact ((tendsto_const_nhds.mul hf).mul tendsto_const_nhds).sub
    ((((tendsto_const_nhds.mul hf).mul tendsto_const_nhds).mul hCi).mul
      ((tendsto_const_nhds.mul hf).mul tendsto_const_nhds))

omit [FiniteDimensional ℝ E] in
theorem quad_le_norm (A : E →L[ℝ] E) (x : E) : |⟪x, A x⟫| ≤ ‖A‖ * ‖x‖ ^ 2 := by
  calc |⟪x, A x⟫| ≤ ‖x‖ * ‖A x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := by gcongr; exact A.le_opNorm x
    _ = ‖A‖ * ‖x‖ ^ 2 := by ring

/-- First-order behaviour of the Schur complement at a kernel crossing. -/
theorem vacuum_schur_slope (P X' : E →L[ℝ] E) (Xv : ℝ → E →L[ℝ] E) (t₀ : ℝ)
    (hder : HasDerivAt Xv X' t₀)
    (hXP : Xv t₀ * P = 0) (hPX : P * Xv t₀ = 0) (hC0 : IsUnit (schurC P (Xv t₀))) :
    Tendsto (fun t => (t - t₀)⁻¹ • schurS P (Xv t)) (𝓝[≠] t₀) (𝓝 (P * X' * P)) := by
  have hslope : Tendsto (fun t => (t - t₀)⁻¹ • (Xv t - Xv t₀)) (𝓝[≠] t₀) (𝓝 X') := by
    have h := hasDerivAt_iff_tendsto_slope.mp hder
    have he : slope Xv t₀ = fun t => (t - t₀)⁻¹ • (Xv t - Xv t₀) := by
      funext t; exact slope_def_module Xv t₀ t
    rwa [he] at h
  have hcont : Tendsto Xv (𝓝[≠] t₀) (𝓝 (Xv t₀)) :=
    hder.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hh : Tendsto (fun t => Xv t - Xv t₀) (𝓝[≠] t₀) (𝓝 0) := by
    have := hcont.sub_const (Xv t₀)
    rwa [sub_self] at this
  have hCi := tendsto_inverse_of_unit hC0 (((schurC_continuous P).tendsto _).comp hcont)
  have hid : ∀ t, (t - t₀)⁻¹ • schurS P (Xv t) =
      P * ((t - t₀)⁻¹ • (Xv t - Xv t₀)) * P - P * ((t - t₀)⁻¹ • (Xv t - Xv t₀)) * (1 - P) *
        Ring.inverse (schurC P (Xv t)) * ((1 - P) * (Xv t - Xv t₀) * P) := by
    intro t
    have e1 : P * Xv t * P = P * (Xv t - Xv t₀) * P := by
      rw [mul_sub P (Xv t) (Xv t₀), sub_mul (P * Xv t) (P * Xv t₀) P, hPX, zero_mul, sub_zero]
    have e2 : P * Xv t * (1 - P) = P * (Xv t - Xv t₀) * (1 - P) := by
      rw [mul_sub P (Xv t) (Xv t₀), hPX, sub_zero]
    have e3 : (1 - P) * Xv t * P = (1 - P) * (Xv t - Xv t₀) * P := by
      rw [mul_sub (1 - P) (Xv t) (Xv t₀), sub_mul ((1 - P) * Xv t) ((1 - P) * Xv t₀) P,
        mul_assoc (1 - P) (Xv t₀) P, hXP, mul_zero, sub_zero]
    unfold schurS
    rw [e1, e2, e3, smul_sub (t - t₀)⁻¹ (P * (Xv t - Xv t₀) * P)]
    simp only [mul_smul_comm, smul_mul_assoc]
  simp_rw [hid]
  have hlim := ((tendsto_const_nhds (x := P)).mul hslope |>.mul (tendsto_const_nhds (x := P))).sub
    (((((tendsto_const_nhds (x := P)).mul hslope).mul (tendsto_const_nhds (x := 1 - P))).mul hCi).mul
      (((tendsto_const_nhds (x := 1 - P)).mul hh).mul (tendsto_const_nhds (x := P))))
  have hval : P * X' * P - P * X' * (1 - P) * Ring.inverse (schurC P (Xv t₀)) *
      ((1 - P) * 0 * P) = P * X' * P := by simp
  rwa [hval] at hlim

omit [FiniteDimensional ℝ E] in
/-- The exact algebra of the corrected Schur complement. -/
theorem schur_difference_identity (P X D : E →L[ℝ] E) (c : ℝ)
    (hX : IsUnit (schurC P X)) (hY : IsUnit (schurC P (X - D))) :
    c • (schurS P X - schurS P (X - D)) =
      P * (c • D) * P
      + (P * X * (1 - P)) * Ring.inverse (schurC P (X - D)) * ((1 - P) * (c • D) * (1 - P)) *
          Ring.inverse (schurC P X) * ((1 - P) * X * P)
      - (P * X * (1 - P)) * Ring.inverse (schurC P (X - D)) * ((1 - P) * (c • D) * P)
      - (P * (c • D) * (1 - P)) * Ring.inverse (schurC P (X - D)) * ((1 - P) * X * P)
      + (P * D * (1 - P)) * Ring.inverse (schurC P (X - D)) * ((1 - P) * (c • D) * P) := by
  have hres : Ring.inverse (schurC P (X - D)) - Ring.inverse (schurC P X) =
      Ring.inverse (schurC P (X - D)) * ((1 - P) * D * (1 - P)) * Ring.inverse (schurC P X) := by
    have hd : schurC P X - schurC P (X - D) = (1 - P) * D * (1 - P) := by
      unfold schurC; noncomm_ring
    have e1 : Ring.inverse (schurC P (X - D)) * schurC P X * Ring.inverse (schurC P X) =
        Ring.inverse (schurC P (X - D)) := by
      rw [mul_assoc, Ring.mul_inverse_cancel _ hX, mul_one]
    have e2 : Ring.inverse (schurC P (X - D)) * schurC P (X - D) * Ring.inverse (schurC P X) =
        Ring.inverse (schurC P X) := by
      rw [Ring.inverse_mul_cancel _ hY, one_mul]
    rw [← hd, mul_sub, sub_mul, e1, e2]
  have key : schurS P X - schurS P (X - D) = P * D * P
      + (P * X * (1 - P)) * (Ring.inverse (schurC P (X - D)) - Ring.inverse (schurC P X)) *
          ((1 - P) * X * P)
      - (P * X * (1 - P)) * Ring.inverse (schurC P (X - D)) * ((1 - P) * D * P)
      - (P * D * (1 - P)) * Ring.inverse (schurC P (X - D)) * ((1 - P) * X * P)
      + (P * D * (1 - P)) * Ring.inverse (schurC P (X - D)) * ((1 - P) * D * P) := by
    unfold schurS
    generalize Ring.inverse (schurC P (X - D)) = CiY
    generalize Ring.inverse (schurC P X) = CiX
    noncomm_ring
  rw [key, hres]
  simp only [smul_add, smul_sub, mul_smul_comm, smul_mul_assoc, mul_assoc]
  try abel

/-- The corrected Schur complement differs from the carrier one by `ε P D₁ P + o(ε)`. -/
theorem schur_difference_tendsto {α : Type*} {l : Filter α} (P : E →L[ℝ] E)
    {Xf Df : α → E →L[ℝ] E} {c : α → ℝ} {X0 D1 : E →L[ℝ] E}
    (hXP : X0 * P = 0) (hPX : P * X0 = 0) (hC0 : IsUnit (schurC P X0))
    (hX : Tendsto Xf l (𝓝 X0)) (hD : Tendsto Df l (𝓝 0))
    (hcD : Tendsto (fun a => c a • Df a) l (𝓝 D1)) :
    Tendsto (fun a => c a • (schurS P (Xf a) - schurS P (Xf a - Df a)) - P * D1 * P) l (𝓝 0) := by
  have hY : Tendsto (fun a => Xf a - Df a) l (𝓝 X0) := by
    have := hX.sub hD
    rwa [sub_zero] at this
  have hCX := tendsto_inverse_of_unit hC0 (((schurC_continuous P).tendsto X0).comp hX)
  have hCY := tendsto_inverse_of_unit hC0 (((schurC_continuous P).tendsto X0).comp hY)
  have hunitX : ∀ᶠ a in l, IsUnit (schurC P (Xf a)) :=
    (((schurC_continuous P).tendsto X0).comp hX).eventually (Units.isOpen.mem_nhds hC0)
  have hunitY : ∀ᶠ a in l, IsUnit (schurC P (Xf a - Df a)) :=
    (((schurC_continuous P).tendsto X0).comp hY).eventually (Units.isOpen.mem_nhds hC0)
  have hid : ∀ᶠ a in l,
      (P * (c a • Df a) * P - P * D1 * P)
      + (P * Xf a * (1 - P)) * Ring.inverse (schurC P (Xf a - Df a)) *
          ((1 - P) * (c a • Df a) * (1 - P)) * Ring.inverse (schurC P (Xf a)) * ((1 - P) * Xf a * P)
      - (P * Xf a * (1 - P)) * Ring.inverse (schurC P (Xf a - Df a)) * ((1 - P) * (c a • Df a) * P)
      - (P * (c a • Df a) * (1 - P)) * Ring.inverse (schurC P (Xf a - Df a)) * ((1 - P) * Xf a * P)
      + (P * Df a * (1 - P)) * Ring.inverse (schurC P (Xf a - Df a)) * ((1 - P) * (c a • Df a) * P)
      = c a • (schurS P (Xf a) - schurS P (Xf a - Df a)) - P * D1 * P := by
    filter_upwards [hunitX, hunitY] with a hxu hyu
    rw [schur_difference_identity P (Xf a) (Df a) (c a) hxu hyu]
    abel
  refine Tendsto.congr' hid ?_
  have hb : Tendsto (fun a => P * Xf a * (1 - P)) l (𝓝 0) := by
    have := ((tendsto_const_nhds (x := P)).mul hX).mul (tendsto_const_nhds (x := 1 - P))
    rwa [hPX, zero_mul] at this
  have hb' : Tendsto (fun a => (1 - P) * Xf a * P) l (𝓝 0) := by
    have := ((tendsto_const_nhds (x := 1 - P)).mul hX).mul (tendsto_const_nhds (x := P))
    rwa [mul_assoc (1 - P) X0 P, hXP, mul_zero] at this
  have t0 : Tendsto (fun a => P * (c a • Df a) * P - P * D1 * P) l (𝓝 0) := by
    have := (((tendsto_const_nhds (x := P)).mul hcD).mul (tendsto_const_nhds (x := P))).sub_const
      (P * D1 * P)
    rwa [sub_self] at this
  have t1 := (((hb.mul hCY).mul (((tendsto_const_nhds (x := 1 - P)).mul hcD).mul
    (tendsto_const_nhds (x := 1 - P)))).mul hCX).mul hb'
  have t2 := (hb.mul hCY).mul (((tendsto_const_nhds (x := 1 - P)).mul hcD).mul
    (tendsto_const_nhds (x := P)))
  have t3 := ((((tendsto_const_nhds (x := P)).mul hcD).mul (tendsto_const_nhds (x := 1 - P))).mul
    hCY).mul hb'
  have t4 := ((((tendsto_const_nhds (x := P)).mul hD).mul (tendsto_const_nhds (x := 1 - P))).mul
    hCY).mul (((tendsto_const_nhds (x := 1 - P)).mul hcD).mul (tendsto_const_nhds (x := P)))
  have := (((t0.add t1).sub t2).sub t3).add t4
  simpa using this

end Perturbation

section Main
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Separation along a path from a positivity gap: the core sign-change step on the
range of `P`.  `B` is the corrected Schur complement, `A` the carrier one. -/
theorem core_separation (P : E →L[ℝ] E) (hP : P * P = P) (hPs : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (A B : ℝ → E →L[ℝ] E) (T : ℝ) (hT : 0 < T)
    (hBc : ContinuousOn B (Icc 0 T))
    (hBs : ∀ s x y, ⟪B s x, y⟫ = ⟪x, B s y⟫)
    (hBl : ∀ s v, P (B s v) = B s v) (hBr : ∀ s v, B s (P v) = B s v)
    (hB0 : ∀ x, P x = x → 0 ≤ ⟪x, B 0 x⟫)
    (w : E) (hw : P w = w) (hBT : ⟪w, B T w⟫ < 0)
    (hAB : ∀ s ∈ Icc 0 T, ∀ x, P x = x → x ≠ 0 → ⟪x, B s x⟫ < ⟪x, A s x⟫) :
    ∃ s, 0 ≤ s ∧ s < T ∧ (∀ x, P x = x → A s x = 0 → x = 0) ∧
      ∃ x, P x = x ∧ x ≠ 0 ∧ B s x = 0 := by
  have hPv : ∀ u, P (P u) = P u := fun u => by rw [← mul_apply_eq_comp, hP]
  set pr : ℝ → ℝ := fun s => (projIcc 0 T hT.le s : ℝ) with hpr
  have hprc : Continuous pr := continuous_subtype_val.comp continuous_projIcc
  have hprmem : ∀ s, pr s ∈ Icc 0 T := fun s => (projIcc 0 T hT.le s).2
  have hprid : ∀ s ∈ Icc 0 T, pr s = s := fun s hs => by
    simp only [hpr, projIcc_of_mem hT.le hs]
  set G : ℝ → E →L[ℝ] E := fun s => B (pr s) + (1 - P) with hG
  have hGc : Continuous G := (hBc.comp_continuous hprc hprmem).add continuous_const
  have hQq : ∀ v, ⟪v, (1 - P) v⟫ = ‖v - P v‖ ^ 2 := by
    intro v
    rw [sub_apply, one_apply_eq_self, ← real_inner_self_eq_norm_sq]
    have h0 : ⟪P v, v - P v⟫ = 0 := by
      rw [hPs, map_sub, hPv, sub_self, inner_zero_right]
    calc ⟪v, v - P v⟫ = ⟪(v - P v) + P v, v - P v⟫ := by rw [sub_add_cancel]
      _ = ⟪v - P v, v - P v⟫ := by rw [inner_add_left, h0, add_zero]
  have hBq : ∀ s v, ⟪v, B s v⟫ = ⟪P v, B s (P v)⟫ := by
    intro s v
    rw [hBr, hPs, hBl]
  have hGs : ∀ s x y, ⟪G s x, y⟫ = ⟪x, G s y⟫ := by
    intro s x y
    simp only [hG, add_apply, sub_apply, one_apply_eq_self, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, hBs, hPs]
  have hG0 : PSD (G 0) := by
    intro v
    simp only [hG, add_apply, inner_add_right]
    rw [hprid 0 ⟨le_rfl, hT.le⟩, hQq, hBq]
    have h1 := hB0 (P v) (hPv v)
    have h2 := sq_nonneg ‖v - P v‖
    linarith
  have hGT : ⟪w, G T w⟫ < 0 := by
    simp only [hG, add_apply, inner_add_right]
    rw [hprid T ⟨hT.le, le_rfl⟩, hQq, hw, sub_self, norm_zero]
    simpa using hBT
  obtain ⟨s, hs0, hsT, hpsd, hnu⟩ := exists_psd_nonunit_path G hGc hGs hG0 T hT w hGT
  have hsI : s ∈ Icc 0 T := ⟨hs0, hsT.le⟩
  have hGs' : G s = B s + (1 - P) := by simp only [hG, hprid s hsI]
  -- a kernel vector of `G s`
  have hker : ∃ y, y ≠ 0 ∧ G s y = 0 := by
    by_contra hcon
    apply hnu
    have hinj : Function.Injective (G s) := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      by_contra hy0
      exact hcon ⟨y, hy0, hy⟩
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hinj, (LinearMap.injective_iff_surjective (f := ((G s) : E →ₗ[ℝ] E))).mp hinj⟩
  obtain ⟨y, hy0, hGy⟩ := hker
  rw [hGs', add_apply, sub_apply, one_apply_eq_self] at hGy
  have hBy : B s y = 0 := by
    have := congrArg P hGy
    rw [map_add, map_sub, hBl, hPv, sub_self, add_zero, map_zero] at this
    exact this
  have hPy : P y = y := by
    rw [hBy, zero_add, sub_eq_zero] at hGy
    exact hGy.symm
  refine ⟨s, hs0, hsT, fun x hx hAx => ?_, y, hPy, hy0, hBy⟩
  by_contra hx0
  have h1 := hAB s hsI x hx hx0
  rw [hAx, inner_zero_right] at h1
  have h2 := hpsd x
  rw [hGs', add_apply, inner_add_right, hQq, hx, sub_self, norm_zero] at h2
  have : (0 : ℝ) ^ 2 = 0 := by norm_num
  linarith

end Main

section MainTheorem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Perturbative separation, positive sign.  At zero curvature the carrier `X 0 ·`
has a crossing at `t₀` whose kernel is the range of the symmetric idempotent `P`,
with negative slope there; the correction is `ε D₁ + o(ε)` with `D₁` positive on
the kernel.  Then every small `ε > 0` has an angle where `X ε t` is a unit and
`X ε t - D ε` is not.  No positivity of the carrier is assumed (other directions
may have crossed earlier), and no symmetry of the kernel. -/
theorem separation_of_vacuum_data_pos
    (X : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E) (P : E →L[ℝ] E)
    (hP : P * P = P) (hPs : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (hXs : ∀ ε t x y, ⟪X ε t x, y⟫ = ⟪x, X ε t y⟫)
    (hDs : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (hXc : ∀ ε, Continuous (X ε))
    (t₀ η₀ : ℝ) (hη₀ : 0 < η₀)
    (hjoint : ∀ t, |t - t₀| < η₀ → ContinuousAt (fun p : ℝ × ℝ => X p.1 p.2) (0, t))
    (X' : E →L[ℝ] E) (hder : HasDerivAt (X 0) X' t₀)
    (D₁ : E →L[ℝ] E) (hD : Tendsto (fun ε : ℝ => ε⁻¹ • D ε) (𝓝[>] 0) (𝓝 D₁))
    (hXP : X 0 t₀ * P = 0) (hker : ∀ x, X 0 t₀ x = 0 → P x = x)
    (w : E) (hwP : P w = w) (hw0 : w ≠ 0)
    (hslope : ∀ v, P v = v → v ≠ 0 → ⟪v, X' v⟫ < 0)
    (hpos : ∀ v, P v = v → v ≠ 0 → 0 < ⟪v, D₁ v⟫) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ t : ℝ, IsUnit (X ε t) ∧ ¬ IsUnit (X ε t - D ε) := by
  have hPv : ∀ u, P (P u) = P u := fun u => by rw [← mul_apply_eq_comp, hP]
  -- `P X₀ = 0` by symmetry
  have hPX : P * X 0 t₀ = 0 := by
    ext x
    rw [mul_apply_eq_comp, zero_apply]
    apply ext_inner_right ℝ
    intro y
    rw [hPs, hXs, ← mul_apply_eq_comp (X 0 t₀) P y, hXP, zero_apply, inner_zero_right,
      inner_zero_left]
  -- the complementary block is invertible at the crossing
  have hC0 : IsUnit (schurC P (X 0 t₀)) := by
    have hinj : Function.Injective (schurC P (X 0 t₀)) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have hCv : schurC P (X 0 t₀) x = (X 0 t₀ (x - P x) - P (X 0 t₀ (x - P x))) + P x := by
        simp only [schurC, add_apply, mul_apply_eq_comp, sub_apply, one_apply_eq_self]
      have hPX0 : ∀ u, P (X 0 t₀ u) = 0 := fun u => by
        rw [← mul_apply_eq_comp, hPX, zero_apply]
      have hPx : P x = 0 := by
        have := congrArg P hx
        rw [hCv, map_add, map_sub, hPv, sub_self, zero_add, hPv, map_zero] at this
        exact this
      rw [hCv, hPx, sub_zero, add_zero, hPX0, sub_zero] at hx
      have := hker x hx
      rw [hPx] at this
      exact this.symm
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj,
      (LinearMap.injective_iff_surjective (f := ((schurC P (X 0 t₀)) : E →ₗ[ℝ] E))).mp hinj⟩
  -- uniform constants on the kernel
  obtain ⟨ν, hν, hνc⟩ := exists_coercive_on_range P D₁ hpos
  obtain ⟨σ₀, hσ₀, hσc⟩ := exists_coercive_on_range P (-X') (fun v hv hv0 => by
    rw [neg_apply, inner_neg_right]; linarith [hslope v hv hv0])
  -- (1) the vacuum Schur complement has slope `P X' P`
  have hvac := vacuum_schur_slope P X' (X 0) t₀ hder hXP hPX hC0
  have hΨ : ∀ᶠ t in 𝓝[≠] t₀, ‖(t - t₀)⁻¹ • schurS P (X 0 t) - P * X' * P‖ < σ₀ / 2 :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hvac).eventually (gt_mem_nhds (by positivity))
  obtain ⟨η₂, hη₂, hη₂'⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hΨ)
  -- (2) vacuum units near the crossing
  have hCvac : ∀ᶠ t in 𝓝 t₀, IsUnit (schurC P (X 0 t)) :=
    (((schurC_continuous P).tendsto _).comp hder.continuousAt.tendsto).eventually
      (Units.isOpen.mem_nhds hC0)
  obtain ⟨η₃, hη₃, hη₃'⟩ := Metric.eventually_nhds_iff.mp hCvac
  -- (3) off the vacuum: units and the first-order corrected difference
  have hXF : Tendsto (fun p : ℝ × ℝ => X p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t₀) (𝓝 (X 0 t₀)) := by
    have h := (hjoint t₀ (by simpa using hη₀)).tendsto
    refine h.mono_left ?_
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
  have hD0 : Tendsto D (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => ε • (ε⁻¹ • D ε)) (𝓝[>] 0) (𝓝 ((0 : ℝ) • D₁)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul hD
    rw [zero_smul] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    rw [smul_smul, mul_inv_cancel₀ hε'.ne', one_smul]
  have hDF : Tendsto (fun p : ℝ × ℝ => D p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t₀) (𝓝 0) :=
    hD0.comp tendsto_fst
  have hcDF : Tendsto (fun p : ℝ × ℝ => p.1⁻¹ • D p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t₀) (𝓝 D₁) :=
    hD.comp tendsto_fst
  have hYF : Tendsto (fun p : ℝ × ℝ => X p.1 p.2 - D p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t₀)
      (𝓝 (X 0 t₀)) := by
    have := hXF.sub hDF
    rwa [sub_zero] at this
  have hdiff := schur_difference_tendsto P hXP hPX hC0 hXF hDF hcDF
  have hev : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 t₀,
      IsUnit (schurC P (X p.1 p.2)) ∧ IsUnit (schurC P (X p.1 p.2 - D p.1)) ∧
      ‖p.1⁻¹ • (schurS P (X p.1 p.2) - schurS P (X p.1 p.2 - D p.1)) - P * D₁ * P‖ < ν / 2 := by
    refine ((((schurC_continuous P).tendsto _).comp hXF).eventually
      (Units.isOpen.mem_nhds hC0)).and
      (((((schurC_continuous P).tendsto _).comp hYF).eventually
        (Units.isOpen.mem_nhds hC0)).and ?_)
    exact (tendsto_iff_norm_sub_tendsto_zero.mp hdiff).eventually
      (gt_mem_nhds (show (0 : ℝ) < ν / 2 by positivity)) |>.mono (fun p hp => by simpa using hp)
  obtain ⟨pa, hpa, pb, hpb, hpab⟩ := Filter.eventually_prod_iff.mp hev
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hpa)
  obtain ⟨η₁, hη₁, hη₁'⟩ := Metric.eventually_nhds_iff.mp hpb
  have hoff : ∀ ε t, 0 < ε → ε < δ₁ → |t - t₀| < η₁ →
      IsUnit (schurC P (X ε t)) ∧ IsUnit (schurC P (X ε t - D ε)) ∧
      ‖ε⁻¹ • (schurS P (X ε t) - schurS P (X ε t - D ε)) - P * D₁ * P‖ < ν / 2 := by
    intro ε t hε hεδ ht
    have h1 : pa ε := hδ₁' (by rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact hεδ) hε
    have h2 : pb t := hη₁' (by rw [Real.dist_eq]; exact ht)
    exact hpab h1 h2
  -- (4) fix the half-width `η`
  set η : ℝ := min (min η₀ η₁) (min η₂ η₃) / 2 with hη
  have hηpos : 0 < η := by positivity
  have hη0 : η < η₀ := by
    have := min_le_left (min η₀ η₁) (min η₂ η₃); have := min_le_left η₀ η₁; linarith
  have hη1 : η < η₁ := by
    have := min_le_left (min η₀ η₁) (min η₂ η₃); have := min_le_right η₀ η₁; linarith
  have hη2 : η < η₂ := by
    have := min_le_right (min η₀ η₁) (min η₂ η₃); have := min_le_left η₂ η₃; linarith
  have hη3 : η < η₃ := by
    have := min_le_right (min η₀ η₁) (min η₂ η₃); have := min_le_right η₂ η₃; linarith
  -- (5) the vacuum Schur form at `t₀ ∓ η`
  have hvacform : ∀ τ : ℝ, τ ≠ 0 → |τ| < η₂ → ∀ x, P x = x →
      |⟪x, schurS P (X 0 (t₀ + τ)) x⟫ - τ * ⟪x, X' x⟫| ≤ |τ| * (σ₀ / 2) * ‖x‖ ^ 2 := by
    intro τ hτ hτη x hx
    have hne : t₀ + τ ≠ t₀ := by intro h; apply hτ; linarith
    have hΨt := hη₂' (show dist (t₀ + τ) t₀ < η₂ by
      rw [Real.dist_eq, add_sub_cancel_left]; exact hτη) hne
    rw [add_sub_cancel_left] at hΨt
    set Ψ := τ⁻¹ • schurS P (X 0 (t₀ + τ)) - P * X' * P with hΨdef
    have hS : schurS P (X 0 (t₀ + τ)) = τ • (P * X' * P + Ψ) := by
      rw [hΨdef, add_sub_cancel, smul_smul, mul_inv_cancel₀ hτ, one_smul]
    have hPXP : ⟪x, (P * X' * P) x⟫ = ⟪x, X' x⟫ := by
      rw [mul_apply_eq_comp, mul_apply_eq_comp, hx, ← hPs, hx]
    rw [hS, smul_apply, inner_smul_right, add_apply, inner_add_right, hPXP]
    have hq := quad_le_norm Ψ x
    have : τ * (⟪x, X' x⟫ + ⟪x, Ψ x⟫) - τ * ⟪x, X' x⟫ = τ * ⟪x, Ψ x⟫ := by ring
    rw [this, abs_mul]
    have h3 : ‖Ψ‖ * ‖x‖ ^ 2 ≤ σ₀ / 2 * ‖x‖ ^ 2 := by gcongr
    calc |τ| * |⟪x, Ψ x⟫| ≤ |τ| * (‖Ψ‖ * ‖x‖ ^ 2) := by gcongr
      _ ≤ |τ| * (σ₀ / 2 * ‖x‖ ^ 2) := by gcongr
      _ = |τ| * (σ₀ / 2) * ‖x‖ ^ 2 := by ring
  have hleft : ∀ x, P x = x → η * (σ₀ / 2) * ‖x‖ ^ 2 ≤ ⟪x, schurS P (X 0 (t₀ - η)) x⟫ := by
    intro x hx
    have h := hvacform (-η) (neg_ne_zero.mpr hηpos.ne')
      (by rw [abs_neg, abs_of_pos hηpos]; exact hη2) x hx
    rw [← sub_eq_add_neg, abs_neg, abs_of_pos hηpos] at h
    have hs := hσc x hx
    rw [neg_apply, inner_neg_right] at hs
    have h1 := (abs_le.mp h).1
    have h2 := mul_le_mul_of_nonneg_left hs hηpos.le
    nlinarith
  have hright : ∀ x, P x = x → ⟪x, schurS P (X 0 (t₀ + η)) x⟫ ≤ -(η * (σ₀ / 2) * ‖x‖ ^ 2) := by
    intro x hx
    have h := hvacform η hηpos.ne' (by rw [abs_of_pos hηpos]; exact hη2) x hx
    rw [abs_of_pos hηpos] at h
    have hs := hσc x hx
    rw [neg_apply, inner_neg_right] at hs
    have h1 := (abs_le.mp h).2
    have h2 := mul_le_mul_of_nonneg_left hs hηpos.le
    nlinarith
  -- (6) the corrected Schur form at the two ends, for small `ε`
  have hend : ∀ τ : ℝ, |τ| = η → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖schurS P (X ε (t₀ + τ) - D ε) - schurS P (X 0 (t₀ + τ))‖ < η * (σ₀ / 4) := by
    intro τ hτ
    have hcl : |t₀ + τ - t₀| < η₀ := by rw [add_sub_cancel_left, hτ]; exact hη0
    have hX1 : Tendsto (fun ε : ℝ => X ε (t₀ + τ)) (𝓝[>] 0) (𝓝 (X 0 (t₀ + τ))) := by
      have h := (hjoint (t₀ + τ) hcl).tendsto
      exact h.comp (Tendsto.prodMk_nhds (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
        tendsto_const_nhds)
    have hY1 : Tendsto (fun ε : ℝ => X ε (t₀ + τ) - D ε) (𝓝[>] 0) (𝓝 (X 0 (t₀ + τ))) := by
      have := hX1.sub hD0
      rwa [sub_zero] at this
    have hu : IsUnit (schurC P (X 0 (t₀ + τ))) := hη₃' (by
      rw [Real.dist_eq, add_sub_cancel_left, hτ]; exact hη3)
    have hS1 := tendsto_schurS P hu hY1
    exact (tendsto_iff_norm_sub_tendsto_zero.mp hS1).eventually (gt_mem_nhds (by positivity))
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp ((hend (-η) (by rw [abs_neg, abs_of_pos hηpos])).and
      (hend η (abs_of_pos hηpos))))
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun ε hε hεδ => ?_⟩
  have hεδ₁ : ε < δ₁ := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεδ₂ : ε < δ₂ := lt_of_lt_of_le hεδ (min_le_right _ _)
  obtain ⟨hendL, hendR⟩ := hδ₂' (show dist ε 0 < δ₂ by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact hεδ₂) hε
  rw [← sub_eq_add_neg] at hendL
  -- (7) the path argument on `[t₀ - η, t₀ + η]`
  have hin : ∀ u ∈ Icc (0 : ℝ) (2 * η), |t₀ - η + u - t₀| < η₁ := by
    intro u hu
    have : |t₀ - η + u - t₀| ≤ η := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    linarith
  have hBc : ContinuousOn (fun u => schurS P (X ε (t₀ - η + u) - D ε)) (Icc 0 (2 * η)) := by
    intro u hu
    have hun := (hoff ε (t₀ - η + u) hε hεδ₁ (hin u hu)).2.1
    have hc : Tendsto (fun u' => X ε (t₀ - η + u') - D ε) (𝓝 u)
        (𝓝 (X ε (t₀ - η + u) - D ε)) := by
      have : Continuous (fun u' => X ε (t₀ - η + u') - D ε) :=
        ((hXc ε).comp (continuous_const.add continuous_id)).sub continuous_const
      exact this.tendsto u
    exact ContinuousAt.continuousWithinAt (tendsto_schurS P hun hc)
  have hYs : ∀ u x y, ⟪(X ε (t₀ - η + u) - D ε) x, y⟫ = ⟪x, (X ε (t₀ - η + u) - D ε) y⟫ := by
    intro u x y
    rw [sub_apply, sub_apply, inner_sub_left, inner_sub_right, hXs, hDs]
  have hB0 : ∀ x, P x = x → 0 ≤ ⟪x, schurS P (X ε (t₀ - η + 0) - D ε) x⟫ := by
    intro x hx
    have e : t₀ - η + 0 = t₀ - η := by ring
    rw [e]
    have h1 := hleft x hx
    have h2 := quad_le_norm (schurS P (X ε (t₀ - η) - D ε) - schurS P (X 0 (t₀ - η))) x
    rw [sub_apply, inner_sub_right] at h2
    have h3 := mul_le_mul_of_nonneg_right hendL.le (sq_nonneg ‖x‖)
    have h4 : 0 ≤ η * σ₀ * ‖x‖ ^ 2 := by positivity
    have := (abs_le.mp h2).1
    nlinarith
  have hBT : ⟪w, schurS P (X ε (t₀ - η + 2 * η) - D ε) w⟫ < 0 := by
    have e : t₀ - η + 2 * η = t₀ + η := by ring
    rw [e]
    have h1 := hright w hwP
    have h2 := quad_le_norm (schurS P (X ε (t₀ + η) - D ε) - schurS P (X 0 (t₀ + η))) w
    rw [sub_apply, inner_sub_right] at h2
    have h3 := mul_le_mul_of_nonneg_right hendR.le (sq_nonneg ‖w‖)
    have h4 : 0 < η * σ₀ * ‖w‖ ^ 2 := by
      have := norm_pos_iff.mpr hw0; positivity
    have := (abs_le.mp h2).2
    nlinarith
  have hAB : ∀ u ∈ Icc 0 (2 * η), ∀ x, P x = x → x ≠ 0 →
      ⟪x, schurS P (X ε (t₀ - η + u) - D ε) x⟫ < ⟪x, schurS P (X ε (t₀ - η + u)) x⟫ := by
    intro u hu x hx hx0
    obtain ⟨-, -, hΦ⟩ := hoff ε (t₀ - η + u) hε hεδ₁ (hin u hu)
    set Φ := ε⁻¹ • (schurS P (X ε (t₀ - η + u)) - schurS P (X ε (t₀ - η + u) - D ε)) -
      P * D₁ * P with hΦdef
    have hdiff : schurS P (X ε (t₀ - η + u)) - schurS P (X ε (t₀ - η + u) - D ε) =
        ε • (P * D₁ * P + Φ) := by
      rw [hΦdef, add_sub_cancel, smul_smul, mul_inv_cancel₀ (ne_of_gt hε), one_smul]
    have hPDP : ⟪x, (P * D₁ * P) x⟫ = ⟪x, D₁ x⟫ := by
      rw [mul_apply_eq_comp, mul_apply_eq_comp, hx, ← hPs, hx]
    have hform : ⟪x, schurS P (X ε (t₀ - η + u)) x⟫ - ⟪x, schurS P (X ε (t₀ - η + u) - D ε) x⟫ =
        ε * (⟪x, D₁ x⟫ + ⟪x, Φ x⟫) := by
      rw [← inner_sub_right, ← sub_apply, hdiff, smul_apply, inner_smul_right, add_apply,
        inner_add_right, hPDP]
    have hq := quad_le_norm Φ x
    have hn := hνc x hx
    have hx2 : 0 < ν * ‖x‖ ^ 2 := by have := norm_pos_iff.mpr hx0; positivity
    have h3 := mul_le_mul_of_nonneg_right hΦ.le (sq_nonneg ‖x‖)
    have h4 := (abs_le.mp hq).1
    have h5 : 0 < ⟪x, D₁ x⟫ + ⟪x, Φ x⟫ := by nlinarith
    have h6 : 0 < ε * (⟪x, D₁ x⟫ + ⟪x, Φ x⟫) := mul_pos hε h5
    linarith
  obtain ⟨u, hu0, huT, hAinj, y, hyP, hy0, hBy⟩ :=
    core_separation P hP hPs (fun u => schurS P (X ε (t₀ - η + u)))
      (fun u => schurS P (X ε (t₀ - η + u) - D ε)) (2 * η) (by positivity) hBc
      (fun u x y => schurS_symm P _ hPs (hYs u) x y)
      (fun u v => schurS_left P _ hP v) (fun u v => schurS_right P _ hP v)
      hB0 w hwP hBT hAB
  have huI : u ∈ Icc (0 : ℝ) (2 * η) := ⟨hu0, huT.le⟩
  obtain ⟨hCX, hCY, -⟩ := hoff ε (t₀ - η + u) hε hεδ₁ (hin u huI)
  refine ⟨t₀ - η + u, (schur_unit_iff hP hCX).mpr hAinj, fun hY => ?_⟩
  exact hy0 ((schur_unit_iff hP hCY).mp hY y hyP hBy)

/-- Perturbative separation, either sign of the first-order correction on the kernel. -/
theorem separation_of_vacuum_data
    (X : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E) (P : E →L[ℝ] E)
    (hP : P * P = P) (hPs : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (hXs : ∀ ε t x y, ⟪X ε t x, y⟫ = ⟪x, X ε t y⟫)
    (hDs : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (hXc : ∀ ε, Continuous (X ε))
    (t₀ η₀ : ℝ) (hη₀ : 0 < η₀)
    (hjoint : ∀ t, |t - t₀| < η₀ → ContinuousAt (fun p : ℝ × ℝ => X p.1 p.2) (0, t))
    (X' : E →L[ℝ] E) (hder : HasDerivAt (X 0) X' t₀)
    (D₁ : E →L[ℝ] E) (hD : Tendsto (fun ε : ℝ => ε⁻¹ • D ε) (𝓝[>] 0) (𝓝 D₁))
    (hXP : X 0 t₀ * P = 0) (hker : ∀ x, X 0 t₀ x = 0 → P x = x)
    (w : E) (hwP : P w = w) (hw0 : w ≠ 0)
    (hslope : ∀ v, P v = v → v ≠ 0 → ⟪v, X' v⟫ < 0)
    (hsign : (∀ v, P v = v → v ≠ 0 → ⟪v, D₁ v⟫ < 0) ∨
      (∀ v, P v = v → v ≠ 0 → 0 < ⟪v, D₁ v⟫)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ t : ℝ, IsUnit (X ε t) ∧ ¬ IsUnit (X ε t - D ε) := by
  rcases hsign with hneg | hpos
  · -- reflect the angle about `t₀` and change the overall sign
    set Xr : ℝ → ℝ → E →L[ℝ] E := fun ε t => -X ε (2 * t₀ - t) with hXr
    set Dr : ℝ → E →L[ℝ] E := fun ε => -D ε with hDr
    have h2t : 2 * t₀ - t₀ = t₀ := by ring
    have hXr0 : Xr 0 t₀ = -X 0 t₀ := by simp only [hXr, h2t]
    have hXrs : ∀ ε t x y, ⟪Xr ε t x, y⟫ = ⟪x, Xr ε t y⟫ := by
      intro ε t x y
      simp only [hXr, neg_apply, inner_neg_left, inner_neg_right, hXs]
    have hDrs : ∀ ε x y, ⟪Dr ε x, y⟫ = ⟪x, Dr ε y⟫ := by
      intro ε x y
      simp only [hDr, neg_apply, inner_neg_left, inner_neg_right, hDs]
    have hXrc : ∀ ε, Continuous (Xr ε) := fun ε =>
      ((hXc ε).comp (continuous_const.sub continuous_id)).neg
    have hjr : ∀ t, |t - t₀| < η₀ → ContinuousAt (fun p : ℝ × ℝ => Xr p.1 p.2) (0, t) := by
      intro t ht
      have h1 : |2 * t₀ - t - t₀| < η₀ := by
        rw [show 2 * t₀ - t - t₀ = -(t - t₀) by ring, abs_neg]; exact ht
      have h2 := hjoint (2 * t₀ - t) h1
      have hmap : ContinuousAt (fun p : ℝ × ℝ => (p.1, 2 * t₀ - p.2)) (0, t) :=
        (continuous_fst.prodMk (continuous_const.sub continuous_snd)).continuousAt
      have h3 := ContinuousAt.comp (f := fun p : ℝ × ℝ => (p.1, 2 * t₀ - p.2))
        (g := fun p : ℝ × ℝ => X p.1 p.2) h2 hmap
      exact h3.neg
    have hderr : HasDerivAt (Xr 0) X' t₀ := by
      have h1 : HasDerivAt (fun t : ℝ => 2 * t₀ - t) (-1) t₀ := by
        simpa using (hasDerivAt_id t₀).const_sub (2 * t₀)
      have h2 : HasDerivAt (X 0) X' (2 * t₀ - t₀) := by rw [h2t]; exact hder
      have h3 := h2.scomp t₀ h1
      have h4 := h3.neg
      simp only [neg_smul, one_smul, neg_neg] at h4
      exact h4
    have hDr1 : Tendsto (fun ε : ℝ => ε⁻¹ • Dr ε) (𝓝[>] 0) (𝓝 (-D₁)) := by
      simp only [hDr, smul_neg]
      exact hD.neg
    have hXrP : Xr 0 t₀ * P = 0 := by rw [hXr0, neg_mul, hXP, neg_zero]
    have hkerr : ∀ x, Xr 0 t₀ x = 0 → P x = x := by
      intro x hx
      rw [hXr0, neg_apply, neg_eq_zero] at hx
      exact hker x hx
    have hposr : ∀ v, P v = v → v ≠ 0 → 0 < ⟪v, (-D₁) v⟫ := by
      intro v hv hv0
      rw [neg_apply, inner_neg_right]
      linarith [hneg v hv hv0]
    obtain ⟨δ, hδ, hsep⟩ := separation_of_vacuum_data_pos Xr Dr P hP hPs hXrs hDrs hXrc t₀ η₀ hη₀
      hjr X' hderr (-D₁) hDr1 hXrP hkerr w hwP hw0 hslope hposr
    refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
    obtain ⟨t, hu, hnu⟩ := hsep ε hε hεδ
    refine ⟨2 * t₀ - t, ?_, ?_⟩
    · have := hu.neg
      simpa [hXr] using this
    · intro hcon
      apply hnu
      have : Xr ε t - Dr ε = -(X ε (2 * t₀ - t) - D ε) := by
        simp only [hXr, hDr]; abel
      rw [this]
      exact hcon.neg
  · exact separation_of_vacuum_data_pos X D P hP hPs hXs hDs hXc t₀ η₀ hη₀ hjoint X' hder D₁ hD
      hXP hker w hwP hw0 hslope hpos

/-- The same with the kernel of the vacuum carrier itself as the crossing space. -/
theorem separation_of_vacuum_kernel
    (X : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E)
    (hXs : ∀ ε t x y, ⟪X ε t x, y⟫ = ⟪x, X ε t y⟫)
    (hDs : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (hXc : ∀ ε, Continuous (X ε))
    (t₀ η₀ : ℝ) (hη₀ : 0 < η₀)
    (hjoint : ∀ t, |t - t₀| < η₀ → ContinuousAt (fun p : ℝ × ℝ => X p.1 p.2) (0, t))
    (X' : E →L[ℝ] E) (hder : HasDerivAt (X 0) X' t₀)
    (D₁ : E →L[ℝ] E) (hD : Tendsto (fun ε : ℝ => ε⁻¹ • D ε) (𝓝[>] 0) (𝓝 D₁))
    (hne : ∃ v, X 0 t₀ v = 0 ∧ v ≠ 0)
    (hslope : ∀ v, X 0 t₀ v = 0 → v ≠ 0 → ⟪v, X' v⟫ < 0)
    (hsign : (∀ v, X 0 t₀ v = 0 → v ≠ 0 → ⟪v, D₁ v⟫ < 0) ∨
      (∀ v, X 0 t₀ v = 0 → v ≠ 0 → 0 < ⟪v, D₁ v⟫)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ t : ℝ, IsUnit (X ε t) ∧ ¬ IsUnit (X ε t - D ε) := by
  set K : Submodule ℝ E := LinearMap.ker (X 0 t₀ : E →ₗ[ℝ] E) with hK
  set P : E →L[ℝ] E := K.starProjection with hPdef
  have hP : P * P = P := K.isIdempotentElem_starProjection
  have hPs : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫ := fun x y => K.inner_starProjection_left_eq_right x y
  have hmem : ∀ x, P x = x ↔ X 0 t₀ x = 0 := by
    intro x
    rw [hPdef, Submodule.starProjection_eq_self_iff, hK, LinearMap.mem_ker]
    try rfl
  have hXP : X 0 t₀ * P = 0 := by
    ext x
    rw [mul_apply_eq_comp, zero_apply]
    have : P x ∈ K := K.starProjection_apply_mem x
    rw [hK, LinearMap.mem_ker] at this
    exact this
  obtain ⟨w, hw, hw0⟩ := hne
  refine separation_of_vacuum_data X D P hP hPs hXs hDs hXc t₀ η₀ hη₀ hjoint X' hder D₁ hD hXP
    (fun x hx => (hmem x).mpr hx) w ((hmem w).mpr hw) hw0
    (fun v hv hv0 => hslope v ((hmem v).mp hv) hv0) ?_
  rcases hsign with h | h
  · exact Or.inl (fun v hv hv0 => h v ((hmem v).mp hv) hv0)
  · exact Or.inr (fun v hv hv0 => h v ((hmem v).mp hv) hv0)

end MainTheorem

section Instantiation

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-! ## The actual twist family

`X ε t = twistA q R ε 1 t` (the all-plaquette carrier, curvature `ε` at the interior
defect, exterior twist angle `t`), `D ε = twistD q R ε 1 0` (the localized correction,
independent of the exterior angle by `twistD_constant`).  The premise below is a
statement about zero curvature only, plus soft regularity in `(ε, t)` at `ε = 0`.
It is NOT proved here. -/

/-- The carrier space of the twist family at scale `q` and radius `R`. -/
abbrev TwistSpace (q R : ℕ) : Type := ↥(bondSupp (geomOf 2 1 (dilTower q R)))

/-- Soft regularity at zero curvature (no spectral content): the carrier is jointly
continuous in `(ε, t)` at `ε = 0`, and the correction has the first-order coefficient
`D₁` as `ε → 0⁺`.  NOT proved here. -/
def ZeroCurvatureRegularity (q R : ℕ) (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R) : Prop :=
  (∀ t : ℝ, ContinuousAt (fun p : ℝ × ℝ => twistA q R p.1 1 p.2) (0, t)) ∧
  Tendsto (fun ε : ℝ => ε⁻¹ • twistD q R ε 1 0) (𝓝[>] 0) (𝓝 D₁)

/-- The vacuum crossing data (spectral content, at zero curvature only): at some angle
`t₀` the vacuum carrier is singular, it has an angle derivative `X'` there which is
negative definite on the kernel, and the first-order correction `D₁` is definite (of
either sign) on the kernel.  NOT proved here. -/
def VacuumCrossing (q R : ℕ) (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R) : Prop :=
  ∃ (t₀ : ℝ) (X' : TwistSpace q R →L[ℝ] TwistSpace q R), HasDerivAt (twistA q R 0 1) X' t₀ ∧
    (∃ v, twistA q R 0 1 t₀ v = 0 ∧ v ≠ 0) ∧
    (∀ v, twistA q R 0 1 t₀ v = 0 → v ≠ 0 → ⟪v, X' v⟫ < 0) ∧
    ((∀ v, twistA q R 0 1 t₀ v = 0 → v ≠ 0 → ⟪v, D₁ v⟫ < 0) ∨
      (∀ v, twistA q R 0 1 t₀ v = 0 → v ≠ 0 → 0 < ⟪v, D₁ v⟫))

/-- Vacuum nondegeneracy of the actual family at `(q, R)`. -/
def VacuumNondegeneracy (q R : ℕ) : Prop :=
  ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R, ZeroCurvatureRegularity q R D₁ ∧ VacuumCrossing q R D₁

/-- Step (2) of the route, on the actual operators: vacuum nondegeneracy at `(q, R)`
gives a guarded separation at EVERY small positive curvature. -/
theorem eventually_twistSeparation_of_vacuum {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (h : VacuumNondegeneracy q R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → TwistSeparation q R ε := by
  obtain ⟨D₁, ⟨hjoint, hD⟩, t₀, X', hder, hne, hslope, hsign⟩ := h
  have hXs : ∀ ε t x y, ⟪twistA q R ε 1 t x, y⟫ = ⟪x, twistA q R ε 1 t y⟫ := by
    intro ε t x y
    exact (dataS selAll selAll (twistP q R ε 1 t)).Ginv_symm (dataS_laws selAll selAll _) x y
  have hDs : ∀ ε x y, ⟪twistD q R ε 1 0 x, y⟫ = ⟪x, twistD q R ε 1 0 y⟫ := by
    intro ε x y
    exact ((dataS selIn selIn (twistP q R ε 1 0)).Delta2_spec (dataS_laws selIn selIn _)).1 x y
  obtain ⟨δ, hδ, hsep⟩ := separation_of_vacuum_kernel (fun ε t => twistA q R ε 1 t)
    (fun ε => twistD q R ε 1 0) hXs hDs (fun ε => twistA_continuous hq hR hroom ε 1)
    t₀ 1 one_pos (fun t _ => hjoint t) X' hder D₁ hD hne hslope hsign
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  obtain ⟨t, hu, hnu⟩ := hsep ε hε hεδ
  refine ⟨t, hu, ?_⟩
  rw [twistD_constant hq hR hroom ε 1 t]
  exact hnu

/-- The cofinal premise of this route: vacuum nondegeneracy for infinitely many dyadic
scales and, for each, infinitely many even radii `R ≥ 18`.  NOT proved here. -/
def CofinalVacuumNondegeneracy : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    VacuumNondegeneracy (2^j) R

theorem cofinalTwistSeparation_of_cofinalVacuum (h : CofinalVacuumNondegeneracy) :
    CofinalTwistSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun δ hδ => ?_⟩
  have hq : 0 < 2^j := by positivity
  obtain ⟨δ', hδ', hsep⟩ := eventually_twistSeparation_of_vacuum hq hR (by nlinarith) hv
  have hm : 0 < min δ δ' := lt_min hδ hδ'
  refine ⟨min δ δ' / 2, by positivity, ?_, hsep _ (by positivity) ?_⟩
  · linarith [min_le_left δ δ']
  · linarith [min_le_right δ δ']

/-- Main reduction of this round: cofinal vacuum nondegeneracy refutes the guarded
all-plaquette reading. -/
theorem goalNeg2_of_cofinalVacuum (h : CofinalVacuumNondegeneracy) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_cofinalVacuum h)

/-- And the positive reading forbids cofinal vacuum nondegeneracy. -/
theorem not_cofinalVacuum_of_goalPos1 (h : GoalPos1) : ¬ CofinalVacuumNondegeneracy :=
  fun h' => not_cofinalTwistSeparation_of_goalPos1 h (cofinalTwistSeparation_of_cofinalVacuum h')

/-! ## Any exterior field

The class conditions of the curved dilated family hold for EVERY exterior field `V`
(`dil_regular` takes an arbitrary `V`), and the localized data do not depend on it.
So the cofinal bridge only needs SOME exterior field per instance, not one on the
round-5 twist.  For a continuous exterior path the vacuum reduction above applies
verbatim.  This lets the remaining premise be stated for the path that makes the
vacuum problem cleanest: twisting only the LEFT half of the exterior slab removes the
right boundary crossing, so the vacuum crossing is a single boundary mode with an O(1)
gap instead of an exponentially small left/right splitting. -/

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

/-- Separation at `(q, R, ε)` for SOME exterior field.  NOT proved here. -/
def ExtSeparation (q R : ℕ) (ε : ℝ) : Prop :=
  ∃ V : LinkCfg (scaleUp 2 1 (dilLu q R)),
    IsUnit (extA q R ε V) ∧ ¬ IsUnit (extA q R ε V - extD q R ε V)

/-- The cofinal form, with the quantifiers of `CofinalTwistSeparation`.  NOT proved here. -/
def CofinalExtSeparation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ExtSeparation (2^j) R ε

/-- Cofinal bridge for an arbitrary exterior field: the round-8 bookkeeping, with the
exterior field left free (same witnesses `m = j+1`, `R` before the cap, `α = 160 ε`). -/
theorem goalNeg2_of_cofinalExtSeparation (h : CofinalExtSeparation) : GoalNeg2 := by
  apply cofinalPencilFailure_implies_goalNeg2
  refine ⟨2, by norm_num, 1, by norm_num, ?_⟩
  intro m₀
  obtain ⟨j, hj, hRs⟩ := h m₀
  refine ⟨j+1, by omega, by omega, ?_⟩
  intro R₀
  obtain ⟨R, hRR, hR, hR18, hsep⟩ := hRs R₀
  refine ⟨R, hRR, ?_⟩
  intro a₀ ha₀
  let q := 2^j
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(j+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let δ : ℝ := min (a₀/(3840*q)) 1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ε, hε0, hεδ, V, hu, hnu⟩ := hsep δ hδ
  let α : ℝ := 160*ε
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ := by
    have he : ε < a₀/(3840*q) := lt_of_lt_of_le hεδ (min_le_left _ _)
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3840*q)).mp he
    dsimp [α]; push_cast; nlinarith
  have heps : |ε| ≤ α/80 := by rw [abs_of_pos hε0]; dsimp [α]; linarith
  have hclass : ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (dilU q R ε V) :=
    ⟨dil_coverage hq hR (by omega), dil_regular hq hR hα heps _⟩
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR
  rw [hpow]
  exact ⟨1, by norm_num, dilLu q R, α, hα, hcap, dil_torus hq R,
    dilTower q R, dil_admissible hq hR, dilLam q R, dil_lambda hq hR,
    dilU q R ε V, hclass, dilBt hq R, hBt1, hBt2, hE, hu, hnu⟩

/-- The positive reading forbids it. -/
theorem not_cofinalExtSeparation_of_goalPos1 (h : GoalPos1) : ¬ CofinalExtSeparation :=
  fun h' => goalNeg2_of_cofinalExtSeparation h' (goalPos2_iff_goalPos1.mpr h)

/-- The round-8 premise is a special case (exterior field `Uth t`). -/
theorem extSeparation_of_twistSeparation {q R : ℕ} {ε : ℝ} (h : TwistSeparation q R ε) :
    ExtSeparation q R ε := by
  obtain ⟨t, hu, hnu⟩ := h
  exact ⟨AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t, hu, hnu⟩

theorem cofinalExtSeparation_of_cofinalTwistSeparation (h : CofinalTwistSeparation) :
    CofinalExtSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hs⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun δ hδ => ?_⟩
  obtain ⟨ε, hε, hεδ, ht⟩ := hs δ hδ
  exact ⟨ε, hε, hεδ, extSeparation_of_twistSeparation ht⟩

/-- Only the exterior field's values on bonds with no endpoint in `Ω₀` enter `dilU`. -/
theorem dilU_agree (q R : ℕ) (ε : ℝ) (V V' : LinkCfg (scaleUp 2 1 (dilLu q R)))
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)) :
    dilU q R ε V e = dilU q R ε V' e := by
  classical
  simp only [dilU, if_neg he]

/-- The localized correction does not depend on the exterior field. -/
theorem extD_congr {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q)) (ε : ℝ)
    (V V' : LinkCfg (scaleUp 2 1 (dilLu q R))) : extD q R ε V = extD q R ε V' := by
  have hd : dataS selIn selIn (extP q R ε V) = dataS selIn selIn (extP q R ε V') := by
    change (extP q R ε V).data = (extP q R ε V').data
    exact AdalyFormal.M1IMS.data_congr_U (by norm_num) (dil_admissible hq hR)
      (by norm_num) hroom (dilU q R ε V') (dilU q R ε V) 1 (dilLam q R)
      (fun e he => dilU_agree q R ε V' V e (fun hz => hz.1 he.1))
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

theorem extPath_cont (q R : ℕ) (ε : ℝ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (hV : AdalyFormal.D1Literal.ContFam V) :
    AdalyFormal.D1Literal.ContFam (fun t => dilU q R ε (V t)) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [dilU, if_pos he]
    exact hV e
  · simp only [dilU, if_neg he]
    exact continuous_const

/-- Carrier continuity along any continuous exterior path (round-5 proof, path left free). -/
theorem extA_continuous {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q)) (ε : ℝ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (hV : AdalyFormal.D1Literal.ContFam V) :
    Continuous (fun t => extA q R ε (V t)) := by
  let G := geomOf 2 1 (dilTower q R)
  let U : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) := fun t => dilU q R ε (V t)
  have h : (fun t => extA q R ε (V t)) = fun t => extA q R ε (V 0) +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wop G (U 0) 1)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (U t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (U 0) Set.univ)).comp
          (Wop G (U 0) 1))).comp (iE G)) := by
    funext t
    exact exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      1 (dilLam q R) U (fun s e he => dilU_agree q R ε (V s) (V 0) e he) selAll t
  rw [h]
  have hd : Continuous fun t => AdalyFormal.StatementLaneR6.deltaKLocCLM (U t)
      (Set.univ : Set (PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)))) :=
    AdalyFormal.D1Literal.cont_deltaKLocCLM (extPath_cont q R ε V hV) _
  refine continuous_const.add
    (Continuous.clm_comp continuous_const (Continuous.clm_comp ?_ continuous_const))
  exact Continuous.clm_comp continuous_const
    (Continuous.clm_comp (hd.sub continuous_const) continuous_const)

/-- Soft regularity along an exterior path at zero curvature (no spectral content): joint
continuity of the carrier at `ε = 0` and the first-order coefficient of the correction.
NOT proved here. -/
def PathRegularity (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R) : Prop :=
  (∀ t : ℝ, ContinuousAt (fun p : ℝ × ℝ => extA q R p.1 (V p.2)) (0, t)) ∧
  Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε (V 0)) (𝓝[>] 0) (𝓝 D₁)

/-- Vacuum crossing data along an exterior path (zero curvature only).  NOT proved here. -/
def PathCrossing (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R) : Prop :=
  ∃ (t₀ : ℝ) (X' : TwistSpace q R →L[ℝ] TwistSpace q R),
    HasDerivAt (fun t => extA q R 0 (V t)) X' t₀ ∧
    (∃ v, extA q R 0 (V t₀) v = 0 ∧ v ≠ 0) ∧
    (∀ v, extA q R 0 (V t₀) v = 0 → v ≠ 0 → ⟪v, X' v⟫ < 0) ∧
    ((∀ v, extA q R 0 (V t₀) v = 0 → v ≠ 0 → ⟪v, D₁ v⟫ < 0) ∨
      (∀ v, extA q R 0 (V t₀) v = 0 → v ≠ 0 → 0 < ⟪v, D₁ v⟫))

/-- Vacuum nondegeneracy along a continuous exterior path. -/
def PathVacuumNondegeneracy (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : Prop :=
  AdalyFormal.D1Literal.ContFam V ∧
  ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R, PathRegularity q R V D₁ ∧ PathCrossing q R V D₁

/-- Step (2) along any continuous exterior path. -/
theorem eventually_extSeparation_of_pathVacuum {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (h : PathVacuumNondegeneracy q R V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ExtSeparation q R ε := by
  obtain ⟨hV, D₁, ⟨hjoint, hD⟩, t₀, X', hder, hne, hslope, hsign⟩ := h
  have hXs : ∀ ε t x y, ⟪extA q R ε (V t) x, y⟫ = ⟪x, extA q R ε (V t) y⟫ := by
    intro ε t x y
    exact (dataS selAll selAll (extP q R ε (V t))).Ginv_symm (dataS_laws selAll selAll _) x y
  have hDs : ∀ ε x y, ⟪extD q R ε (V 0) x, y⟫ = ⟪x, extD q R ε (V 0) y⟫ := by
    intro ε x y
    exact ((dataS selIn selIn (extP q R ε (V 0))).Delta2_spec (dataS_laws selIn selIn _)).1 x y
  obtain ⟨δ, hδ, hsep⟩ := separation_of_vacuum_kernel (fun ε t => extA q R ε (V t))
    (fun ε => extD q R ε (V 0)) hXs hDs (fun ε => extA_continuous hq hR hroom ε V hV)
    t₀ 1 one_pos (fun t _ => hjoint t) X' hder D₁ hD hne hslope hsign
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  obtain ⟨t, hu, hnu⟩ := hsep ε hε hεδ
  refine ⟨V t, hu, ?_⟩
  rw [extD_congr hq hR hroom ε (V t) (V 0)]
  exact hnu

/-- The cofinal premise with the exterior path free.  NOT proved here. -/
def CofinalPathVacuum : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), PathVacuumNondegeneracy (2^j) R V

theorem cofinalExtSeparation_of_cofinalPathVacuum (h : CofinalPathVacuum) :
    CofinalExtSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hv⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun δ hδ => ?_⟩
  have hq : 0 < 2^j := by positivity
  obtain ⟨δ', hδ', hsep⟩ := eventually_extSeparation_of_pathVacuum hq hR (by nlinarith) V hv
  have hm : 0 < min δ δ' := lt_min hδ hδ'
  refine ⟨min δ δ' / 2, by positivity, ?_, hsep _ (by positivity) ?_⟩
  · linarith [min_le_left δ δ']
  · linarith [min_le_right δ δ']

theorem goalNeg2_of_cofinalPathVacuum (h : CofinalPathVacuum) : GoalNeg2 :=
  goalNeg2_of_cofinalExtSeparation (cofinalExtSeparation_of_cofinalPathVacuum h)

theorem not_cofinalPathVacuum_of_goalPos1 (h : GoalPos1) : ¬ CofinalPathVacuum :=
  fun h' => not_cofinalExtSeparation_of_goalPos1 h (cofinalExtSeparation_of_cofinalPathVacuum h')

open Classical in
/-- The exterior twist on the left half of the exterior slab only (longitudinal base
coordinate below `4q`, the left end of `Ω₀`), identity elsewhere. -/
noncomputable def leftTwist (q R : ℕ) (t : ℝ) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) ∧ (e.1 0).val < 4 * q
    then AdalyFormal.D1Literal.uθ t else 1

theorem leftTwist_cont (q R : ℕ) : AdalyFormal.D1Literal.ContFam (leftTwist q R) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) ∧ (e.1 0).val < 4 * q
  · simp only [leftTwist, if_pos he]
    show Continuous fun θ => AdalyFormal.D1Literal.uMat θ
    unfold AdalyFormal.D1Literal.uMat
    refine continuous_matrix (fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · simp only [leftTwist, if_neg he]
    exact continuous_const

/-- The recommended cofinal premise: vacuum nondegeneracy along the LEFT twist.
NOT proved here. -/
def CofinalLeftVacuum : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ D₁ : TwistSpace (2^j) R →L[ℝ] TwistSpace (2^j) R,
      PathRegularity (2^j) R (leftTwist (2^j) R) D₁ ∧ PathCrossing (2^j) R (leftTwist (2^j) R) D₁

theorem goalNeg2_of_cofinalLeftVacuum (h : CofinalLeftVacuum) : GoalNeg2 := by
  apply goalNeg2_of_cofinalPathVacuum
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, D₁, hreg, hcr⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, leftTwist (2^j) R, leftTwist_cont _ _, D₁, hreg, hcr⟩

/-- The non-spectral half of the left-twist premise: a uniform analyticity statement at
zero curvature (joint continuity of the carrier, first-order coefficient of the
correction), for every admissible scale and radius.  NOT proved here. -/
def LeftSoft : Prop :=
  ∀ q R : ℕ, 0 < q → 2 ∣ R → 18 ≤ R →
    ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R, PathRegularity q R (leftTwist q R) D₁

/-- The spectral half: for cofinal dyadic scales and radii, the vacuum crossing data of
the left twist, for the first-order coefficient of the correction.  NOT proved here. -/
def LeftSpectral : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ D₁ : TwistSpace (2^j) R →L[ℝ] TwistSpace (2^j) R,
      PathRegularity (2^j) R (leftTwist (2^j) R) D₁ → PathCrossing (2^j) R (leftTwist (2^j) R) D₁

theorem cofinalLeftVacuum_of_soft_spectral (hs : LeftSoft) (hc : LeftSpectral) :
    CofinalLeftVacuum := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := hc j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hcr⟩ := hRs R₀
  obtain ⟨D₁, hreg⟩ := hs (2^j) R (by positivity) hR hR18
  exact ⟨R, hRR, hR, hR18, D₁, hreg, hcr D₁ hreg⟩

/-- Final form of the reduction: soft regularity plus cofinal vacuum crossing data of
the left twist refute the guarded all-plaquette reading. -/
theorem goalNeg2_of_leftSoft_leftSpectral (hs : LeftSoft) (hc : LeftSpectral) : GoalNeg2 :=
  goalNeg2_of_cofinalLeftVacuum (cofinalLeftVacuum_of_soft_spectral hs hc)

end Instantiation

#print axioms exists_psd_nonunit_path
#print axioms exists_coercive_on_range
#print axioms schurC
#print axioms schurS
#print axioms inverse_symm
#print axioms schurS_symm
#print axioms schurS_left
#print axioms schurS_right
#print axioms schur_unit_iff
#print axioms tendsto_inverse_of_unit
#print axioms schurC_continuous
#print axioms tendsto_schurS
#print axioms quad_le_norm
#print axioms vacuum_schur_slope
#print axioms schur_difference_identity
#print axioms schur_difference_tendsto
#print axioms core_separation
#print axioms separation_of_vacuum_data_pos
#print axioms separation_of_vacuum_data
#print axioms separation_of_vacuum_kernel
#print axioms TwistSpace
#print axioms ZeroCurvatureRegularity
#print axioms VacuumCrossing
#print axioms VacuumNondegeneracy
#print axioms eventually_twistSeparation_of_vacuum
#print axioms CofinalVacuumNondegeneracy
#print axioms cofinalTwistSeparation_of_cofinalVacuum
#print axioms goalNeg2_of_cofinalVacuum
#print axioms not_cofinalVacuum_of_goalPos1
#print axioms extP
#print axioms extA
#print axioms extD
#print axioms ExtSeparation
#print axioms CofinalExtSeparation
#print axioms goalNeg2_of_cofinalExtSeparation
#print axioms not_cofinalExtSeparation_of_goalPos1
#print axioms extSeparation_of_twistSeparation
#print axioms cofinalExtSeparation_of_cofinalTwistSeparation
#print axioms dilU_agree
#print axioms extD_congr
#print axioms extPath_cont
#print axioms extA_continuous
#print axioms PathRegularity
#print axioms PathCrossing
#print axioms PathVacuumNondegeneracy
#print axioms eventually_extSeparation_of_pathVacuum
#print axioms CofinalPathVacuum
#print axioms cofinalExtSeparation_of_cofinalPathVacuum
#print axioms goalNeg2_of_cofinalPathVacuum
#print axioms not_cofinalPathVacuum_of_goalPos1
#print axioms leftTwist
#print axioms leftTwist_cont
#print axioms CofinalLeftVacuum
#print axioms goalNeg2_of_cofinalLeftVacuum
#print axioms LeftSoft
#print axioms LeftSpectral
#print axioms cofinalLeftVacuum_of_soft_spectral
#print axioms goalNeg2_of_leftSoft_leftSpectral

end AdalyFormal.Round9.Guarded.AnalyticR1
