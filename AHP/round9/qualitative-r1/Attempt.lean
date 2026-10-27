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
Round 9, qualitative route: first-order separation at fixed scale and radius, with a free
exterior path and a free interior profile.

At zero curvature the localized correction vanishes, so for small curvature a corrected
crossing can only split off a vacuum crossing.  Two abstract theorems turn zero-curvature
data into a separation at EVERY small positive curvature:
* `first_order_separation`: the vacuum carrier is positive definite just before a crossing
  angle and has a negative direction just after it, the carrier is jointly continuous at
  zero curvature, and the first-order correction is positive definite on the vacuum
  kernel (no angle derivative, no gap constant, no scalar action; pre-crossing sign);
* `perturbative_sign_change`: both signs, under joint differentiability and a scalar
  action on the kernel.
The concrete part allows any continuous exterior path and any bounded interior profile
(round 5 `maskedU`).  Reflecting the profile reflects the curvature, so a coupling of
either sign gives a pre-crossing separation for the profile or for its reflection.  The
remaining premise `CofinalVacuumCoupling` is a statement about zero curvature plus soft
regularity.

Nothing here proves a pinned goal.  The family premises are explicit, unproved
hypotheses on the actual operators; the abstract lemmas are finite-dimensional facts.
-/
namespace AdalyFormal.Round9.Guarded.Qualitative

open scoped RealInnerProductSpace
open AdalyFormal.D1Literal (PSD psd_kernel psd_coercive)
open AdalyFormal.Round8.Guarded.SignFree (unit_of_definite_complements)
open AdalyFormal.Round5.Guarded.IVTR2 (first_carrier_crossing)

section Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem abs_inner_op_le (N : E →L[ℝ] E) (u y : E) : |⟪u, N y⟫| ≤ ‖N‖ * ‖u‖ * ‖y‖ := by
  calc |⟪u, N y⟫| ≤ ‖u‖ * ‖N y‖ := abs_real_inner_le_norm u (N y)
    _ ≤ ‖u‖ * (‖N‖ * ‖y‖) := mul_le_mul_of_nonneg_left (N.le_opNorm y) (norm_nonneg u)
    _ = ‖N‖ * ‖u‖ * ‖y‖ := by ring

/-- Two-block positivity with respect to `E = K ⊕ Kᗮ`: a definite `K`-block, a
definite `Kᗮ`-block and a small off-diagonal block give a positive definite form. -/
theorem block_pos (X : E →L[ℝ] E) (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (K : Submodule ℝ E)
    {a g b : ℝ} (ha : 0 < a) (hab : b ^ 2 < a * g)
    (hK : ∀ u ∈ K, a * ‖u‖ ^ 2 ≤ ⟪u, X u⟫)
    (hKp : ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, X y⟫)
    (hX : ∀ u ∈ K, ∀ y ∈ Kᗮ, |⟪u, X y⟫| ≤ b * ‖u‖ * ‖y‖) :
    ∀ x : E, x ≠ 0 → 0 < ⟪x, X x⟫ := by
  intro x hx
  obtain ⟨u, hu, y, hy, rfl⟩ := K.exists_add_mem_mem_orthogonal x
  have hsym : ⟪y, X u⟫ = ⟪u, X y⟫ := by rw [← hs y u, real_inner_comm]
  have hexp : ⟪u + y, X (u + y)⟫ = ⟪u, X u⟫ + 2 * ⟪u, X y⟫ + ⟪y, X y⟫ := by
    simp only [map_add, inner_add_left, inner_add_right]
    rw [hsym]; ring
  rw [hexp]
  have h1 := hK u hu
  have h2 := hKp y hy
  have h3 : -(b * ‖u‖ * ‖y‖) ≤ ⟪u, X y⟫ := (abs_le.mp (hX u hu y hy)).1
  have hr0 : 0 ≤ ‖y‖ := norm_nonneg _
  have key : 0 < a * ‖u‖ ^ 2 - 2 * (b * ‖u‖ * ‖y‖) + g * ‖y‖ ^ 2 := by
    have hQ : a * (a * ‖u‖ ^ 2 - 2 * (b * ‖u‖ * ‖y‖) + g * ‖y‖ ^ 2) =
        (a * ‖u‖ - b * ‖y‖) ^ 2 + (a * g - b ^ 2) * ‖y‖ ^ 2 := by ring
    rcases hr0.lt_or_eq with hr | hr
    · have hpos : 0 < (a * g - b ^ 2) * ‖y‖ ^ 2 := mul_pos (by linarith) (pow_pos hr 2)
      have hm : 0 < a * (a * ‖u‖ ^ 2 - 2 * (b * ‖u‖ * ‖y‖) + g * ‖y‖ ^ 2) := by
        rw [hQ]; linarith [sq_nonneg (a * ‖u‖ - b * ‖y‖)]
      by_contra hcon
      have hcon' := not_lt.mp hcon
      have := mul_le_mul_of_nonneg_left hcon' ha.le
      linarith
    · have hy0 : y = 0 := norm_eq_zero.mp hr.symm
      have hu0 : u ≠ 0 := by
        intro hu0
        apply hx
        rw [hu0, hy0, add_zero]
      have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      rw [← hr]
      have : 0 < a * ‖u‖ ^ 2 := mul_pos ha (pow_pos hun 2)
      linarith
  linarith

omit [FiniteDimensional ℝ E] in
/-- The quadratic form of `A0 + τ At + ε B + R` on a kernel vector of `A0` on which
`At` and `B` act as scalars. -/
theorem kernel_form (A0 At B R : E →L[ℝ] E) (τ ε σ β : ℝ) (u : E) (h0 : A0 u = 0)
    (ht : ⟪u, At u⟫ = σ * ‖u‖ ^ 2) (hb : ⟪u, B u⟫ = β * ‖u‖ ^ 2) :
    ⟪u, (A0 + τ • At + ε • B + R) u⟫ = (σ * τ + ε * β) * ‖u‖ ^ 2 + ⟪u, R u⟫ := by
  simp only [add_apply, smul_apply, inner_add_right,
    real_inner_smul_right, h0, inner_zero_right, ht, hb]
  ring

omit [FiniteDimensional ℝ E] in
theorem expansion_dist (A0 At B R : E →L[ℝ] E) (τ ε : ℝ) :
    ‖(A0 + τ • At + ε • B + R) - A0‖ ≤ |τ| * ‖At‖ + |ε| * ‖B‖ + ‖R‖ := by
  have h : (A0 + τ • At + ε • B + R) - A0 = τ • At + ε • B + R := by abel
  rw [h]
  calc ‖τ • At + ε • B + R‖ ≤ ‖τ • At + ε • B‖ + ‖R‖ := norm_add_le _ _
    _ ≤ ‖τ • At‖ + ‖ε • B‖ + ‖R‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = |τ| * ‖At‖ + |ε| * ‖B‖ + ‖R‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]

omit [FiniteDimensional ℝ E] in
theorem perp_lower (A0 X : E →L[ℝ] E) (K : Submodule ℝ E) {g δ : ℝ}
    (hgap : ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, A0 y⟫) (hδ : ‖X - A0‖ ≤ δ) :
    ∀ y ∈ Kᗮ, (g - δ) * ‖y‖ ^ 2 ≤ ⟪y, X y⟫ := by
  intro y hy
  have h1 := hgap y hy
  have h2 := (abs_le.mp (abs_inner_op_le (X - A0) y y)).1
  have h3 : ⟪y, X y⟫ = ⟪y, A0 y⟫ + ⟪y, (X - A0) y⟫ := by
    simp only [sub_apply, inner_sub_right]; ring
  have h4 : ‖X - A0‖ * ‖y‖ * ‖y‖ ≤ δ * ‖y‖ ^ 2 := by
    have hy0 : 0 ≤ ‖y‖ * ‖y‖ := mul_nonneg (norm_nonneg y) (norm_nonneg y)
    calc ‖X - A0‖ * ‖y‖ * ‖y‖ = ‖X - A0‖ * (‖y‖ * ‖y‖) := by ring
      _ ≤ δ * (‖y‖ * ‖y‖) := mul_le_mul_of_nonneg_right hδ hy0
      _ = δ * ‖y‖ ^ 2 := by ring
  rw [h3]
  linarith

omit [FiniteDimensional ℝ E] in
theorem cross_upper (A0 X : E →L[ℝ] E) (hs0 : ∀ x y, ⟪A0 x, y⟫ = ⟪x, A0 y⟫)
    (K : Submodule ℝ E) (hker : ∀ u ∈ K, A0 u = 0) {δ : ℝ} (hδ : ‖X - A0‖ ≤ δ) :
    ∀ u ∈ K, ∀ y : E, |⟪u, X y⟫| ≤ δ * ‖u‖ * ‖y‖ := by
  intro u hu y
  have h0 : ⟪u, A0 y⟫ = 0 := by rw [← hs0, hker u hu, inner_zero_left]
  have h3 : ⟪u, X y⟫ = ⟪u, (X - A0) y⟫ := by
    simp only [sub_apply, inner_sub_right, h0, sub_zero]
  rw [h3]
  have huy : 0 ≤ ‖u‖ * ‖y‖ := mul_nonneg (norm_nonneg u) (norm_nonneg y)
  calc |⟪u, (X - A0) y⟫| ≤ ‖X - A0‖ * ‖u‖ * ‖y‖ := abs_inner_op_le _ _ _
    _ = ‖X - A0‖ * (‖u‖ * ‖y‖) := by ring
    _ ≤ δ * (‖u‖ * ‖y‖) := mul_le_mul_of_nonneg_right hδ huy
    _ = δ * ‖u‖ * ‖y‖ := by ring

omit [FiniteDimensional ℝ E] in
/-- First-order bookkeeping: if `X = A0 + τ At + ε B + R` with `‖R‖ ≤ ρ`, then on the
kernel `K` of `A0` (where `At`, `B` act as scalars) the form of `X` is its first-order
value up to `ρ`, and `X` is within `|τ|‖At‖ + |ε|‖B‖ + ρ` of `A0`. -/
theorem kernel_form_bounds (A0 At B X : E →L[ℝ] E) (K : Submodule ℝ E)
    (hker : ∀ u ∈ K, A0 u = 0) {σ β τ ε ρ : ℝ}
    (ht : ∀ u ∈ K, ⟪u, At u⟫ = σ * ‖u‖ ^ 2) (hb : ∀ u ∈ K, ⟪u, B u⟫ = β * ‖u‖ ^ 2)
    (hR : ‖X - A0 - τ • At - ε • B‖ ≤ ρ) :
    (∀ u ∈ K, |⟪u, X u⟫ - (σ * τ + ε * β) * ‖u‖ ^ 2| ≤ ρ * ‖u‖ ^ 2) ∧
      ‖X - A0‖ ≤ |τ| * ‖At‖ + |ε| * ‖B‖ + ρ := by
  obtain ⟨R, hR_def⟩ : ∃ R : E →L[ℝ] E, R = X - A0 - τ • At - ε • B := ⟨_, rfl⟩
  have hRn : ‖R‖ ≤ ρ := by rw [hR_def]; exact hR
  have hX : X = A0 + τ • At + ε • B + R := by rw [hR_def]; abel
  constructor
  · intro u hu
    rw [hX, kernel_form A0 At B R τ ε σ β u (hker u hu) (ht u hu) (hb u hu)]
    have h1 := abs_inner_op_le R u u
    have h2 : ‖R‖ * ‖u‖ * ‖u‖ ≤ ρ * ‖u‖ ^ 2 := by
      have hu0 : 0 ≤ ‖u‖ * ‖u‖ := mul_nonneg (norm_nonneg u) (norm_nonneg u)
      calc ‖R‖ * ‖u‖ * ‖u‖ = ‖R‖ * (‖u‖ * ‖u‖) := by ring
        _ ≤ ρ * (‖u‖ * ‖u‖) := mul_le_mul_of_nonneg_right hRn hu0
        _ = ρ * ‖u‖ ^ 2 := by ring
    have h3 : (σ * τ + ε * β) * ‖u‖ ^ 2 + ⟪u, R u⟫ - (σ * τ + ε * β) * ‖u‖ ^ 2 = ⟪u, R u⟫ := by
      ring
    rw [h3]
    exact le_trans h1 h2
  · rw [hX]
    exact le_trans (expansion_dist A0 At B R τ ε) (by linarith)

/-- **Perturbative sign-free separation.**  `A ε t` is a symmetric two-parameter
family, `D ε` a symmetric correction.  At `ε = 0` and `t = ts` the carrier `A 0 ts`
vanishes on a nonzero subspace `K` and is bounded below by `g > 0` on `Kᗮ` (so `A 0 ts`
is positive semidefinite and `ts` is a first crossing).  Suppose `(ε,t) ↦ A ε t` and
`ε ↦ D ε` are differentiable at `(0,ts)` and `0` in the first-order sense of `hAexp` and
`hDexp` (in particular `D 0 = 0`), with derivatives `At`, `Ae`, `De` acting on `K` as the
scalars `σ < 0`, `α`, `c`.  If `c ≠ 0` then for every sufficiently small `ε > 0` there is
an interval `[t₀,t₁]` of carrier units on which `A ε · - D ε` passes from positive
semidefinite to a negative direction.  For `c > 0` the carrier is positive definite on
the interval (pre-crossing), for `c < 0` it is an indefinite unit (post-crossing).
Only `c ≠ 0` enters, never its value. -/
theorem perturbative_sign_change
    (A : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E)
    (hsA : ∀ ε t x y, ⟪A ε t x, y⟫ = ⟪x, A ε t y⟫)
    (hsD : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (ts : ℝ) (K : Submodule ℝ E) (g σ α c : ℝ) (At Ae De : E →L[ℝ] E)
    (hker : ∀ u ∈ K, A 0 ts u = 0)
    (hg : 0 < g) (hgap : ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, A 0 ts y⟫)
    (hne : ∃ u ∈ K, u ≠ 0)
    (hσ : σ < 0) (hc : c ≠ 0)
    (hAt : ∀ u ∈ K, ⟪u, At u⟫ = σ * ‖u‖ ^ 2)
    (hAe : ∀ u ∈ K, ⟪u, Ae u⟫ = α * ‖u‖ ^ 2)
    (hDe : ∀ u ∈ K, ⟪u, De u⟫ = c * ‖u‖ ^ 2)
    (hAexp : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ ε τ : ℝ, |ε| < r → |τ| < r →
      ‖A ε (ts + τ) - A 0 ts - τ • At - ε • Ae‖ ≤ η * (|ε| + |τ|))
    (hDexp : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, |ε| < r →
      ‖D ε - ε • De‖ ≤ η * |ε|) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ t₀ t₁ : ℝ, t₀ ≤ t₁ ∧ (∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (A ε t)) ∧
        PSD (A ε t₀ - D ε) ∧ ∃ w : E, ⟪w, (A ε t₁ - D ε) w⟫ < 0 := by
  have hs0 : ∀ x y, ⟪A 0 ts x, y⟫ = ⟪x, A 0 ts y⟫ := hsA 0 ts
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = -σ := ⟨_, rfl⟩
  have hs : 0 < s := by linarith
  have hσs : |σ| = s := by rw [abs_of_neg hσ, hs_def]
  have hcabs : 0 < |c| := abs_pos.mpr hc
  obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = |c| / (3 * s) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ_def]; exact div_pos hcabs (by linarith)
  have hsκ : s * κ = |c| / 3 := by
    rw [hκ_def, mul_div_assoc', div_eq_div_iff (mul_pos (by norm_num) hs).ne' (by norm_num)]
    ring
  obtain ⟨Λ, hΛ_def⟩ : ∃ Λ : ℝ, Λ = |α - c| / s + κ := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ_def]; exact add_nonneg (div_nonneg (abs_nonneg _) hs.le) hκ0.le
  obtain ⟨η₁, hη₁_def⟩ : ∃ η : ℝ, η = |c| / (24 * (1 + Λ)) := ⟨_, rfl⟩
  have hη₁0 : 0 < η₁ := by rw [hη₁_def]; exact div_pos hcabs (by linarith)
  have hη₁Λ : η₁ * (1 + Λ) = |c| / 24 := by
    rw [hη₁_def, div_mul_eq_mul_div,
      div_eq_div_iff (mul_pos (by norm_num) (by linarith : (0 : ℝ) < 1 + Λ)).ne' (by norm_num)]
    ring
  have hη₂0 : (0 : ℝ) < |c| / 24 := div_pos hcabs (by norm_num)
  obtain ⟨r₁, hr₁, hA1⟩ := hAexp η₁ hη₁0
  obtain ⟨r₂, hr₂, hD1⟩ := hDexp (|c| / 24) hη₂0
  obtain ⟨C, hC_def⟩ : ∃ C : ℝ, C = Λ * ‖At‖ + ‖Ae‖ + ‖De‖ + |c| / 12 := ⟨_, rfl⟩
  have hC0 : 0 < C := by
    have h1 := mul_nonneg hΛ0 (norm_nonneg At)
    have h2 := norm_nonneg Ae
    have h3 := norm_nonneg De
    have h4 : 0 < |c| / 12 := div_pos hcabs (by norm_num)
    rw [hC_def]; linarith
  have h1Λ : (0 : ℝ) < 1 + Λ := by linarith
  have h2C : (0 : ℝ) < 2 * C := by linarith
  have h16C : (0 : ℝ) < 16 * C ^ 2 := mul_pos (by norm_num) (pow_pos hC0 2)
  have hr₁' : 0 < r₁ / (1 + Λ) := div_pos hr₁ h1Λ
  have hgC : 0 < g / (2 * C) := div_pos hg h2C
  have hcgC : 0 < |c| * g / (16 * C ^ 2) := div_pos (mul_pos hcabs hg) h16C
  refine ⟨min (min (r₁ / (1 + Λ)) r₂) (min (g / (2 * C)) (|c| * g / (16 * C ^ 2))),
    lt_min (lt_min hr₁' hr₂) (lt_min hgC hcgC), ?_⟩
  intro ε hε hε₀
  have hε1 : ε < r₁ / (1 + Λ) :=
    lt_of_lt_of_le hε₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε2 : ε < r₂ := lt_of_lt_of_le hε₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε3 : ε < g / (2 * C) :=
    lt_of_lt_of_le hε₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε4 : ε < |c| * g / (16 * C ^ 2) :=
    lt_of_lt_of_le hε₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hεr₁ : ε * (1 + Λ) < r₁ := (lt_div_iff₀ h1Λ).mp hε1
  have hεC : ε * C < g / 2 := by
    have h := (lt_div_iff₀ h2C).mp hε3
    linarith
  have hεC2 : ε * C ^ 2 * 16 < |c| * g := by
    have h := (lt_div_iff₀ h16C).mp hε4
    linarith
  have hεabs : |ε| = ε := abs_of_pos hε
  obtain ⟨τC, hτC_def⟩ : ∃ τ : ℝ, τ = ε * (α - c) / s := ⟨_, rfl⟩
  have hστC : σ * τC = -(ε * (α - c)) := by
    rw [hτC_def, mul_div_assoc', div_eq_iff hs.ne', hs_def]; ring
  have hτCabs : |τC| = ε * (|α - c| / s) := by
    rw [hτC_def, abs_div, abs_mul, abs_of_pos hε, abs_of_pos hs]; ring
  have hDn : ‖D ε - ε • De‖ ≤ ε * |c| / 24 := by
    have h := hD1 ε (by rw [hεabs]; exact hε2)
    rw [hεabs] at h
    linarith
  -- every angle in the window `|t - ts - τC| ≤ ε κ`
  have window : ∀ t : ℝ, |t - ts - τC| ≤ ε * κ →
      ‖A ε t - A 0 ts‖ ≤ ε * C ∧ ‖(A ε t - D ε) - A 0 ts‖ ≤ ε * C ∧
      (∀ u ∈ K, |⟪u, A ε t u⟫ - (ε * c + σ * (t - ts - τC)) * ‖u‖ ^ 2| ≤
        ε * |c| / 24 * ‖u‖ ^ 2) ∧
      (∀ u ∈ K, |⟪u, (A ε t - D ε) u⟫ - σ * (t - ts - τC) * ‖u‖ ^ 2| ≤
        ε * |c| / 12 * ‖u‖ ^ 2) := by
    intro t ht
    obtain ⟨τ, hτ_def⟩ : ∃ τ : ℝ, τ = t - ts := ⟨_, rfl⟩
    have hτ : |τ| ≤ ε * Λ := by
      have h1 : τ = τC + (t - ts - τC) := by rw [hτ_def]; ring
      calc |τ| = |τC + (t - ts - τC)| := by rw [h1]
        _ ≤ |τC| + |t - ts - τC| := abs_add_le _ _
        _ ≤ ε * (|α - c| / s) + ε * κ := by rw [hτCabs]; linarith
        _ = ε * Λ := by rw [hΛ_def]; ring
    have hεΛ : 0 ≤ ε * Λ := mul_nonneg hε.le hΛ0
    have hτr : |τ| < r₁ := by linarith
    have hεr : |ε| < r₁ := by rw [hεabs]; linarith
    have hA := hA1 ε τ hεr hτr
    have hts : ts + τ = t := by rw [hτ_def]; ring
    rw [hts] at hA
    have hAn : ‖A ε t - A 0 ts - τ • At - ε • Ae‖ ≤ ε * |c| / 24 := by
      calc ‖A ε t - A 0 ts - τ • At - ε • Ae‖ ≤ η₁ * (|ε| + |τ|) := hA
        _ ≤ η₁ * (ε + ε * Λ) :=
          mul_le_mul_of_nonneg_left (by rw [hεabs]; linarith) hη₁0.le
        _ = ε * (η₁ * (1 + Λ)) := by ring
        _ = ε * |c| / 24 := by rw [hη₁Λ]; ring
    have hRD : ‖(A ε t - D ε) - A 0 ts - τ • At - ε • (Ae - De)‖ ≤ ε * |c| / 12 := by
      have h : (A ε t - D ε) - A 0 ts - τ • At - ε • (Ae - De) =
          (A ε t - A 0 ts - τ • At - ε • Ae) - (D ε - ε • De) := by
        rw [smul_sub]; abel
      rw [h]
      calc ‖(A ε t - A 0 ts - τ • At - ε • Ae) - (D ε - ε • De)‖
          ≤ ‖A ε t - A 0 ts - τ • At - ε • Ae‖ + ‖D ε - ε • De‖ := norm_sub_le _ _
        _ ≤ ε * |c| / 24 + ε * |c| / 24 := add_le_add hAn hDn
        _ = ε * |c| / 12 := by ring
    have hADe : ∀ u ∈ K, ⟪u, (Ae - De) u⟫ = (α - c) * ‖u‖ ^ 2 := by
      intro u hu
      simp only [sub_apply, inner_sub_right, hAe u hu, hDe u hu]
      ring
    obtain ⟨hKA, hdA⟩ := kernel_form_bounds (A 0 ts) At Ae (A ε t) K hker hAt hAe hAn
    obtain ⟨hKD, hdD⟩ :=
      kernel_form_bounds (A 0 ts) At (Ae - De) (A ε t - D ε) K hker hAt hADe hRD
    have hτAt : |τ| * ‖At‖ ≤ ε * Λ * ‖At‖ := mul_le_mul_of_nonneg_right hτ (norm_nonneg _)
    have hεDe : 0 ≤ ε * ‖De‖ := mul_nonneg hε.le (norm_nonneg _)
    have hεc : 0 ≤ ε * |c| := mul_nonneg hε.le (abs_nonneg _)
    have hsub : ‖Ae - De‖ ≤ ‖Ae‖ + ‖De‖ := norm_sub_le _ _
    have hεsub : ε * ‖Ae - De‖ ≤ ε * (‖Ae‖ + ‖De‖) := mul_le_mul_of_nonneg_left hsub hε.le
    have hστ1 : σ * τ + ε * α = ε * c + σ * (t - ts - τC) := by
      rw [hτ_def]; linarith
    have hστ2 : σ * τ + ε * (α - c) = σ * (t - ts - τC) := by
      rw [hτ_def]; linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc ‖A ε t - A 0 ts‖ ≤ |τ| * ‖At‖ + |ε| * ‖Ae‖ + ε * |c| / 24 := hdA
        _ ≤ ε * C := by rw [hεabs, hC_def]; linarith
    · calc ‖(A ε t - D ε) - A 0 ts‖ ≤ |τ| * ‖At‖ + |ε| * ‖Ae - De‖ + ε * |c| / 12 := hdD
        _ ≤ ε * C := by rw [hεabs, hC_def]; linarith
    · intro u hu
      have h := hKA u hu
      rw [hστ1] at h
      exact h
    · intro u hu
      have h := hKD u hu
      rw [hστ2] at h
      exact h
  have hσw : ∀ t : ℝ, |t - ts - τC| ≤ ε * κ → |σ * (t - ts - τC)| ≤ ε * |c| / 3 := by
    intro t ht
    rw [abs_mul, hσs]
    calc s * |t - ts - τC| ≤ s * (ε * κ) := mul_le_mul_of_nonneg_left ht hs.le
      _ = ε * (s * κ) := by ring
      _ = ε * |c| / 3 := by rw [hsκ]; ring
  obtain ⟨u₀, hu₀K, hu₀⟩ := hne
  have hεκ : 0 < ε * κ := mul_pos hε hκ0
  refine ⟨ts + τC - ε * κ, ts + τC + ε * κ, by linarith, ?_, ?_, ?_⟩
  · -- the interval guard
    intro t ht0 ht1
    have hw : |t - ts - τC| ≤ ε * κ := abs_le.mpr ⟨by linarith, by linarith⟩
    obtain ⟨hdA, -, hKA, -⟩ := window t hw
    have hδ := abs_le.mp (hσw t hw)
    have hperp := perp_lower (A 0 ts) (A ε t) K hgap hdA
    rcases lt_or_gt_of_ne hc with hcneg | hcpos
    · -- post-crossing: negative definite on `K`, positive definite on `Kᗮ`
      have hca : |c| = -c := abs_of_neg hcneg
      apply unit_of_definite_complements (A ε t) (hsA ε t) K Kᗮ
      · intro u hu hu0
        have h := (abs_le.mp (hKA u hu)).2
        have hun : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu0) 2
        rw [hca] at h hδ
        have hm := mul_le_mul_of_nonneg_right hδ.2 hun.le
        have hp : 0 < ε * (-c) * ‖u‖ ^ 2 := mul_pos (mul_pos hε (by linarith)) hun
        linarith
      · intro y hy hy0
        have h := hperp y hy
        have hyn : 0 < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hy0) 2
        have hg2 : 0 < g - ε * C := by linarith
        have := mul_pos hg2 hyn
        linarith
      · exact (Submodule.finrank_add_finrank_orthogonal K).ge
    · -- pre-crossing: positive definite
      have hca : |c| = c := abs_of_pos hcpos
      have hpd : ∀ x : E, x ≠ 0 → 0 < ⟪x, A ε t x⟫ := by
        refine block_pos (A ε t) (hsA ε t) K (a := ε * c / 2) (g := g / 2) (b := ε * C)
          (by have := mul_pos hε hcpos; linarith) ?_ ?_ ?_ ?_
        · rw [hca] at hεC2
          have h3 : ε * (ε * C ^ 2 * 16) < ε * (c * g) := mul_lt_mul_of_pos_left hεC2 hε
          have hpos : 0 < ε * (c * g) := mul_pos hε (mul_pos hcpos hg)
          linarith
        · intro u hu
          have h := (abs_le.mp (hKA u hu)).1
          rw [hca] at h hδ
          have hun : 0 ≤ ‖u‖ ^ 2 := pow_nonneg (norm_nonneg u) 2
          have hm := mul_le_mul_of_nonneg_right hδ.1 hun
          have hp : 0 ≤ ε * c * ‖u‖ ^ 2 := mul_nonneg (mul_nonneg hε.le hcpos.le) hun
          linarith
        · intro y hy
          have h := hperp y hy
          have hyn : 0 ≤ ‖y‖ ^ 2 := pow_nonneg (norm_nonneg y) 2
          have : (g / 2) * ‖y‖ ^ 2 ≤ (g - ε * C) * ‖y‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (by linarith) hyn
          linarith
        · intro u hu y _
          exact cross_upper (A 0 ts) (A ε t) hs0 K hker hdA u hu y
      refine unit_of_definite_complements (A ε t) (hsA ε t) ⊥ ⊤ ?_
        (fun x _ hx0 => hpd x hx0) ?_
      · intro x hx hx0
        exact absurd ((Submodule.mem_bot ℝ).mp hx) hx0
      · simp
  · -- the corrected carrier is positive semidefinite at `t₀`
    have hw : |ts + τC - ε * κ - ts - τC| ≤ ε * κ := le_of_eq (by
      rw [show ts + τC - ε * κ - ts - τC = -(ε * κ) by ring, abs_neg, abs_of_pos hεκ])
    obtain ⟨-, hdD, -, hKD⟩ := window _ hw
    have hval : σ * (ts + τC - ε * κ - ts - τC) = ε * |c| / 3 := by
      have h : σ * (ts + τC - ε * κ - ts - τC) = ε * (s * κ) := by rw [hs_def]; ring
      rw [h, hsκ]; ring
    have hperp := perp_lower (A 0 ts) (A ε (ts + τC - ε * κ) - D ε) K hgap hdD
    have hsM : ∀ x y, ⟪(A ε (ts + τC - ε * κ) - D ε) x, y⟫ =
        ⟪x, (A ε (ts + τC - ε * κ) - D ε) y⟫ := by
      intro x y
      simp only [sub_apply, inner_sub_left, inner_sub_right, hsA, hsD]
    have hpd : ∀ x : E, x ≠ 0 → 0 < ⟪x, (A ε (ts + τC - ε * κ) - D ε) x⟫ := by
      refine block_pos _ hsM K (a := ε * |c| / 4) (g := g / 2) (b := ε * C)
        (by have := mul_pos hε hcabs; linarith) ?_ ?_ ?_ ?_
      · have h3 : ε * (ε * C ^ 2 * 16) < ε * (|c| * g) := mul_lt_mul_of_pos_left hεC2 hε
        have hpos : 0 < ε * (|c| * g) := mul_pos hε (mul_pos hcabs hg)
        linarith
      · intro u hu
        have h := (abs_le.mp (hKD u hu)).1
        rw [hval] at h
        have hun : 0 ≤ ‖u‖ ^ 2 := pow_nonneg (norm_nonneg u) 2
        linarith
      · intro y hy
        have h := hperp y hy
        have hyn : 0 ≤ ‖y‖ ^ 2 := pow_nonneg (norm_nonneg y) 2
        have : (g / 2) * ‖y‖ ^ 2 ≤ (g - ε * C) * ‖y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) hyn
        linarith
      · intro u hu y _
        exact cross_upper (A 0 ts) _ hs0 K hker hdD u hu y
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hpd v hv).le
  · -- a negative direction of the corrected carrier at `t₁`
    have hw : |ts + τC + ε * κ - ts - τC| ≤ ε * κ := le_of_eq (by
      rw [show ts + τC + ε * κ - ts - τC = ε * κ by ring, abs_of_pos hεκ])
    obtain ⟨-, -, -, hKD⟩ := window _ hw
    have hval : σ * (ts + τC + ε * κ - ts - τC) = -(ε * |c| / 3) := by
      have h : σ * (ts + τC + ε * κ - ts - τC) = -(ε * (s * κ)) := by rw [hs_def]; ring
      rw [h, hsκ]; ring
    refine ⟨u₀, ?_⟩
    have h := (abs_le.mp (hKD u₀ hu₀K)).2
    rw [hval] at h
    have hun : 0 < ‖u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu₀) 2
    have hp : 0 < ε * |c| * ‖u₀‖ ^ 2 := mul_pos (mul_pos hε hcabs) hun
    linarith

omit [FiniteDimensional ℝ E] in
/-- A symmetric operator commuting with an orthogonal map `J` acts as a scalar on the
plane spanned by `u₀` and `J u₀` whenever `J (J u₀) = -u₀` (a complex line of a `U(1)`
symmetry).  This is how the scalar hypotheses of `perturbative_sign_change` arise from
the diagonal `U(1)` symmetry of the curved twist family. -/
theorem scalar_on_complex_line (M J : E →L[ℝ] E) (hM : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫)
    (hJ : ∀ x y, ⟪J x, J y⟫ = ⟪x, y⟫) (hMJ : ∀ x, M (J x) = J (M x))
    (u₀ : E) (hu₀ : u₀ ≠ 0) (hJJ : J (J u₀) = -u₀) :
    ∃ l : ℝ, ∀ u ∈ Submodule.span ℝ {u₀, J u₀}, ⟪u, M u⟫ = l * ‖u‖ ^ 2 := by
  have h01' : ⟪u₀, J u₀⟫ = -⟪u₀, J u₀⟫ := by
    calc ⟪u₀, J u₀⟫ = ⟪J u₀, J (J u₀)⟫ := (hJ _ _).symm
      _ = ⟪J u₀, -u₀⟫ := by rw [hJJ]
      _ = -⟪J u₀, u₀⟫ := inner_neg_right _ _
      _ = -⟪u₀, J u₀⟫ := by rw [real_inner_comm u₀ (J u₀)]
  have h01 : ⟪u₀, J u₀⟫ = 0 := by linarith
  have h10 : ⟪J u₀, u₀⟫ = 0 := by rw [real_inner_comm]; exact h01
  have hJn : ⟪J u₀, J u₀⟫ = ⟪u₀, u₀⟫ := hJ u₀ u₀
  have e1 : ⟪J u₀, M u₀⟫ = ⟪u₀, M (J u₀)⟫ :=
    (hM (J u₀) u₀).symm.trans (real_inner_comm u₀ (M (J u₀)))
  have h1 : ⟪u₀, M (J u₀)⟫ = -⟪u₀, M (J u₀)⟫ := by
    calc ⟪u₀, M (J u₀)⟫ = ⟪J u₀, J (M (J u₀))⟫ := (hJ _ _).symm
      _ = ⟪J u₀, M (J (J u₀))⟫ := by rw [hMJ (J u₀)]
      _ = ⟪J u₀, M (-u₀)⟫ := by rw [hJJ]
      _ = -⟪J u₀, M u₀⟫ := by rw [map_neg, inner_neg_right]
      _ = -⟪u₀, M (J u₀)⟫ := by rw [e1]
  have hc1 : ⟪u₀, M (J u₀)⟫ = 0 := by linarith
  have hc2 : ⟪J u₀, M u₀⟫ = 0 := by rw [e1]; exact hc1
  have hd : ⟪J u₀, M (J u₀)⟫ = ⟪u₀, M u₀⟫ := by rw [hMJ u₀]; exact hJ _ _
  have hn : 0 < ‖u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu₀) 2
  refine ⟨⟪u₀, M u₀⟫ / ‖u₀‖ ^ 2, fun u hu => ?_⟩
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  have hform : ⟪a • u₀ + b • J u₀, M (a • u₀ + b • J u₀)⟫ =
      (a ^ 2 + b ^ 2) * ⟪u₀, M u₀⟫ := by
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hc1, hc2, hd]
    ring
  have hnorm : ‖a • u₀ + b • J u₀‖ ^ 2 = (a ^ 2 + b ^ 2) * ‖u₀‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hJn, h01, h10]
    ring
  rw [hform, hnorm, div_mul_eq_mul_div, eq_div_iff hn.ne']
  ring

/-- First-order expansion from joint Fréchet differentiability at `(0, ts)`. -/
theorem expansion_of_hasFDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → ℝ → F) (ts : ℝ) (Fe Ft : F)
    (h : HasFDerivAt (fun p : ℝ × ℝ => f p.1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Fe +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Ft) ((0 : ℝ), ts)) :
    ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ ε τ : ℝ, |ε| < r → |τ| < r →
      ‖f ε (ts + τ) - f 0 ts - τ • Ft - ε • Fe‖ ≤ η * (|ε| + |τ|) := by
  intro η hη
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp h
  rw [Asymptotics.isLittleO_iff] at hlo
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hlo hη)
  refine ⟨r, hr, fun ε τ hε hτ => ?_⟩
  have hd : dist ((ε, τ) : ℝ × ℝ) 0 < r := by
    rw [Prod.dist_eq]
    simp only [Prod.fst_zero, Prod.snd_zero, Real.dist_eq, sub_zero]
    exact max_lt hε hτ
  have heq : f ε (ts + τ) - f 0 ts - τ • Ft - ε • Fe =
      (fun p : ℝ × ℝ => f p.1 p.2) (((0 : ℝ), ts) + (ε, τ)) -
      (fun p : ℝ × ℝ => f p.1 p.2) ((0 : ℝ), ts) -
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Fe +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Ft) (ε, τ) := by
    simp only [Prod.mk_add_mk, zero_add, add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
    abel
  have hn : ‖((ε, τ) : ℝ × ℝ)‖ ≤ |ε| + |τ| := by
    rw [Prod.norm_def]
    simp only [Real.norm_eq_abs]
    exact max_le (by linarith [abs_nonneg τ]) (by linarith [abs_nonneg ε])
  rw [heq]
  calc _ ≤ η * ‖((ε, τ) : ℝ × ℝ)‖ := hball hd
    _ ≤ η * (|ε| + |τ|) := mul_le_mul_of_nonneg_left hn hη.le

/-- First-order expansion from differentiability at `0`, for a map vanishing at `0`. -/
theorem expansion_of_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (Fe : F) (h0 : f 0 = 0) (h : HasDerivAt f Fe 0) :
    ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, |ε| < r → ‖f ε - ε • Fe‖ ≤ η * |ε| := by
  intro η hη
  have hlo := hasDerivAt_iff_isLittleO_nhds_zero.mp h
  rw [Asymptotics.isLittleO_iff] at hlo
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hlo hη)
  refine ⟨r, hr, fun ε hε => ?_⟩
  have hd : dist ε 0 < r := by rw [Real.dist_eq, sub_zero]; exact hε
  have hb := hball hd
  simp only [zero_add, h0, sub_zero, Real.norm_eq_abs] at hb
  exact hb

/-! ### Pre-crossing separation from first-order data, without derivatives in the angle

The theorem `first_order_separation` below needs, at zero curvature, only that the
carrier is positive definite at angles arbitrarily close before a crossing angle `ts`
and has a negative direction at angles arbitrarily close after it.  For the curvature
it needs joint continuity at zero curvature, and a first-order expansion of the
correction whose coefficient is positive definite on the kernel of the vacuum carrier
at `ts`.  No derivative in the angle, no spectral-gap constant and no scalar action
on the kernel are assumed; the gap is produced by compactness.  The sign is the
pre-crossing one; for the families below the opposite sign is reached by reflecting
the interior profile. -/

/-- A positive definite symmetric operator is a unit. -/
theorem unit_of_pos (X : E →L[ℝ] E) (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫)
    (hpos : ∀ x : E, x ≠ 0 → 0 < ⟪x, X x⟫) : IsUnit X := by
  refine unit_of_definite_complements X hs ⊥ ⊤ ?_ (fun x _ hx0 => hpos x hx0) ?_
  · intro x hx hx0
    exact absurd ((Submodule.mem_bot ℝ).mp hx) hx0
  · simp

omit [FiniteDimensional ℝ E] in
theorem psd_of_pos (X : E →L[ℝ] E) (hpos : ∀ x : E, x ≠ 0 → 0 < ⟪x, X x⟫) : PSD X := by
  intro x
  by_cases hx : x = 0
  · rw [hx, inner_zero_left]
  · exact (hpos x hx).le

omit [FiniteDimensional ℝ E] in
/-- Positive semidefiniteness at an angle that is a limit of positive definite angles. -/
theorem psd_of_pd_before (F : ℝ → E →L[ℝ] E) (hc : Continuous F) (ts : ℝ)
    (h : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x : E, x ≠ 0 → 0 < ⟪x, F t₀ x⟫) : PSD (F ts) := by
  intro x
  by_contra hneg
  have hx : ⟪x, F ts x⟫ < 0 := lt_of_not_ge hneg
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hcont : Continuous fun t => ⟪x, F t x⟫ :=
    continuous_const.inner (hc.clm_apply continuous_const)
  have hev : ∀ᶠ t in nhds ts, ⟪x, F t x⟫ < 0 :=
    Filter.Tendsto.eventually (hcont.tendsto ts) (gt_mem_nhds hx)
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨t₀, h1, h2, h3⟩ := h η hη
  have hd : dist t₀ ts < η := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have h4 := hball hd
  have h5 := h3 x hx0
  linarith

/-- A positive semidefinite symmetric operator is bounded below by some `g > 0` on the
orthogonal complement of any subspace containing its kernel (compactness of the unit
sphere). -/
theorem exists_gap_of_psd (X : E →L[ℝ] E) (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (hp : PSD X)
    (K : Submodule ℝ E) (hK : ∀ v, X v = 0 → v ∈ K) :
    ∃ g : ℝ, 0 < g ∧ ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, X y⟫ := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hunit : ∀ y ∈ Kᗮ, y ≠ 0 → ‖y‖⁻¹ • y ∈ Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E) := by
    intro y hy hy0
    refine ⟨?_, Submodule.smul_mem _ _ hy⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_pos_iff.mpr hy0).ne']
  by_cases hne : (Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E)).Nonempty
  · have hS : IsCompact (Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E)) :=
      (isCompact_sphere (0 : E) 1).inter_right (Submodule.isClosed_orthogonal K)
    have hcont : ContinuousOn (fun y => ⟪y, X y⟫) (Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E)) :=
      (continuous_id.inner X.continuous).continuousOn
    obtain ⟨y₀, hy₀, hmin⟩ := hS.exists_isMinOn hne hcont
    have hy₀n : ‖y₀‖ = 1 := mem_sphere_zero_iff_norm.mp hy₀.1
    have hy₀K : y₀ ∈ Kᗮ := hy₀.2
    refine ⟨⟪y₀, X y₀⟫, ?_, ?_⟩
    · rcases (hp y₀).lt_or_eq with h | h
      · exact h
      · exfalso
        have hX0 : X y₀ = 0 := psd_kernel X hs hp y₀ h.symm
        have h0 : ⟪y₀, y₀⟫ = 0 := Submodule.inner_right_of_mem_orthogonal (hK y₀ hX0) hy₀K
        have hy0 : y₀ = 0 := inner_self_eq_zero.mp h0
        rw [hy0, norm_zero] at hy₀n
        exact zero_ne_one hy₀n
    · intro y hy
      by_cases hy0 : y = 0
      · rw [hy0]
        simp
      · have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
        have h1 : ⟪y₀, X y₀⟫ ≤ ⟪‖y‖⁻¹ • y, X (‖y‖⁻¹ • y)⟫ :=
          isMinOn_iff.mp hmin _ (hunit y hy hy0)
        have h2 : ⟪‖y‖⁻¹ • y, X (‖y‖⁻¹ • y)⟫ = (‖y‖ ^ 2)⁻¹ * ⟪y, X y⟫ := by
          rw [map_smul, real_inner_smul_left, real_inner_smul_right]
          ring
        rw [h2, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hyn 2)] at h1
        exact h1
  · refine ⟨1, one_pos, fun y hy => ?_⟩
    by_cases hy0 : y = 0
    · rw [hy0]
      simp
    · exact absurd ⟨_, hunit y hy hy0⟩ hne

/-- Positivity of a two-variable quadratic form. -/
theorem quad_pos {a b g U Y : ℝ} (ha : 0 < a) (hab : b ^ 2 < a * g) (hU : 0 ≤ U) (hY : 0 ≤ Y)
    (hne : U ≠ 0 ∨ Y ≠ 0) : 0 < a * U ^ 2 - 2 * b * U * Y + g * Y ^ 2 := by
  have hQ : a * (a * U ^ 2 - 2 * b * U * Y + g * Y ^ 2) =
      (a * U - b * Y) ^ 2 + (a * g - b ^ 2) * Y ^ 2 := by ring
  have hm : 0 < a * (a * U ^ 2 - 2 * b * U * Y + g * Y ^ 2) := by
    rw [hQ]
    by_cases hY0 : Y = 0
    · have hU0 : U ≠ 0 := by
        rcases hne with h | h
        · exact h
        · exact absurd hY0 h
      have hUp : 0 < U := lt_of_le_of_ne hU (Ne.symm hU0)
      subst hY0
      have h1 : 0 < (a * U) ^ 2 := pow_pos (mul_pos ha hUp) 2
      have e : (a * U - b * 0) ^ 2 + (a * g - b ^ 2) * 0 ^ 2 = (a * U) ^ 2 := by ring
      rw [e]
      exact h1
    · have hYp : 0 < Y := lt_of_le_of_ne hY (Ne.symm hY0)
      have h1 : 0 < (a * g - b ^ 2) * Y ^ 2 := mul_pos (by linarith) (pow_pos hYp 2)
      linarith [sq_nonneg (a * U - b * Y)]
  by_contra hcon
  have h2 := mul_le_mul_of_nonneg_left (not_lt.mp hcon) ha.le
  rw [mul_zero] at h2
  linarith

/-- **The pre-crossing comparison.**  Let `A₀` vanish on `K` and be `≥ g` on `Kᗮ`, and let
`De ≥ c` on `K`.  If `C` is positive semidefinite (it may be singular) and `δ`-close to
`A₀`, then `C + ε De + R` is positive definite once `δ`, `ε` and `‖R‖/ε` are below
thresholds depending only on `g`, `c` and `‖De‖` (`κ` below).  The cross terms between
`K` and `Kᗮ` are absorbed by a fraction `κ ε` of the positive semidefinite form of `C`. -/
theorem pos_of_psd_add (A₀ C De R : E →L[ℝ] E) (K : Submodule ℝ E)
    (hs0 : ∀ x y, ⟪A₀ x, y⟫ = ⟪x, A₀ y⟫) (hsC : ∀ x y, ⟪C x, y⟫ = ⟪x, C y⟫)
    (hker : ∀ u ∈ K, A₀ u = 0) {g c δ ε μ κ : ℝ} (hg : 0 < g) (hc : 0 < c)
    (hgap : ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, A₀ y⟫)
    (hDe : ∀ u ∈ K, c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫)
    (hκ : κ * (g / 2) = ‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c)
    (hC : PSD C) (hδ : ‖C - A₀‖ ≤ δ) (hδg : δ ≤ g / 2) (hκδ : κ * δ ≤ 1)
    (hε : 0 < ε) (hκε : κ * ε ≤ 1) (hμ : μ ≤ c / 4) (hR : ‖R‖ ≤ μ * ε) :
    ∀ x : E, x ≠ 0 → 0 < ⟪x, (C + ε • De + R) x⟫ := by
  intro x hx
  obtain ⟨u, hu, y, hy, rfl⟩ := K.exists_add_mem_mem_orthogonal x
  have hd0 : 0 ≤ ‖De‖ := norm_nonneg _
  have hU0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hY0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hδ
  have hμε0 : 0 ≤ μ * ε := le_trans (norm_nonneg _) hR
  have hpos4 : 0 < 4 * (‖De‖ + 1) ^ 2 / c := div_pos (by positivity) hc
  have hκpos : 0 < κ := by
    by_contra hk
    have h1 := mul_le_mul_of_nonneg_right (not_lt.mp hk) (le_of_lt (half_pos hg))
    rw [zero_mul] at h1
    linarith
  have hκε0 : 0 ≤ κ * ε := (mul_pos hκpos hε).le
  -- expansions
  have hC1 : ⟪u + y, C (u + y)⟫ = ⟪u, C u⟫ + 2 * ⟪u, C y⟫ + ⟪y, C y⟫ := by
    have hsym : ⟪y, C u⟫ = ⟪u, C y⟫ := by rw [← hsC y u, real_inner_comm]
    simp only [map_add, inner_add_left, inner_add_right]
    rw [hsym]
    ring
  have hD1 : ⟪u + y, De (u + y)⟫ = ⟪u, De u⟫ + ⟪u, De y⟫ + ⟪y, De u⟫ + ⟪y, De y⟫ := by
    simp only [map_add, inner_add_left, inner_add_right]
    ring
  have hQ : ⟪u + y, (C + ε • De + R) (u + y)⟫ =
      ⟪u + y, C (u + y)⟫ + ε * ⟪u + y, De (u + y)⟫ + ⟪u + y, R (u + y)⟫ := by
    simp only [add_apply, smul_apply, inner_add_right, real_inner_smul_right]
  -- the bounds
  have hCnn : 0 ≤ ⟪u + y, C (u + y)⟫ := hC _
  have hCu : 0 ≤ ⟪u, C u⟫ := hC u
  have hCuy := (abs_le.mp (cross_upper A₀ C hs0 K hker hδ u hu y)).1
  have hCy := perp_lower A₀ C K hgap hδ y hy
  have hDu := hDe u hu
  have hDuy := (abs_le.mp (abs_inner_op_le De u y)).1
  have hDyu := (abs_le.mp (abs_inner_op_le De y u)).1
  have hDy := (abs_le.mp (abs_inner_op_le De y y)).1
  have hRx : -(μ * ε * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2))) ≤ ⟪u + y, R (u + y)⟫ := by
    have h1 := (abs_le.mp (abs_inner_op_le R (u + y) (u + y))).1
    have hx0 : 0 ≤ ‖u + y‖ := norm_nonneg _
    have hxn : ‖u + y‖ ≤ ‖u‖ + ‖y‖ := norm_add_le u y
    have h3a : ‖u + y‖ * ‖u + y‖ ≤ (‖u‖ + ‖y‖) * (‖u‖ + ‖y‖) :=
      mul_le_mul hxn hxn hx0 (by linarith)
    have e3 : 2 * (‖u‖ ^ 2 + ‖y‖ ^ 2) - (‖u‖ + ‖y‖) * (‖u‖ + ‖y‖) = (‖u‖ - ‖y‖) ^ 2 := by
      ring
    have h3 : ‖u + y‖ * ‖u + y‖ ≤ 2 * (‖u‖ ^ 2 + ‖y‖ ^ 2) := by
      linarith [sq_nonneg (‖u‖ - ‖y‖)]
    have h4 : ‖R‖ * ‖u + y‖ * ‖u + y‖ ≤ μ * ε * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2)) := by
      calc ‖R‖ * ‖u + y‖ * ‖u + y‖ = ‖R‖ * (‖u + y‖ * ‖u + y‖) := by ring
        _ ≤ (μ * ε) * (‖u + y‖ * ‖u + y‖) :=
          mul_le_mul_of_nonneg_right hR (mul_nonneg hx0 hx0)
        _ ≤ (μ * ε) * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2)) := mul_le_mul_of_nonneg_left h3 hμε0
        _ = μ * ε * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2)) := by ring
    linarith
  -- a fraction `κ ε` of the form of `C` absorbs the cross terms
  have hw1 : κ * ε * ⟪u + y, C (u + y)⟫ ≤ ⟪u + y, C (u + y)⟫ := by
    have h1 := mul_nonneg (sub_nonneg.mpr hκε) hCnn
    have e : (1 - κ * ε) * ⟪u + y, C (u + y)⟫ =
        ⟪u + y, C (u + y)⟫ - κ * ε * ⟪u + y, C (u + y)⟫ := by ring
    linarith
  have e5 : κ * ε * ⟪u + y, C (u + y)⟫ =
      κ * ε * ⟪u, C u⟫ + 2 * (κ * ε * ⟪u, C y⟫) + κ * ε * ⟪y, C y⟫ := by
    rw [hC1]
    ring
  have e6 : ε * ⟪u + y, De (u + y)⟫ =
      ε * ⟪u, De u⟫ + ε * ⟪u, De y⟫ + ε * ⟪y, De u⟫ + ε * ⟪y, De y⟫ := by
    rw [hD1]
    ring
  have h5a := mul_le_mul_of_nonneg_left hCuy hκε0
  have h5b := mul_le_mul_of_nonneg_left hCy hκε0
  have h5c := mul_nonneg hκε0 hCu
  have h6a := mul_le_mul_of_nonneg_left hDu hε.le
  have h6b := mul_le_mul_of_nonneg_left hDuy hε.le
  have h6c := mul_le_mul_of_nonneg_left hDyu hε.le
  have h6d := mul_le_mul_of_nonneg_left hDy hε.le
  -- the reduced two-variable form is positive
  have hbr : 0 < (c - 2 * μ) * ‖u‖ ^ 2 - 2 * (κ * δ + ‖De‖) * ‖u‖ * ‖y‖ +
      (κ * (g - δ) - ‖De‖ - 2 * μ) * ‖y‖ ^ 2 := by
    have ha' : c / 2 ≤ c - 2 * μ := by linarith
    have hgd : κ * (g / 2) ≤ κ * (g - δ) := mul_le_mul_of_nonneg_left (by linarith) hκpos.le
    have hg' : c / 2 + 4 * (‖De‖ + 1) ^ 2 / c ≤ κ * (g - δ) - ‖De‖ - 2 * μ := by linarith
    have hprod : (c / 2) * (c / 2 + 4 * (‖De‖ + 1) ^ 2 / c) ≤
        (c - 2 * μ) * (κ * (g - δ) - ‖De‖ - 2 * μ) :=
      mul_le_mul ha' hg' (by linarith) (by linarith)
    have hcc : c / 2 * (4 * (‖De‖ + 1) ^ 2 / c) = 2 * (‖De‖ + 1) ^ 2 := by
      rw [div_mul_div_comm, div_eq_iff (mul_ne_zero two_ne_zero hc.ne')]
      ring
    have hval : (c / 2) * (c / 2 + 4 * (‖De‖ + 1) ^ 2 / c) =
        c ^ 2 / 4 + 2 * (‖De‖ + 1) ^ 2 := by
      rw [mul_add, hcc]
      ring
    have hb0 : 0 ≤ κ * δ + ‖De‖ := by
      have := mul_nonneg hκpos.le hδ0
      linarith
    have hb1 : κ * δ + ‖De‖ ≤ 1 + ‖De‖ := by linarith
    have hbsq : (κ * δ + ‖De‖) * (κ * δ + ‖De‖) ≤ (1 + ‖De‖) * (1 + ‖De‖) :=
      mul_le_mul hb1 hb1 hb0 (by linarith)
    have hd1 : 0 < (1 + ‖De‖) * (1 + ‖De‖) := by positivity
    have hc2 : 0 ≤ c ^ 2 / 4 := by positivity
    have e7 : (‖De‖ + 1) ^ 2 = (1 + ‖De‖) * (1 + ‖De‖) := by ring
    have e8 : (κ * δ + ‖De‖) ^ 2 = (κ * δ + ‖De‖) * (κ * δ + ‖De‖) := by ring
    refine quad_pos (by linarith) ?_ hU0 hY0 ?_
    · rw [e8]
      linarith [hbsq, hprod, hval, hd1, hc2, e7]
    · by_contra hcon
      apply hx
      have h1 : ‖u‖ = 0 := by
        by_contra h
        exact hcon (Or.inl h)
      have h2 : ‖y‖ = 0 := by
        by_contra h
        exact hcon (Or.inr h)
      rw [norm_eq_zero.mp h1, norm_eq_zero.mp h2, add_zero]
  have hfin : ε * ((c - 2 * μ) * ‖u‖ ^ 2 - 2 * (κ * δ + ‖De‖) * ‖u‖ * ‖y‖ +
      (κ * (g - δ) - ‖De‖ - 2 * μ) * ‖y‖ ^ 2) ≤ ⟪u + y, (C + ε • De + R) (u + y)⟫ := by
    rw [hQ]
    linarith
  have := mul_pos hε hbr
  linarith

omit [FiniteDimensional ℝ E] in
/-- The metric form of joint continuity at a point of zero curvature. -/
theorem metric_of_continuousAt {F : Type*} [SeminormedAddCommGroup F] (f : ℝ → ℝ → F) (t : ℝ)
    (h : ContinuousAt (fun p : ℝ × ℝ => f p.1 p.2) (0, t)) :
    ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ ∀ ε s : ℝ, |ε| < r → |s - t| < r →
      ‖f ε s - f 0 t‖ < δ := by
  intro δ hδ
  obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.mp h δ hδ
  refine ⟨r, hr, fun ε s hε hs => ?_⟩
  have hd : dist ((ε, s) : ℝ × ℝ) (0, t) < r := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt hε hs
  have h1 := hball hd
  simp only [dist_eq_norm] at h1
  exact h1

/-- **First-order guarded separation (pre-crossing).**  `A ε t` is the carrier at curvature
`ε` and angle `t`, `D ε` the correction.  Hypotheses: symmetry; continuity in the angle at
every curvature; joint continuity at zero curvature near `ts` (metric form); at zero
curvature the carrier is positive definite at angles arbitrarily close before `ts` and has a negative
direction at angles arbitrarily close after `ts`; the correction is `ε De + o(ε)` with
`De ≥ c > 0` on the kernel of `A 0 ts`.  Then at every small positive curvature some
angle has a positive definite (hence unit) carrier and a singular corrected carrier. -/
theorem first_order_separation
    (A : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E)
    (hsA : ∀ ε t x y, ⟪A ε t x, y⟫ = ⟪x, A ε t y⟫)
    (hsD : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (hcA : ∀ ε, Continuous (A ε)) (ts : ℝ)
    (hjoint : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
      ∀ ε s : ℝ, |ε| < r → |s - t| < r → ‖A ε s - A 0 t‖ < δ)
    (hbefore : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x : E, x ≠ 0 → 0 < ⟪x, A 0 t₀ x⟫)
    (hafter : ∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w : E, ⟪w, A 0 t₁ w⟫ < 0)
    (c : ℝ) (De : E →L[ℝ] E) (hc : 0 < c)
    (hDe : ∀ u : E, A 0 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫)
    (hDexp : ∀ μ : ℝ, 0 < μ → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε < r →
      ‖D ε - ε • De‖ ≤ μ * ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ t : ℝ, IsUnit (A ε t) ∧ ¬ IsUnit (A ε t - D ε) := by
  have hsC : ∀ ε t x y, ⟪(A ε t - D ε) x, y⟫ = ⟪x, (A ε t - D ε) y⟫ := by
    intro ε t x y
    simp only [sub_apply, inner_sub_left, inner_sub_right, hsA, hsD]
  -- the vacuum carrier at `ts`: positive semidefinite, with a gap off its kernel
  have hpsd : PSD (A 0 ts) := psd_of_pd_before (A 0) (hcA 0) ts hbefore
  obtain ⟨K, hK_def⟩ : ∃ K : Submodule ℝ E, K = LinearMap.ker (A 0 ts : E →ₗ[ℝ] E) := ⟨_, rfl⟩
  have hmemK : ∀ v, v ∈ K ↔ A 0 ts v = 0 := by
    intro v
    rw [hK_def, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  have hker : ∀ u ∈ K, A 0 ts u = 0 := fun u hu => (hmemK u).mp hu
  obtain ⟨g, hg, hgap⟩ := exists_gap_of_psd (A 0 ts) (hsA 0 ts) hpsd K
    (fun v hv => (hmemK v).mpr hv)
  have hDeK : ∀ u ∈ K, c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫ :=
    fun u hu => hDe u (hker u hu)
  -- constants
  have hpos4 : 0 < 4 * (‖De‖ + 1) ^ 2 / c := div_pos (by positivity) hc
  obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = 2 / g * (‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c) := ⟨_, rfl⟩
  have hκpos : 0 < κ := by
    rw [hκ_def]
    exact mul_pos (div_pos two_pos hg) (by linarith [norm_nonneg De])
  have hκ : κ * (g / 2) = ‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c := by
    have h2g : 2 / g * (g / 2) = 1 := by
      rw [div_mul_div_comm, mul_comm 2 g, div_self (mul_ne_zero hg.ne' two_ne_zero)]
    rw [hκ_def]
    calc 2 / g * (‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c) * (g / 2)
        = (2 / g * (g / 2)) * (‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c) := by ring
      _ = ‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c := by rw [h2g, one_mul]
  obtain ⟨δ₀, hδ₀_def⟩ : ∃ δ₀ : ℝ, δ₀ = min (g / 2) (1 / κ) := ⟨_, rfl⟩
  have hδ₀ : 0 < δ₀ := by rw [hδ₀_def]; exact lt_min (half_pos hg) (one_div_pos.mpr hκpos)
  have hδ₀g : δ₀ ≤ g / 2 := by rw [hδ₀_def]; exact min_le_left _ _
  have hκδ₀ : κ * δ₀ ≤ 1 := by
    have h := min_le_right (g / 2) (1 / κ)
    rw [← hδ₀_def] at h
    calc κ * δ₀ ≤ κ * (1 / κ) := mul_le_mul_of_nonneg_left h hκpos.le
      _ = 1 := mul_one_div_cancel hκpos.ne'
  -- the window, the correction size and the endpoints
  obtain ⟨η₀, hη₀, hjoint⟩ := hjoint
  obtain ⟨r₁, hr₁, hA1⟩ := hjoint ts (by simp [hη₀]) (δ₀ / 2) (half_pos hδ₀)
  obtain ⟨r₂, hr₂, hD2⟩ := hDexp (c / 4) (by linarith)
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ, ρ = min r₁ η₀ := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρ_def]; exact lt_min hr₁ hη₀
  have hρ1 : ρ ≤ r₁ := by rw [hρ_def]; exact min_le_left _ _
  have hρ2 : ρ ≤ η₀ := by rw [hρ_def]; exact min_le_right _ _
  obtain ⟨t₀, ht₀a, ht₀b, hpd₀⟩ := hbefore ρ hρ
  obtain ⟨t₁, ht₁a, ht₁b, w, hw⟩ := hafter ρ hρ
  obtain ⟨m, hm, hmc⟩ := psd_coercive (A 0 t₀) (hsA 0 t₀) (psd_of_pos _ hpd₀)
    (unit_of_pos _ (hsA 0 t₀) hpd₀)
  obtain ⟨r₃, hr₃, hA3⟩ := hjoint t₀ (by rw [abs_lt]; constructor <;> linarith) (m / 2)
    (half_pos hm)
  obtain ⟨ν, hν_def⟩ : ∃ ν : ℝ, ν = -⟪w, A 0 t₁ w⟫ := ⟨_, rfl⟩
  have hν : 0 < ν := by rw [hν_def]; linarith
  obtain ⟨W, hW_def⟩ : ∃ W : ℝ, W = ‖w‖ ^ 2 + 1 := ⟨_, rfl⟩
  have hW : 0 < W := by rw [hW_def]; positivity
  have hwW : ‖w‖ * ‖w‖ ≤ W := by
    rw [hW_def]
    have e : ‖w‖ * ‖w‖ = ‖w‖ ^ 2 := by ring
    rw [e]
    linarith
  obtain ⟨r₄, hr₄, hA4⟩ := hjoint t₁ (by rw [abs_lt]; constructor <;> linarith) (ν / (2 * W))
    (div_pos hν (by linarith))
  obtain ⟨Dc, hDc_def⟩ : ∃ Dc : ℝ, Dc = ‖De‖ + c / 4 + 1 := ⟨_, rfl⟩
  have hDc : 0 < Dc := by rw [hDc_def]; linarith [norm_nonneg De]
  have hDsmall : ∀ ε : ℝ, 0 < ε → ε < r₂ → ‖D ε‖ ≤ Dc * ε := by
    intro ε hε hεr
    have h1 := hD2 ε hε hεr
    have h2 : ‖D ε‖ ≤ ‖D ε - ε • De‖ + ‖ε • De‖ := by
      calc ‖D ε‖ = ‖(D ε - ε • De) + ε • De‖ := by rw [sub_add_cancel]
        _ ≤ ‖D ε - ε • De‖ + ‖ε • De‖ := norm_add_le _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε] at h2
    rw [hDc_def]
    linarith
  have h2Dc : 0 < 2 * Dc := by linarith
  have h2WDc : 0 < 2 * W * Dc := mul_pos (mul_pos two_pos hW) hDc
  refine ⟨min (min (min r₁ r₂) (min r₃ r₄))
      (min (min (1 / κ) (δ₀ / (2 * Dc))) (min (m / (2 * Dc)) (ν / (2 * W * Dc)))), ?_, ?_⟩
  · exact lt_min (lt_min (lt_min hr₁ hr₂) (lt_min hr₃ hr₄))
      (lt_min (lt_min (one_div_pos.mpr hκpos) (div_pos hδ₀ h2Dc))
        (lt_min (div_pos hm h2Dc) (div_pos hν h2WDc)))
  intro ε hε hε₀
  have e1 : ε < r₁ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have e2 : ε < r₂ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have e3 : ε < r₃ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have e4 : ε < r₄ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have e5 : ε < 1 / κ := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have e6 : ε < δ₀ / (2 * Dc) := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have e7 : ε < m / (2 * Dc) := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have e8 : ε < ν / (2 * W * Dc) := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hεabs : |ε| = ε := abs_of_pos hε
  have hDε := hDsmall ε hε e2
  have hDε1 : ‖D ε‖ < δ₀ / 2 := by
    have h := (lt_div_iff₀ h2Dc).mp e6
    linarith
  have hDε2 : ‖D ε‖ < m / 2 := by
    have h := (lt_div_iff₀ h2Dc).mp e7
    linarith
  have hDε3 : ‖D ε‖ * (2 * W) < ν := by
    have h := (lt_div_iff₀ h2WDc).mp e8
    have h' := mul_le_mul_of_nonneg_right hDε (by linarith : (0 : ℝ) ≤ 2 * W)
    linarith
  have hκε : κ * ε ≤ 1 := by
    have h := (lt_div_iff₀ hκpos).mp e5
    linarith
  -- the corrected carrier is positive definite at `t₀`
  have hC0 : ∀ x : E, x ≠ 0 → 0 < ⟪x, (A ε t₀ - D ε) x⟫ := by
    intro x hx
    have h1 := hmc x
    have h2 : ‖A ε t₀ - A 0 t₀‖ < m / 2 := hA3 ε t₀ (by rw [hεabs]; exact e3) (by simp [hr₃])
    have hxx : 0 < ‖x‖ * ‖x‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hx)
    have h3 := (abs_le.mp (abs_inner_op_le (A ε t₀ - A 0 t₀) x x)).1
    have h4 := (abs_le.mp (abs_inner_op_le (D ε) x x)).2
    have e : ⟪x, (A ε t₀ - D ε) x⟫ = ⟪x, A 0 t₀ x⟫ + ⟪x, (A ε t₀ - A 0 t₀) x⟫ - ⟪x, D ε x⟫ := by
      simp only [sub_apply, inner_sub_right]
      ring
    have h5 := mul_lt_mul_of_pos_right h2 hxx
    have h6 := mul_lt_mul_of_pos_right hDε2 hxx
    have e' : ‖x‖ ^ 2 = ‖x‖ * ‖x‖ := by ring
    rw [e]
    rw [e'] at h1
    linarith
  -- and has a negative direction at `t₁`
  have hC1 : ⟪w, (A ε t₁ - D ε) w⟫ < 0 := by
    have h2 : ‖A ε t₁ - A 0 t₁‖ < ν / (2 * W) := hA4 ε t₁ (by rw [hεabs]; exact e4) (by simp [hr₄])
    have h2' : ‖A ε t₁ - A 0 t₁‖ * (2 * W) < ν := (lt_div_iff₀ (by linarith)).mp h2
    have h3 := (abs_le.mp (abs_inner_op_le (A ε t₁ - A 0 t₁) w w)).2
    have h4 := (abs_le.mp (abs_inner_op_le (D ε) w w)).1
    have h5 := mul_le_mul_of_nonneg_left hwW (norm_nonneg (A ε t₁ - A 0 t₁))
    have h6 := mul_le_mul_of_nonneg_left hwW (norm_nonneg (D ε))
    have e : ⟪w, (A ε t₁ - D ε) w⟫ = ⟪w, A 0 t₁ w⟫ + ⟪w, (A ε t₁ - A 0 t₁) w⟫ - ⟪w, D ε w⟫ := by
      simp only [sub_apply, inner_sub_right]
      ring
    rw [e]
    linarith
  -- the first singular corrected carrier on the window
  have hF : Continuous fun s : ℝ => A ε (t₀ + s) - D ε :=
    ((hcA ε).comp (continuous_const.add continuous_id)).sub continuous_const
  have hT : t₀ + (t₁ - t₀) = t₁ := by ring
  obtain ⟨s, hs0, hsT, hpsdF, hnuF, -, -⟩ := first_carrier_crossing
    (fun s : ℝ => A ε (t₀ + s) - D ε) hF (fun s x y => hsC ε (t₀ + s) x y)
    (by simpa only [add_zero] using psd_of_pos _ hC0)
    (by simpa only [add_zero] using unit_of_pos _ (hsC ε t₀) hC0)
    (t₁ - t₀) (by linarith) w (by simpa only [hT] using hC1)
  have hwin : ‖A ε (t₀ + s) - A 0 ts‖ < δ₀ / 2 := hA1 ε (t₀ + s) (by rw [hεabs]; exact e1)
    (by rw [abs_lt]; constructor <;> linarith)
  have hCδ : ‖(A ε (t₀ + s) - D ε) - A 0 ts‖ ≤ δ₀ := by
    have e : (A ε (t₀ + s) - D ε) - A 0 ts = (A ε (t₀ + s) - A 0 ts) - D ε := by abel
    rw [e]
    calc ‖(A ε (t₀ + s) - A 0 ts) - D ε‖ ≤ ‖A ε (t₀ + s) - A 0 ts‖ + ‖D ε‖ := norm_sub_le _ _
      _ ≤ δ₀ := by linarith
  have hpd := pos_of_psd_add (A 0 ts) (A ε (t₀ + s) - D ε) De (D ε - ε • De)
    K (hsA 0 ts) (hsC ε (t₀ + s)) hker hg hc hgap hDeK hκ hpsdF hCδ
    hδ₀g hκδ₀ hε hκε le_rfl (hD2 ε hε e2)
  have hAeq : (A ε (t₀ + s) - D ε) + ε • De + (D ε - ε • De) = A ε (t₀ + s) := by abel
  refine ⟨t₀ + s, unit_of_pos _ (hsA ε (t₀ + s)) (fun x hx => ?_), hnuF⟩
  have h := hpd x hx
  rwa [hAeq] at h

end Abstract

#print axioms abs_inner_op_le
#print axioms block_pos
#print axioms kernel_form
#print axioms expansion_dist
#print axioms perp_lower
#print axioms cross_upper
#print axioms kernel_form_bounds
#print axioms perturbative_sign_change
#print axioms scalar_on_complex_line
#print axioms expansion_of_hasFDerivAt
#print axioms expansion_of_hasDerivAt
#print axioms unit_of_pos
#print axioms psd_of_pos
#print axioms psd_of_pd_before
#print axioms exists_gap_of_psd
#print axioms quad_pos
#print axioms pos_of_psd_add
#print axioms metric_of_continuousAt
#print axioms first_order_separation

end AdalyFormal.Round9.Guarded.Qualitative

/-! ## Curved twist families with a free interior profile and a free exterior path

The class leaves the exterior field free and allows every bounded interior amplitude mask
(round 5 `maskedU`, `masked_regular`).  A counterexample may therefore use any continuous
one-parameter family `V` of exterior configurations (round 5 uses the frozen twist `Uth`)
and any interior profile `f` with `|f| ≤ 1`, scaled by the curvature `ε`.  At `ε = 0`
the interior is flat whatever `f` is, and the correction vanishes; only the first-order
correction depends on `f`. -/
namespace AdalyFormal.Round9.Guarded.Qualitative

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.D1Literal (PSD)

/-- Interior amplitudes `ε • f` on every bond touching `Ω₀`, the exterior path `V t` on
the purely exterior bonds. -/
noncomputable def pathU (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  maskedU q R (fun e => ε * f e) (V t)

noncomputable def pathP (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (pathU q R V f ε t) a (dilLam q R)

/-- The actual all-plaquette carrier of the family. -/
noncomputable def pathA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selAll selAll (pathP q R V f ε a t)).Ginv

/-- The actual localized correction of the family. -/
noncomputable def pathD (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selIn selIn (pathP q R V f ε a t)).Delta2 (dataS_laws selIn selIn _)

theorem path_agrees (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε s t : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)) :
    pathU q R V f ε s e = pathU q R V f ε t e := by
  classical
  simp only [pathU, maskedU, if_neg he]

theorem path_cont (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    AdalyFormal.D1Literal.ContFam (pathU q R V f ε) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [pathU, maskedU, if_pos he]
    exact hV e
  · simp only [pathU, maskedU, if_neg he]
    exact continuous_const

/-- Continuity of the actual carrier in the path parameter (the proof of round 5's
`twistA_continuous`, through the exterior path identity). -/
theorem pathA_continuous {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ) :
    Continuous (pathA q R V f ε a) := by
  let G := geomOf 2 1 (dilTower q R)
  let U := pathU q R V f ε
  have h : pathA q R V f ε a = fun t => pathA q R V f ε a 0 +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wop G (U 0) a)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (U t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (U 0) Set.univ)).comp
          (Wop G (U 0) a))).comp (iE G)) := by
    funext t
    exact exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      a (dilLam q R) U (fun s e he => path_agrees q R V f ε s 0 e he) selAll t
  rw [h]
  have hd : Continuous fun t => AdalyFormal.StatementLaneR6.deltaKLocCLM (U t)
      (Set.univ : Set (PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)))) :=
    AdalyFormal.D1Literal.cont_deltaKLocCLM (path_cont q R hV f ε) _
  refine continuous_const.add
    (Continuous.clm_comp continuous_const (Continuous.clm_comp ?_ continuous_const))
  exact Continuous.clm_comp continuous_const
    (Continuous.clm_comp (hd.sub continuous_const) continuous_const)

/-- The localized data do not see the exterior. -/
theorem path_data_constant {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    dataS selIn selIn (pathP q R V f ε a t) = dataS selIn selIn (pathP q R V f ε a 0) := by
  change (pathP q R V f ε a t).data = (pathP q R V f ε a 0).data
  exact AdalyFormal.M1IMS.data_congr_U (by norm_num) (dil_admissible hq hR)
    (by norm_num) hroom (pathU q R V f ε 0) (pathU q R V f ε t) a (dilLam q R)
    (fun e he => path_agrees q R V f ε 0 t e (fun hz => hz.1 he.1))

theorem pathD_constant {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    pathD q R V f ε a t = pathD q R V f ε a 0 := by
  have hd := path_data_constant hq hR hroom V f ε a t
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

/-- At zero curvature the correction vanishes, for every exterior path and profile (the
proof of round 6's `twistD_zero_amplitude`, `AHP/round6/limits-r2/Attempt.lean:2421`). -/
theorem pathD_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (h3 : 3 ≤ R * (2*q))
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (a t : ℝ) : pathD q R V f 0 a t = 0 := by
  classical
  let P := pathP q R V f 0 a t
  have hflat : ∀ e : Bond P.Lf, e.1 ∈ P.S.Om 0 → P.U e = 1 := by
    intro e he
    have hz : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) :=
      fun h => h.1 he
    change pathU q R V f 0 t e = 1
    simp only [pathU, maskedU, zero_mul, AdalyFormal.StatementLane2.Ug_zero, ite_eq_right_iff]
    intro h
    exact (hz h).elim
  have hg := AdalyFormal.D1Guarded.G1invS_eq_Ginv_base
    selIn P selIn (dil_admissible hq hR) (by norm_num [P, pathP, gparams]) h3 hflat
  have hid := (dataS selIn selIn P).G1inv_unique
    (AdalyFormal.D1Literal.G1invS_spec selIn selIn P)
    ((dataS selIn selIn P).isG1inv_sub (dataS_laws selIn selIn P))
  have hh : (dataS selIn selIn P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) =
      (dataS selIn selIn P).Ginv := hid.symm.trans hg
  exact sub_eq_self.mp hh

/-- The frozen exterior twist as a path. -/
noncomputable def uthPath (q R : ℕ) : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun t => AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t

theorem uthPath_cont (q R : ℕ) : AdalyFormal.D1Literal.ContFam (uthPath q R) :=
  AdalyFormal.D1Literal.contFam_Uth _

open Classical in
/-- The round-4 single defect line, as a profile. -/
noncomputable def dilMask (q R : ℕ) : Bond (scaleUp 2 1 (dilLu q R)) → ℝ :=
  fun e => if dilPattern q R e then 1 else 0

theorem dilMask_bound (q R : ℕ) (e : Bond (scaleUp 2 1 (dilLu q R))) : |dilMask q R e| ≤ 1 := by
  simp only [dilMask]
  split_ifs <;> simp

/-- The round-4/5 curved twist family is the case `V = Uth`, `f = dilMask`. -/
theorem twistU_eq_path (q R : ℕ) (ε t : ℝ) :
    twistU q R ε t = pathU q R (uthPath q R) (dilMask q R) ε t := by
  classical
  funext e
  simp only [twistU, dilU, pathU, maskedU, uthPath, dilMask]
  split_ifs <;> simp

theorem twistA_eq_path (q R : ℕ) (ε a t : ℝ) :
    twistA q R ε a t = pathA q R (uthPath q R) (dilMask q R) ε a t := by
  unfold twistA twistP pathA pathP
  rw [twistU_eq_path]

theorem twistD_eq_path (q R : ℕ) (ε a t : ℝ) :
    twistD q R ε a t = pathD q R (uthPath q R) (dilMask q R) ε a t := by
  have hd : dataS selIn selIn (twistP q R ε a t) =
      dataS selIn selIn (pathP q R (uthPath q R) (dilMask q R) ε a t) := by
    unfold twistP pathP
    rw [twistU_eq_path]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

/-! ### Separation in a path family refutes the guarded reading -/

/-- Some path parameter has a unit carrier and a non-unit corrected carrier (mass `1`). -/
def PathSeparation (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) : Prop :=
  ∃ t : ℝ, IsUnit (pathA q R V f ε 1 t) ∧ ¬ IsUnit (pathA q R V f ε 1 t - pathD q R V f ε 1 t)

/-- The cofinal premise with, for each scale and radius, a free continuous exterior path
and a free bounded interior profile (both chosen before the cap; only the amplitude `ε`
goes to zero).  NOT proved here. -/
def CofinalPathSeparation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ PathSeparation (2^j) R V f ε

/-- Bridge: the cofinal bookkeeping of round 8, with `masked_regular` in place of
`dil_regular` (the exterior is unconstrained by the class). -/
theorem goalNeg2_of_cofinalPathSeparation (h : CofinalPathSeparation) : GoalNeg2 := by
  apply cofinalPencilFailure_implies_goalNeg2
  refine ⟨2, by norm_num, 1, by norm_num, ?_⟩
  intro m₀
  obtain ⟨j, hj, hRs⟩ := h m₀
  refine ⟨j+1, by omega, by omega, ?_⟩
  intro R₀
  obtain ⟨R, hRR, hR, hR18, V, -, f, hf1, hsep⟩ := hRs R₀
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
  have hmask : ∀ e, |ε * f e| ≤ α/80 := by
    intro e
    rw [abs_mul, abs_of_pos hε0]
    have h1 := hf1 e
    have h2 : ε * |f e| ≤ ε * 1 := mul_le_mul_of_nonneg_left h1 hε0.le
    dsimp [α]
    linarith
  have hclass : ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹
      (pathU q R V f ε t) :=
    ⟨dil_coverage hq hR (by omega), masked_regular hq hR hα (fun e => ε * f e) hmask _⟩
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR
  rw [hpow]
  exact ⟨1, by norm_num, dilLu q R, α, hα, hcap, dil_torus hq R,
    dilTower q R, dil_admissible hq hR, dilLam q R, dil_lambda hq hR,
    pathU q R V f ε t, hclass, dilBt hq R, hBt1, hBt2, hE, hu, hnu⟩

/-- Sign-free interval premise for a path family. -/
def PathSignChange (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) : Prop :=
  ∃ t₀ t₁ : ℝ, t₀ ≤ t₁ ∧
    (∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (pathA q R V f ε 1 t)) ∧
    PSD (pathA q R V f ε 1 t₀ - pathD q R V f ε 1 0) ∧
    ∃ w : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      ⟪w, (pathA q R V f ε 1 t₁ - pathD q R V f ε 1 0) w⟫ < 0

theorem pathSeparation_of_signChange {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V)
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ} {ε : ℝ}
    (h : PathSignChange q R V f ε) : PathSeparation q R V f ε := by
  obtain ⟨t₀, t₁, h01, hguard, h₀, w, h₁⟩ := h
  have hsA : ∀ t x y, ⟪pathA q R V f ε 1 t x, y⟫ = ⟪x, pathA q R V f ε 1 t y⟫ := by
    intro t x y
    exact (dataS selAll selAll (pathP q R V f ε 1 t)).Ginv_symm (dataS_laws selAll selAll _) x y
  have hsD : ∀ x y, ⟪pathD q R V f ε 1 0 x, y⟫ = ⟪x, pathD q R V f ε 1 0 y⟫ := by
    intro x y
    exact ((dataS selIn selIn (pathP q R V f ε 1 0)).Delta2_spec (dataS_laws selIn selIn _)).1 x y
  obtain ⟨t, -, -, hu, hnu⟩ := separation_of_sign_change (pathA q R V f ε 1)
    (pathD q R V f ε 1 0) (pathA_continuous hq hR hroom hV f ε 1) hsA hsD t₀ t₁ h01 hguard
    h₀ w h₁
  refine ⟨t, hu, ?_⟩
  rwa [pathD_constant hq hR hroom V f ε 1 t]

/-! ### Vacuum nondegeneracy: the remaining premise, at zero curvature only -/

/-- **Vacuum nondegeneracy of a path family at `(q,R)`** (mass `1`).  Spectral content only
at zero curvature: the vacuum carrier `pathA q R V f 0 1 ts` (flat interior) vanishes on a
nonzero subspace `K` and is `≥ g > 0` on `Kᗮ` (a first crossing of the path).
Regularity: `(ε,t) ↦ pathA` is Fréchet differentiable at `(0,ts)` and `ε ↦ pathD` is
differentiable at `0`, with derivatives `At`, `Ae`, `De` acting on `K` as scalars
`σ < 0`, `α`, `c`.  Nondegeneracy: `c ≠ 0` (no sign, no size).  NOT proved here. -/
def PathVacuumNondegeneracy (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : Prop :=
  ∃ (ts : ℝ) (K : Submodule ℝ ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (g σ α c : ℝ)
    (At Ae De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))),
    (∀ u ∈ K, pathA q R V f 0 1 ts u = 0) ∧ 0 < g ∧
    (∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, pathA q R V f 0 1 ts y⟫) ∧
    (∃ u ∈ K, u ≠ 0) ∧ σ < 0 ∧ c ≠ 0 ∧
    (∀ u ∈ K, ⟪u, At u⟫ = σ * ‖u‖ ^ 2) ∧
    (∀ u ∈ K, ⟪u, Ae u⟫ = α * ‖u‖ ^ 2) ∧
    (∀ u ∈ K, ⟪u, De u⟫ = c * ‖u‖ ^ 2) ∧
    HasFDerivAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Ae +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight At) ((0 : ℝ), ts) ∧
    HasDerivAt (fun ε : ℝ => pathD q R V f ε 1 0) De 0

/-- Vacuum nondegeneracy gives the sign-free interval premise at EVERY small curvature. -/
theorem pathSignChange_of_vacuum {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (h3 : 3 ≤ R * (2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    (h : PathVacuumNondegeneracy q R V f) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSignChange q R V f ε := by
  obtain ⟨ts, K, g, σ, α, c, At, Ae, De, hker, hg, hgap, hne, hσ, hc, hAt, hAe, hDe,
    hA, hD⟩ := h
  have hsA : ∀ ε t x y, ⟪pathA q R V f ε 1 t x, y⟫ = ⟪x, pathA q R V f ε 1 t y⟫ := by
    intro ε t x y
    exact (dataS selAll selAll (pathP q R V f ε 1 t)).Ginv_symm (dataS_laws selAll selAll _) x y
  have hsD : ∀ ε x y, ⟪pathD q R V f ε 1 0 x, y⟫ = ⟪x, pathD q R V f ε 1 0 y⟫ := by
    intro ε x y
    exact ((dataS selIn selIn (pathP q R V f ε 1 0)).Delta2_spec (dataS_laws selIn selIn _)).1 x y
  exact perturbative_sign_change (fun ε t => pathA q R V f ε 1 t) (fun ε => pathD q R V f ε 1 0)
    hsA hsD ts K g σ α c At Ae De hker hg hgap hne hσ hc hAt hAe hDe
    (expansion_of_hasFDerivAt (fun ε t => pathA q R V f ε 1 t) ts Ae At hA)
    (expansion_of_hasDerivAt (fun ε => pathD q R V f ε 1 0) De (pathD_zero hq hR h3 V f 1 0) hD)

/-- The cofinal vacuum premise: infinitely many dyadic scales, for each infinitely many
even radii `R ≥ 18`, each with SOME continuous exterior path and SOME bounded interior
profile whose first-order correction is visible on a first vacuum crossing kernel.
NOT proved here. -/
def CofinalPathVacuum : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
      PathVacuumNondegeneracy (2^j) R V f

theorem cofinalPathSeparation_of_cofinalPathVacuum (h : CofinalPathVacuum) :
    CofinalPathSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hV, f, hf, hv⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, V, hV, f, hf, fun δ hδ => ?_⟩
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have h3 : 3 ≤ R * (2 * 2^j) := by nlinarith
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  obtain ⟨ε₀, hε₀, hall⟩ := pathSignChange_of_vacuum hq hR h3 hv
  have hm : 0 < min δ ε₀ := lt_min hδ hε₀
  refine ⟨min δ ε₀ / 2, by positivity, by linarith [min_le_left δ ε₀], ?_⟩
  exact pathSeparation_of_signChange hq hR hroom hV
    (hall (min δ ε₀ / 2) (by positivity) (by linarith [min_le_right δ ε₀]))

/-- **Main reduction of this route.**  Cofinal vacuum nondegeneracy (zero-curvature data,
first-order regularity and `c ≠ 0` for some exterior path and bounded interior profile)
refutes the guarded all-plaquette reading. -/
theorem goalNeg2_of_cofinalPathVacuum (h : CofinalPathVacuum) : GoalNeg2 :=
  goalNeg2_of_cofinalPathSeparation (cofinalPathSeparation_of_cofinalPathVacuum h)

/-- The positive reading forbids it. -/
theorem not_cofinalPathVacuum_of_goalPos1 (h : GoalPos1) : ¬ CofinalPathVacuum :=
  fun h' => goalNeg2_of_cofinalPathVacuum h' (goalPos2_iff_goalPos1.mpr h)

/-- What the positive reading demands, stated directly: from some scale on, for all large
even radii, EVERY continuous exterior path and EVERY bounded interior profile fail vacuum
nondegeneracy (the first-order correction is invisible on the first vacuum crossing
kernel, or a regularity, gap or scalar clause fails). -/
theorem goalPos1_forces_vacuum_degeneracy (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ∀ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V →
      ∀ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) →
        ¬ PathVacuumNondegeneracy (2^j) R V f := by
  have h' := not_cofinalPathVacuum_of_goalPos1 h
  by_contra hcon
  apply h'
  intro j₀
  obtain ⟨j, hj⟩ := not_forall.mp (not_exists.mp hcon j₀)
  obtain ⟨hjj, hj2⟩ := Classical.not_imp.mp hj
  refine ⟨j, hjj, fun R₀ => ?_⟩
  obtain ⟨R, hR⟩ := not_forall.mp (not_exists.mp hj2 R₀)
  obtain ⟨hRR, hR1⟩ := Classical.not_imp.mp hR
  obtain ⟨hR2, hR3⟩ := Classical.not_imp.mp hR1
  obtain ⟨hR18, hR4⟩ := Classical.not_imp.mp hR3
  obtain ⟨V, hV⟩ := not_forall.mp hR4
  obtain ⟨hVc, hV1⟩ := Classical.not_imp.mp hV
  obtain ⟨f, hf⟩ := not_forall.mp hV1
  obtain ⟨hfb, hf1⟩ := Classical.not_imp.mp hf
  exact ⟨R, hRR, hR2, hR18, V, hVc, f, hfb, not_not.mp hf1⟩

/-! ### Special cases: the frozen twist, and the round-4 defect line -/

/-- Vacuum nondegeneracy of the round-4/5 single-defect twist family itself. -/
def VacuumNondegeneracy (q R : ℕ) : Prop :=
  PathVacuumNondegeneracy q R (uthPath q R) (dilMask q R)

def CofinalVacuumNondegeneracy : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    VacuumNondegeneracy (2^j) R

theorem cofinalPathVacuum_of_cofinalVacuum (h : CofinalVacuumNondegeneracy) :
    CofinalPathVacuum := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, uthPath (2^j) R, uthPath_cont (2^j) R, dilMask (2^j) R,
    dilMask_bound (2^j) R, hv⟩

theorem goalNeg2_of_cofinalVacuumNondegeneracy (h : CofinalVacuumNondegeneracy) : GoalNeg2 :=
  goalNeg2_of_cofinalPathVacuum (cofinalPathVacuum_of_cofinalVacuum h)

/-- The round-8 separation premise for the round-4 family follows from its vacuum data. -/
theorem cofinalTwistSeparation_of_cofinalVacuum (h : CofinalVacuumNondegeneracy) :
    CofinalTwistSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun δ hδ => ?_⟩
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have h3 : 3 ≤ R * (2 * 2^j) := by nlinarith
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  obtain ⟨ε₀, hε₀, hall⟩ := pathSignChange_of_vacuum hq hR h3 hv
  have hm : 0 < min δ ε₀ := lt_min hδ hε₀
  refine ⟨min δ ε₀ / 2, by positivity, by linarith [min_le_left δ ε₀], ?_⟩
  obtain ⟨t, hu, hnu⟩ := pathSeparation_of_signChange hq hR hroom (uthPath_cont (2^j) R)
    (hall (min δ ε₀ / 2) (by positivity) (by linarith [min_le_right δ ε₀]))
  refine ⟨t, ?_, ?_⟩
  · rw [twistA_eq_path]; exact hu
  · rw [twistA_eq_path, twistD_eq_path]; exact hnu

/-- The same vacuum data with the scalar clauses supplied by a `U(1)` symmetry: the
crossing kernel is the complex line spanned by `u₀` and `J u₀`, where `J` is orthogonal
with `J (J u₀) = -u₀` and the three first-order operators are symmetric and commute with
`J` (for the diagonal families here, `J` is conjugation by `exp(π/4 · E₁)`, a quarter
turn of the charged components).  NOT proved here. -/
def PathVacuumNondegeneracyU1 (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : Prop :=
  ∃ (ts g : ℝ) (u₀ : ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (J At Ae De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))),
    u₀ ≠ 0 ∧ J (J u₀) = -u₀ ∧ (∀ x y, ⟪J x, J y⟫ = ⟪x, y⟫) ∧
    (∀ x y, ⟪At x, y⟫ = ⟪x, At y⟫) ∧ (∀ x y, ⟪Ae x, y⟫ = ⟪x, Ae y⟫) ∧
    (∀ x y, ⟪De x, y⟫ = ⟪x, De y⟫) ∧
    (∀ x, At (J x) = J (At x)) ∧ (∀ x, Ae (J x) = J (Ae x)) ∧ (∀ x, De (J x) = J (De x)) ∧
    pathA q R V f 0 1 ts u₀ = 0 ∧ pathA q R V f 0 1 ts (J u₀) = 0 ∧ 0 < g ∧
    (∀ y ∈ (Submodule.span ℝ {u₀, J u₀})ᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, pathA q R V f 0 1 ts y⟫) ∧
    ⟪u₀, At u₀⟫ < 0 ∧ ⟪u₀, De u₀⟫ ≠ 0 ∧
    HasFDerivAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Ae +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight At) ((0 : ℝ), ts) ∧
    HasDerivAt (fun ε : ℝ => pathD q R V f ε 1 0) De 0

theorem pathVacuum_of_U1 {q R : ℕ} {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    (h : PathVacuumNondegeneracyU1 q R V f) : PathVacuumNondegeneracy q R V f := by
  obtain ⟨ts, g, u₀, J, At, Ae, De, hu₀, hJJ, hJ, hAts, hAes, hDes, hAtJ, hAeJ, hDeJ,
    hk1, hk2, hg, hgap, hσ, hc, hA, hD⟩ := h
  obtain ⟨σ, hσK⟩ := scalar_on_complex_line At J hAts hJ hAtJ u₀ hu₀ hJJ
  obtain ⟨α, hαK⟩ := scalar_on_complex_line Ae J hAes hJ hAeJ u₀ hu₀ hJJ
  obtain ⟨c, hcK⟩ := scalar_on_complex_line De J hDes hJ hDeJ u₀ hu₀ hJJ
  have hmem : u₀ ∈ Submodule.span ℝ {u₀, J u₀} := Submodule.subset_span (by simp)
  have hn : 0 < ‖u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu₀) 2
  have hσ' : σ < 0 := by
    have h1 := hσK u₀ hmem
    rw [h1] at hσ
    by_contra hcon
    have := mul_nonneg (not_lt.mp hcon) hn.le
    linarith
  have hc' : c ≠ 0 := by
    intro hc0
    apply hc
    rw [hcK u₀ hmem, hc0, zero_mul]
  refine ⟨ts, Submodule.span ℝ {u₀, J u₀}, g, σ, α, c, At, Ae, De, ?_, hg, hgap,
    ⟨u₀, hmem, hu₀⟩, hσ', hc', hσK, hαK, hcK, hA, hD⟩
  intro u hu
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  rw [map_add, map_smul, map_smul, hk1, hk2, smul_zero, smul_zero, add_zero]

def CofinalPathVacuumU1 : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
      PathVacuumNondegeneracyU1 (2^j) R V f

theorem goalNeg2_of_cofinalPathVacuumU1 (h : CofinalPathVacuumU1) : GoalNeg2 := by
  apply goalNeg2_of_cofinalPathVacuum
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hV, f, hf, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, V, hV, f, hf, pathVacuum_of_U1 hv⟩

#print axioms pathU
#print axioms pathP
#print axioms pathA
#print axioms pathD
#print axioms path_agrees
#print axioms path_cont
#print axioms pathA_continuous
#print axioms path_data_constant
#print axioms pathD_constant
#print axioms pathD_zero
#print axioms uthPath
#print axioms uthPath_cont
#print axioms dilMask
#print axioms dilMask_bound
#print axioms twistU_eq_path
#print axioms twistA_eq_path
#print axioms twistD_eq_path
#print axioms PathSeparation
#print axioms CofinalPathSeparation
#print axioms goalNeg2_of_cofinalPathSeparation
#print axioms PathSignChange
#print axioms pathSeparation_of_signChange
#print axioms PathVacuumNondegeneracy
#print axioms pathSignChange_of_vacuum
#print axioms CofinalPathVacuum
#print axioms cofinalPathSeparation_of_cofinalPathVacuum
#print axioms goalNeg2_of_cofinalPathVacuum
#print axioms not_cofinalPathVacuum_of_goalPos1
#print axioms goalPos1_forces_vacuum_degeneracy
#print axioms VacuumNondegeneracy
#print axioms CofinalVacuumNondegeneracy
#print axioms cofinalPathVacuum_of_cofinalVacuum
#print axioms goalNeg2_of_cofinalVacuumNondegeneracy
#print axioms cofinalTwistSeparation_of_cofinalVacuum
#print axioms PathVacuumNondegeneracyU1
#print axioms pathVacuum_of_U1
#print axioms CofinalPathVacuumU1
#print axioms goalNeg2_of_cofinalPathVacuumU1

end AdalyFormal.Round9.Guarded.Qualitative

/-! ## The weakest vacuum premise: first-order coupling on a vacuum crossing

At zero curvature the interior is flat whatever the profile is, so all path families
with the same exterior path share one vacuum carrier `vacA`.  Reflecting the profile
`f ↦ -f` reflects the curvature `ε ↦ -ε`, hence the sign of the first-order coupling;
so only the pre-crossing sign has to be treated (`first_order_separation`). -/
namespace AdalyFormal.Round9.Guarded.Qualitative

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.D1Literal (PSD)

/-- The vacuum carrier along an exterior path (flat interior, mass `a`). -/
noncomputable def vacA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  pathA q R V (fun _ => 0) 0 a t

theorem pathU_zero (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (t : ℝ) :
    pathU q R V f 0 t = pathU q R V (fun _ => 0) 0 t := by
  unfold pathU
  congr 1
  funext e
  simp

/-- At zero curvature every profile has the vacuum carrier. -/
theorem pathA_zero (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (a t : ℝ) :
    pathA q R V f 0 a t = vacA q R V a t := by
  unfold vacA pathA pathP
  rw [pathU_zero]

theorem pathU_neg (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) :
    pathU q R V (fun e => -f e) ε t = pathU q R V f (-ε) t := by
  unfold pathU
  congr 1
  funext e
  simp

/-- Reflecting the profile reflects the curvature. -/
theorem pathA_neg (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    pathA q R V (fun e => -f e) ε a t = pathA q R V f (-ε) a t := by
  unfold pathA pathP
  rw [pathU_neg]

theorem pathD_neg (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    pathD q R V (fun e => -f e) ε a t = pathD q R V f (-ε) a t := by
  have hd : dataS selIn selIn (pathP q R V (fun e => -f e) ε a t) =
      dataS selIn selIn (pathP q R V f (-ε) a t) := by
    unfold pathP
    rw [pathU_neg]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

/-- **Vacuum coupling at `(q,R)`** for an exterior path `V` and an interior profile `f`
(mass `1`).  NOT proved here.
* Vacuum crossing (zero curvature, the same for every profile): the vacuum carrier is
  positive definite at angles arbitrarily close before `ts` and has a negative direction
  at angles arbitrarily close after `ts`.
* Regularity: the carrier is jointly continuous in curvature and angle at zero curvature,
  for angles near `ts`, and the correction is differentiable in the curvature at zero, with
  derivative `De`.
* Nondegeneracy: `De` is definite, of EITHER sign, on the kernel of the vacuum carrier at
  `ts`, with constant `c > 0`.
No derivative in the angle, no spectral gap and no scalar action on the kernel are
required. -/
def VacuumCoupling (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : Prop :=
  ∃ (ts c : ℝ) (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))),
    (∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 t₀ x⟫) ∧
    (∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w, ⟪w, vacA q R V 1 t₁ w⟫ < 0) ∧
    (∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ →
      ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) (0, t)) ∧
    HasDerivAt (fun ε : ℝ => pathD q R V f ε 1 0) De 0 ∧
    0 < c ∧ ((∀ u, vacA q R V 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) ∨
      (∀ u, vacA q R V 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫))

/-- The pre-crossing step on the actual operators, for any profile with the given data. -/
theorem eventually_pathSeparation_pos {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (ts c : ℝ) (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (hbef : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 t₀ x⟫)
    (haft : ∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w, ⟪w, vacA q R V 1 t₁ w⟫ < 0)
    (hj : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
      ∀ ε s : ℝ, |ε| < r → |s - t| < r → ‖pathA q R V f ε 1 s - pathA q R V f 0 1 t‖ < δ)
    (hDx : ∀ μ : ℝ, 0 < μ → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε < r →
      ‖pathD q R V f ε 1 0 - ε • De‖ ≤ μ * ε)
    (hc : 0 < c) (hpos : ∀ u, vacA q R V 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSeparation q R V f ε := by
  have hsA : ∀ ε t x y, ⟪pathA q R V f ε 1 t x, y⟫ = ⟪x, pathA q R V f ε 1 t y⟫ := by
    intro ε t x y
    exact (dataS selAll selAll (pathP q R V f ε 1 t)).Ginv_symm (dataS_laws selAll selAll _) x y
  have hsD : ∀ ε x y, ⟪pathD q R V f ε 1 0 x, y⟫ = ⟪x, pathD q R V f ε 1 0 y⟫ := by
    intro ε x y
    exact ((dataS selIn selIn (pathP q R V f ε 1 0)).Delta2_spec (dataS_laws selIn selIn _)).1 x y
  have hbef' : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, pathA q R V f 0 1 t₀ x⟫ := by
    intro η hη
    obtain ⟨t₀, h1, h2, h3⟩ := hbef η hη
    exact ⟨t₀, h1, h2, fun x hx => by rw [pathA_zero]; exact h3 x hx⟩
  have haft' : ∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧
      ∃ w, ⟪w, pathA q R V f 0 1 t₁ w⟫ < 0 := by
    intro η hη
    obtain ⟨t₁, h1, h2, w, hw⟩ := haft η hη
    exact ⟨t₁, h1, h2, w, by rw [pathA_zero]; exact hw⟩
  have hpos' : ∀ u, pathA q R V f 0 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫ := by
    intro u hu
    rw [pathA_zero] at hu
    exact hpos u hu
  obtain ⟨ε₀, hε₀, hall⟩ := first_order_separation (fun ε t => pathA q R V f ε 1 t)
    (fun ε => pathD q R V f ε 1 0) hsA hsD (fun ε => pathA_continuous hq hR hroom hV f ε 1)
    ts hj hbef' haft' c De hc hpos' hDx
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  obtain ⟨t, hu, hnu⟩ := hall ε hε hεε
  exact ⟨t, hu, by rwa [pathD_constant hq hR hroom V f ε 1 t]⟩

/-- Vacuum coupling gives a guarded separation at EVERY small curvature, for the profile
`f` itself or for its reflection `-f` (according to the sign of the coupling). -/
theorem eventually_pathSeparation_of_coupling {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    (h : VacuumCoupling q R V f) :
    ∃ f' : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, (∀ e, |f' e| = |f e|) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSeparation q R V f' ε := by
  obtain ⟨ts, c, De, hbef, haft, ⟨η₀, hη₀, hjoint⟩, hD, hc, hsign⟩ := h
  have h3 : 3 ≤ R * (2*q) := by omega
  have hj : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
      ∀ ε s : ℝ, |ε| < r → |s - t| < r → ‖pathA q R V f ε 1 s - pathA q R V f 0 1 t‖ < δ :=
    ⟨η₀, hη₀, fun t ht => metric_of_continuousAt (fun ε t => pathA q R V f ε 1 t) t (hjoint t ht)⟩
  have hDx := expansion_of_hasDerivAt (fun ε => pathD q R V f ε 1 0) De
    (pathD_zero hq hR h3 V f 1 0) hD
  rcases hsign with hpos | hneg
  · refine ⟨f, fun e => rfl, ?_⟩
    refine eventually_pathSeparation_pos hq hR hroom hV f ts c De hbef haft hj ?_ hc hpos
    intro μ hμ
    obtain ⟨r, hr, hb⟩ := hDx μ hμ
    refine ⟨r, hr, fun ε hε hεr => ?_⟩
    have h1 := hb ε (by rw [abs_of_pos hε]; exact hεr)
    rw [abs_of_pos hε] at h1
    exact h1
  · refine ⟨fun e => -f e, fun e => abs_neg (f e), ?_⟩
    have hj' : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
        ∀ ε s : ℝ, |ε| < r → |s - t| < r →
        ‖pathA q R V (fun e => -f e) ε 1 s - pathA q R V (fun e => -f e) 0 1 t‖ < δ := by
      obtain ⟨η₁, hη₁, hj1⟩ := hj
      refine ⟨η₁, hη₁, fun t ht δ hδ => ?_⟩
      obtain ⟨r, hr, hb⟩ := hj1 t ht δ hδ
      refine ⟨r, hr, fun ε s hε hs => ?_⟩
      rw [pathA_neg, pathA_neg, neg_zero]
      exact hb (-ε) s (by rwa [abs_neg]) hs
    have hDx' : ∀ μ : ℝ, 0 < μ → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε < r →
        ‖pathD q R V (fun e => -f e) ε 1 0 - ε • (-De)‖ ≤ μ * ε := by
      intro μ hμ
      obtain ⟨r, hr, hb⟩ := hDx μ hμ
      refine ⟨r, hr, fun ε hε hεr => ?_⟩
      have h1 := hb (-ε) (by rw [abs_neg, abs_of_pos hε]; exact hεr)
      rw [abs_neg, abs_of_pos hε] at h1
      have e2 : ε • (-De) = (-ε) • De := by
        rw [smul_neg]
        exact (neg_smul ε De).symm
      rw [pathD_neg, e2]
      exact h1
    refine eventually_pathSeparation_pos hq hR hroom hV (fun e => -f e) ts c (-De) hbef haft
      hj' hDx' hc ?_
    intro u hu
    have h1 := hneg u hu
    have e : ⟪u, (-De) u⟫ = -⟪u, De u⟫ := by
      show ⟪u, -(De u)⟫ = -⟪u, De u⟫
      exact inner_neg_right u (De u)
    rw [e]
    exact h1

/-- **The weakest cofinal premise of this route.**  Infinitely many dyadic scales, for
each infinitely many even radii `R ≥ 18`, each with SOME continuous exterior path and SOME
bounded interior profile having vacuum coupling.  NOT proved here. -/
def CofinalVacuumCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
      VacuumCoupling (2^j) R V f

theorem cofinalPathSeparation_of_cofinalVacuumCoupling (h : CofinalVacuumCoupling) :
    CofinalPathSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hV, f, hf, hv⟩ := hRs R₀
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  obtain ⟨f', hf', ε₀, hε₀, hall⟩ := eventually_pathSeparation_of_coupling hq hR hroom hV hv
  refine ⟨R, hRR, hR, hR18, V, hV, f', fun e => by rw [hf']; exact hf e, fun δ hδ => ?_⟩
  have hm : 0 < min δ ε₀ := lt_min hδ hε₀
  exact ⟨min δ ε₀ / 2, by positivity, by linarith [min_le_left δ ε₀],
    hall (min δ ε₀ / 2) (by positivity) (by linarith [min_le_right δ ε₀])⟩

/-- **Main reduction of this round.**  Cofinal vacuum coupling refutes the guarded
all-plaquette reading. -/
theorem goalNeg2_of_cofinalVacuumCoupling (h : CofinalVacuumCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalPathSeparation (cofinalPathSeparation_of_cofinalVacuumCoupling h)

/-- The positive reading forbids it. -/
theorem not_cofinalVacuumCoupling_of_goalPos1 (h : GoalPos1) : ¬ CofinalVacuumCoupling :=
  fun h' => goalNeg2_of_cofinalVacuumCoupling h' (goalPos2_iff_goalPos1.mpr h)

/-- What the positive reading demands, stated directly: from some scale on, for all large
even radii, NO continuous exterior path and NO bounded interior profile has vacuum
coupling. -/
theorem goalPos1_forces_no_vacuum_coupling (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ∀ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V →
      ∀ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) →
        ¬ VacuumCoupling (2^j) R V f := by
  have h' := not_cofinalVacuumCoupling_of_goalPos1 h
  by_contra hcon
  apply h'
  intro j₀
  obtain ⟨j, hj⟩ := not_forall.mp (not_exists.mp hcon j₀)
  obtain ⟨hjj, hj2⟩ := Classical.not_imp.mp hj
  refine ⟨j, hjj, fun R₀ => ?_⟩
  obtain ⟨R, hR⟩ := not_forall.mp (not_exists.mp hj2 R₀)
  obtain ⟨hRR, hR1⟩ := Classical.not_imp.mp hR
  obtain ⟨hR2, hR3⟩ := Classical.not_imp.mp hR1
  obtain ⟨hR18, hR4⟩ := Classical.not_imp.mp hR3
  obtain ⟨V, hV⟩ := not_forall.mp hR4
  obtain ⟨hVc, hV1⟩ := Classical.not_imp.mp hV
  obtain ⟨f, hf⟩ := not_forall.mp hV1
  obtain ⟨hfb, hf1⟩ := Classical.not_imp.mp hf
  exact ⟨R, hRR, hR2, hR18, V, hVc, f, hfb, not_not.mp hf1⟩

/-- The same premise for the round-4/5 family itself: the frozen exterior twist and the single
defect line.  Its coupling is the round-8 vacuum coefficient `c1(q,R)` (numerically negative
at `q = 2, 4`); the reflection then separates with the reversed defect.  NOT proved here. -/
def CofinalDefectLineCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    VacuumCoupling (2^j) R (uthPath (2^j) R) (dilMask (2^j) R)

theorem cofinalVacuumCoupling_of_defectLine (h : CofinalDefectLineCoupling) :
    CofinalVacuumCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, uthPath (2^j) R, uthPath_cont (2^j) R, dilMask (2^j) R,
    dilMask_bound (2^j) R, hv⟩

theorem goalNeg2_of_cofinalDefectLineCoupling (h : CofinalDefectLineCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalVacuumCoupling (cofinalVacuumCoupling_of_defectLine h)

#print axioms vacA
#print axioms pathU_zero
#print axioms pathA_zero
#print axioms pathU_neg
#print axioms pathA_neg
#print axioms pathD_neg
#print axioms VacuumCoupling
#print axioms eventually_pathSeparation_pos
#print axioms eventually_pathSeparation_of_coupling
#print axioms CofinalVacuumCoupling
#print axioms cofinalPathSeparation_of_cofinalVacuumCoupling
#print axioms goalNeg2_of_cofinalVacuumCoupling
#print axioms not_cofinalVacuumCoupling_of_goalPos1
#print axioms goalPos1_forces_no_vacuum_coupling
#print axioms CofinalDefectLineCoupling
#print axioms cofinalVacuumCoupling_of_defectLine
#print axioms goalNeg2_of_cofinalDefectLineCoupling

end AdalyFormal.Round9.Guarded.Qualitative
