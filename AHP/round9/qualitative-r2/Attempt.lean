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

/-!
Round 9.2, qualitative route: the vacuum crossing is a theorem, the two twist directions are
gauge equivalent, and the remaining premise is soft regularity plus one coupling.

* Abstract: a symmetric operator is a unit iff its Gram determinant is nonzero; along a path
  whose matrix coefficients are real-analytic the Gram determinant is analytic, so non-units
  are isolated once the path is a unit somewhere (identity theorem).  A continuous path that is
  positive definite at `t₀`, has a negative direction at `t₁` and isolated non-units, crosses
  at the end of its initial positive semidefinite interval: positive definite arbitrarily close
  before, a negative direction arbitrarily close after.
* Lattice: the frozen continuity chain for the plaquette Hessian (`D1Cont`), repeated with
  `Continuous` replaced by entrywise real-analyticity, and over a general parameter space.
* Concrete: the vacuum carrier of the actual exterior twist is positive definite at angle `0`
  for all large scales and radii (frozen `M2RightInv.p428Target8`), negative at `π` (round 5),
  analytic in the angle; hence it crosses canonically, forwards and backwards.  Joint
  continuity follows from interior continuity.  The literal family may use negative angles.
* Gauge flip: the constant gauge transformation by `[[0,1],[-1,0]]` maps the twist at
  `(ε, t)` to `(-ε, -t)` (frozen covariance lane, extended to the all-plaquette carrier), so
  the backward crossing is the forward one and the coupling changes sign between them.
* Diagonal `U(1)`: the constant rotations `diag(e^{iα}, e^{-iα})` fix every configuration of
  the family, so the vacuum carrier and the first-order coefficient commute with them; on a
  charged complex line the coupling is the single number `⟪u₀, De u₀⟫` (round 8's `c₁`).

Nothing here proves a pinned goal.  The premises `TwistSoftCouplingFwd`, `TwistSoftU1`,
`TwistSoftCoupling` and `PathSoftCoupling` are explicit, unproved hypotheses on the actual
operators.
-/
namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace ComplexConjugate
open Set Filter Topology
open AdalyFormal.D1Literal (PSD psd_kernel psd_coercive)

/-! ### Entrywise real-analytic families of `2 × 2` complex matrices -/

/-- Every entry of the matrix family is real-analytic at every real parameter. -/
def AnM (f : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ (θ₀ : ℝ) (i j : Fin 2), AnalyticAt ℝ (fun θ => f θ i j) θ₀

theorem anM_const (M : Matrix (Fin 2) (Fin 2) ℂ) : AnM (fun _ => M) :=
  fun _ _ _ => analyticAt_const

/-- Real-analytic at every real parameter. -/
def AnR (g : ℝ → ℝ) : Prop := ∀ θ₀ : ℝ, AnalyticAt ℝ g θ₀

theorem anR_const (c : ℝ) : AnR (fun _ => c) := fun _ => analyticAt_const

theorem AnR.add {f g : ℝ → ℝ} (hf : AnR f) (hg : AnR g) : AnR (fun θ => f θ + g θ) :=
  fun θ₀ => (hf θ₀).fun_add (hg θ₀)

theorem AnR.sub {f g : ℝ → ℝ} (hf : AnR f) (hg : AnR g) : AnR (fun θ => f θ - g θ) :=
  fun θ₀ => (hf θ₀).fun_sub (hg θ₀)

theorem AnR.mul {f g : ℝ → ℝ} (hf : AnR f) (hg : AnR g) : AnR (fun θ => f θ * g θ) :=
  fun θ₀ => (hf θ₀).fun_mul (hg θ₀)

theorem AnR.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} (h : ∀ i ∈ s, AnR (f i)) :
    AnR (fun θ => ∑ i ∈ s, f i θ) :=
  fun θ₀ => Finset.analyticAt_fun_sum s (fun i hi => h i hi θ₀)

theorem AnM.add {f g : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) (hg : AnM g) :
    AnM (fun θ => f θ + g θ) := by
  intro θ₀ i j
  simp only [Matrix.add_apply]
  exact (hf θ₀ i j).fun_add (hg θ₀ i j)

theorem AnM.sub {f g : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) (hg : AnM g) :
    AnM (fun θ => f θ - g θ) := by
  intro θ₀ i j
  simp only [Matrix.sub_apply]
  exact (hf θ₀ i j).fun_sub (hg θ₀ i j)

theorem AnM.neg {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) : AnM (fun θ => -f θ) := by
  intro θ₀ i j
  simp only [Matrix.neg_apply]
  exact (hf θ₀ i j).fun_neg

theorem AnM.mul {f g : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) (hg : AnM g) :
    AnM (fun θ => f θ * g θ) := by
  intro θ₀ i j
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ (fun k _ => (hf θ₀ i k).fun_mul (hg θ₀ k j))

theorem AnM.smul {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) (c : ℂ) :
    AnM (fun θ => c • f θ) := by
  intro θ₀ i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact analyticAt_const.fun_mul (hf θ₀ i j)

theorem AnM.star {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) :
    AnM (fun θ => star (f θ)) := by
  intro θ₀ i j
  simp only [Matrix.star_apply]
  have h1 : AnalyticAt ℝ (fun θ => f θ j i) θ₀ := hf θ₀ j i
  have h2 : AnalyticAt ℝ (Complex.conjCLE : ℂ →L[ℝ] ℂ) ((fun θ => f θ j i) θ₀) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).analyticAt _
  have h := AnalyticAt.comp (f := fun θ => f θ j i) h2 h1
  refine h.congr (Filter.Eventually.of_forall (fun θ => ?_))
  simp [Function.comp]

/-- Real part of the trace of an analytic family is real-analytic. -/
theorem AnM.trace_re {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) :
    AnR (fun θ => (Matrix.trace (f θ)).re) := by
  intro θ₀
  have htr : AnalyticAt ℝ (fun θ => Matrix.trace (f θ)) θ₀ := by
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.analyticAt_fun_sum _ (fun i _ => hf θ₀ i i)
  have h2 : AnalyticAt ℝ (Complex.reCLM : ℂ →L[ℝ] ℝ) ((fun θ => Matrix.trace (f θ)) θ₀) :=
    (Complex.reCLM : ℂ →L[ℝ] ℝ).analyticAt _
  have h := AnalyticAt.comp (f := fun θ => Matrix.trace (f θ)) h2 htr
  refine h.congr (Filter.Eventually.of_forall (fun θ => ?_))
  simp [Function.comp]

theorem AnM.tr_re3 {f g h : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) (hg : AnM g)
    (hh : AnM h) : AnR (fun θ => (Matrix.trace (f θ * g θ * h θ)).re) :=
  ((hf.mul hg).mul hh).trace_re

/-- `θ ↦ exp(± i θ)` is real-analytic. -/
theorem analyticAt_exp_I (s : ℝ) (θ₀ : ℝ) :
    AnalyticAt ℝ (fun θ : ℝ => Complex.exp (s * θ * Complex.I)) θ₀ := by
  have hlin : AnalyticAt ℝ (fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) θ₀ := by
    have h1 : AnalyticAt ℝ (fun θ : ℝ => ((θ : ℂ))) θ₀ :=
      (Complex.ofRealCLM.analyticAt θ₀).congr (Filter.Eventually.of_forall (fun θ => rfl))
    exact (analyticAt_const.fun_mul h1).fun_mul analyticAt_const
  have hexp : AnalyticAt ℝ Complex.exp ((fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) θ₀) :=
    (analyticAt_cexp (z := (s : ℂ) * (θ₀ : ℂ) * Complex.I)).restrictScalars
  exact AnalyticAt.comp (f := fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) hexp hlin

/-! ### The Gram determinant: a polynomial certificate of invertibility -/

section Gram
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The determinant of the matrix of `A` in the standard orthonormal basis. -/
noncomputable def gramDet (A : E →L[ℝ] E) : ℝ :=
  Matrix.det (Matrix.of fun i j =>
    ⟪stdOrthonormalBasis ℝ E i, A (stdOrthonormalBasis ℝ E j)⟫)

theorem gramDet_eq (A : E →L[ℝ] E) : gramDet A = LinearMap.det (A : E →ₗ[ℝ] E) := by
  rw [← LinearMap.det_toMatrix (stdOrthonormalBasis ℝ E).toBasis]
  unfold gramDet
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]
  rfl

theorem isUnit_iff_gramDet (A : E →L[ℝ] E) : IsUnit A ↔ gramDet A ≠ 0 := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_isUnit_det,
    gramDet_eq, isUnit_iff_ne_zero]

/-- If every matrix coefficient of a path of operators is real-analytic, so is its
Gram determinant. -/
theorem analyticAt_gramDet {A : ℝ → E →L[ℝ] E}
    (h : ∀ (x y : E) (θ₀ : ℝ), AnalyticAt ℝ (fun θ => ⟪x, A θ y⟫) θ₀) (θ₀ : ℝ) :
    AnalyticAt ℝ (fun θ => gramDet (A θ)) θ₀ := by
  unfold gramDet
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine analyticAt_const.fun_mul ?_
  refine Finset.analyticAt_fun_prod _ (fun i _ => ?_)
  simp only [Matrix.of_apply]
  exact h _ _ θ₀

/-- Isolated non-units: an analytic path of operators that is a unit at one parameter is a
unit on a punctured neighbourhood of EVERY parameter. -/
theorem isUnit_punctured {A : ℝ → E →L[ℝ] E}
    (h : ∀ (x y : E) (θ₀ : ℝ), AnalyticAt ℝ (fun θ => ⟪x, A θ y⟫) θ₀)
    {t₀ : ℝ} (hu : IsUnit (A t₀)) (t : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (A s) := by
  set g : ℝ → ℝ := fun θ => gramDet (A θ) with hgdef
  have hg : AnalyticOnNhd ℝ g Set.univ := fun θ _ => analyticAt_gramDet h θ
  rcases (hg t (Set.mem_univ t)).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exfalso
    have hz := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ t) h0 (Set.mem_univ t₀)
    exact ((isUnit_iff_gramDet _).mp hu) hz
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne
    obtain ⟨η, hη, hb⟩ := hne
    refine ⟨η, hη, fun s hs hst => (isUnit_iff_gramDet _).mpr (hb ?_ hs)⟩
    rw [Real.dist_eq]
    exact hst

end Gram

/-! ### The end of the initial positive semidefinite interval -/

section Edge
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem abs_inner_le_opNorm (N : E →L[ℝ] E) (x : E) : |⟪x, N x⟫| ≤ ‖N‖ * ‖x‖ ^ 2 := by
  calc |⟪x, N x⟫| ≤ ‖x‖ * ‖N x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖N‖ * ‖x‖) := by gcongr; exact N.le_opNorm x
    _ = ‖N‖ * ‖x‖ ^ 2 := by ring

/-- A positive semidefinite unit is positive definite. -/
theorem pos_of_psd_unit (X : E →L[ℝ] E) (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (hp : PSD X)
    (hu : IsUnit X) (x : E) (hx : x ≠ 0) : 0 < ⟪x, X x⟫ := by
  rcases (hp x).lt_or_eq with h | h
  · exact h
  · exfalso
    have hk := psd_kernel X hs hp x h.symm
    have hinj : Function.Injective X := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
    exact hx (hinj (by rw [hk, map_zero]))

/-- A positive definite operator is a unit. -/
theorem unit_of_pd (X : E →L[ℝ] E) (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, X x⟫) : IsUnit X := by
  have hi : Function.Injective X := (injective_iff_map_eq_zero X).mpr (by
    intro v hv
    by_contra hn
    have h := hpd v hn
    rw [hv, inner_zero_right] at h
    exact (lt_irrefl 0) h)
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi, (LinearMap.injective_iff_surjective (f := (show E →ₗ[ℝ] E from X))).mp hi⟩

omit [FiniteDimensional ℝ E] in
theorem psd_of_pd (X : E →L[ℝ] E) (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, X x⟫) : PSD X := by
  intro v
  by_cases hv : v = 0
  · rw [hv]; simp
  · exact (hpd v hv).le

/-- Positive definiteness is open along a continuous symmetric path. -/
theorem eventually_pd {A : ℝ → E →L[ℝ] E} (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫) (t₀ : ℝ)
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, A t₀ x⟫) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s - t₀| < δ → ∀ x, x ≠ 0 → 0 < ⟪x, A s x⟫ := by
  obtain ⟨m, hm, hmc⟩ := psd_coercive (A t₀) (hs t₀) (psd_of_pd _ hpd) (unit_of_pd _ hpd)
  have hct : ContinuousAt A t₀ := hc.continuousAt
  rw [Metric.continuousAt_iff] at hct
  obtain ⟨δ, hδ, hb⟩ := hct (m / 2) (by positivity)
  refine ⟨δ, hδ, fun s hs' x hx => ?_⟩
  have hd : dist (A s) (A t₀) < m / 2 := hb (by rw [Real.dist_eq]; exact hs')
  rw [dist_eq_norm] at hd
  have h1 := hmc x
  have h2 := abs_inner_le_opNorm (A s - A t₀) x
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  have e : ⟪x, A s x⟫ = ⟪x, A t₀ x⟫ + ⟪x, (A s - A t₀) x⟫ := by
    rw [show (A s - A t₀) x = A s x - A t₀ x from rfl, inner_sub_right]; ring
  have h3 : ‖A s - A t₀‖ * ‖x‖ ^ 2 ≤ m / 2 * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hd.le hx2.le
  rw [e]
  have := (abs_le.mp h2).1
  nlinarith

/-- The end of the initial positive semidefinite interval of a path, in `[t₀, t₁]`. -/
noncomputable def psdEdge (A : ℝ → E →L[ℝ] E) (t₀ t₁ : ℝ) : ℝ :=
  sSup {t | t ∈ Icc t₀ t₁ ∧ ∀ s ∈ Icc t₀ t, PSD (A s)}

/-- **The canonical crossing.**  A continuous symmetric path, positive definite at `t₀`,
with a negative direction at `t₁ > t₀` and isolated non-units, has at the end `ts` of its
initial positive semidefinite interval a genuine sign change: `A ts` is positive
semidefinite and singular, `A` is positive definite at parameters arbitrarily close before
`ts` and has a negative direction at parameters arbitrarily close after `ts`. -/
theorem psdEdge_spec (A : ℝ → E →L[ℝ] E) (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫) {t₀ t₁ : ℝ} (h01 : t₀ < t₁)
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, A t₀ x⟫) (w : E) (hw : ⟪w, A t₁ w⟫ < 0)
    (hiso : ∀ t, ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (A s)) :
    t₀ < psdEdge A t₀ t₁ ∧ psdEdge A t₀ t₁ < t₁ ∧
    PSD (A (psdEdge A t₀ t₁)) ∧ ¬ IsUnit (A (psdEdge A t₀ t₁)) ∧
    (∀ s, t₀ ≤ s → s ≤ psdEdge A t₀ t₁ → PSD (A s)) ∧
    (∀ η : ℝ, 0 < η → ∃ s, psdEdge A t₀ t₁ - η < s ∧ s < psdEdge A t₀ t₁ ∧
        ∀ x, x ≠ 0 → 0 < ⟪x, A s x⟫) ∧
    (∀ η : ℝ, 0 < η → ∃ s, psdEdge A t₀ t₁ < s ∧ s < psdEdge A t₀ t₁ + η ∧
        ∃ v, ⟪v, A s v⟫ < 0) := by
  set S : Set ℝ := {t | t ∈ Icc t₀ t₁ ∧ ∀ s ∈ Icc t₀ t, PSD (A s)} with hS
  have hts' : psdEdge A t₀ t₁ = sSup S := rfl
  set ts := psdEdge A t₀ t₁ with hts
  have hpsd0 : PSD (A t₀) := psd_of_pd _ hpd
  have h0S : t₀ ∈ S := ⟨⟨le_rfl, h01.le⟩, fun s hs' => by
    rw [le_antisymm hs'.2 hs'.1]; exact hpsd0⟩
  have hne : S.Nonempty := ⟨t₀, h0S⟩
  have hbdd : BddAbove S := ⟨t₁, fun t ht => ht.1.2⟩
  have hts0 : t₀ ≤ ts := by rw [hts']; exact le_csSup hbdd h0S
  have hts1 : ts ≤ t₁ := by rw [hts']; exact csSup_le hne (fun t ht => ht.1.2)
  obtain ⟨δ, hδ, hpdn⟩ := eventually_pd hc hs t₀ hpd
  have hδS : min (t₀ + δ / 2) t₁ ∈ S := by
    refine ⟨⟨le_min (by linarith) h01.le, min_le_right _ _⟩, fun s hs' => ?_⟩
    have hs1 : s ≤ t₀ + δ / 2 := le_trans hs'.2 (min_le_left _ _)
    exact psd_of_pd _ (hpdn s (by rw [abs_lt]; constructor <;> linarith [hs'.1]))
  have hts0' : t₀ < ts := by
    have h1 : t₀ < min (t₀ + δ / 2) t₁ := lt_min (by linarith) h01
    have h2 : min (t₀ + δ / 2) t₁ ≤ ts := by rw [hts']; exact le_csSup hbdd hδS
    linarith
  have hlt : ∀ s, t₀ ≤ s → s < ts → PSD (A s) := by
    intro s hs0 hs1
    rw [hts'] at hs1
    obtain ⟨t, ht, hst⟩ := exists_lt_of_lt_csSup hne hs1
    exact ht.2 s ⟨hs0, hst.le⟩
  have hpsd_ts : PSD (A ts) := by
    intro v
    have hsub : Ico t₀ ts ⊆ {s : ℝ | 0 ≤ ⟪v, A s v⟫} := fun s hs' => hlt s hs'.1 hs'.2 v
    have hcl : IsClosed {s : ℝ | 0 ≤ ⟪v, A s v⟫} := isClosed_le continuous_const (by fun_prop)
    have hcs := hcl.closure_subset_iff.mpr hsub
    exact hcs (by rw [closure_Ico hts0'.ne]; exact ⟨hts0, le_rfl⟩)
  have hle : ∀ s, t₀ ≤ s → s ≤ ts → PSD (A s) := by
    intro s hs0 hs1
    rcases hs1.lt_or_eq with h | h
    · exact hlt s hs0 h
    · rw [h]; exact hpsd_ts
  have hts1' : ts < t₁ := by
    rcases hts1.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hpsd_ts w
      rw [h] at this
      linarith
  have haft : ∀ η : ℝ, 0 < η → ∃ s, ts < s ∧ s < ts + η ∧ ∃ v, ⟪v, A s v⟫ < 0 := by
    intro η hη
    set t' := min (ts + η / 2) t₁ with ht'
    have ht'1 : ts < t' := lt_min (by linarith) hts1'
    have hnot : t' ∉ S := by
      intro h
      have : t' ≤ ts := by rw [hts']; exact le_csSup hbdd h
      linarith
    have hnall : ¬ ∀ s ∈ Icc t₀ t', PSD (A s) := fun hall =>
      hnot ⟨⟨by linarith, min_le_right _ _⟩, hall⟩
    push Not at hnall
    obtain ⟨s, hs', hns⟩ := hnall
    have hsts : ts < s := by
      by_contra hcon
      push Not at hcon
      exact hns (hle s hs'.1 hcon)
    have hst' : s < ts + η := lt_of_le_of_lt (le_trans hs'.2 (min_le_left _ _)) (by linarith)
    unfold PSD at hns
    push Not at hns
    exact ⟨s, hsts, hst', hns⟩
  have hnu : ¬ IsUnit (A ts) := by
    intro hu
    have hpdts : ∀ x, x ≠ 0 → 0 < ⟪x, A ts x⟫ := fun x hx =>
      pos_of_psd_unit _ (hs ts) hpsd_ts hu x hx
    obtain ⟨δ', hδ', hb⟩ := eventually_pd hc hs ts hpdts
    obtain ⟨s, h1, h2, v, hv⟩ := haft δ' hδ'
    have hsd := hb s (by rw [abs_lt]; constructor <;> linarith)
    by_cases hv0 : v = 0
    · rw [hv0] at hv; simp at hv
    · linarith [hsd v hv0]
  have hbef : ∀ η : ℝ, 0 < η → ∃ s, ts - η < s ∧ s < ts ∧ ∀ x, x ≠ 0 → 0 < ⟪x, A s x⟫ := by
    intro η hη
    obtain ⟨η', hη', hiso'⟩ := hiso ts
    set r := min (min η η') (ts - t₀) with hr
    have hr0 : 0 < r := lt_min (lt_min hη hη') (by linarith)
    have hr1 : r ≤ η := le_trans (min_le_left _ _) (min_le_left _ _)
    have hr2 : r ≤ η' := le_trans (min_le_left _ _) (min_le_right _ _)
    have hr3 : r ≤ ts - t₀ := min_le_right _ _
    refine ⟨ts - r / 2, by linarith, by linarith, fun x hx => ?_⟩
    have hu := hiso' (ts - r / 2) (by intro h; linarith)
      (by rw [abs_lt]; constructor <;> linarith)
    exact pos_of_psd_unit _ (hs _) (hle _ (by linarith) (by linarith)) hu x hx
  exact ⟨hts0', hts1', hpsd_ts, hnu, hle, hbef, haft⟩

end Edge

#print axioms gramDet_eq
#print axioms isUnit_iff_gramDet
#print axioms analyticAt_gramDet
#print axioms isUnit_punctured
#print axioms psdEdge_spec
#print axioms AnM.trace_re
#print axioms analyticAt_exp_I

#print axioms AnM
#print axioms anM_const
#print axioms AnR
#print axioms anR_const
#print axioms AnR.add
#print axioms AnR.sub
#print axioms AnR.mul
#print axioms AnR.sum
#print axioms AnM.add
#print axioms AnM.sub
#print axioms AnM.neg
#print axioms AnM.mul
#print axioms AnM.smul
#print axioms AnM.star
#print axioms AnM.tr_re3
#print axioms gramDet
#print axioms abs_inner_le_opNorm
#print axioms pos_of_psd_unit
#print axioms unit_of_pd
#print axioms psd_of_pd
#print axioms eventually_pd
#print axioms psdEdge

end AdalyFormal.Round9.Guarded.QualitativeR2

/-! ## The plaquette Hessian along an analytic family of links

The frozen `D1Cont` proves that `θ ↦ deltaKLocCLM (U θ) P` is continuous when every link
matrix is.  The same chain of elementary operations (matrix products, adjoints, traces,
real parts, finite sums) preserves real-analyticity; below is that chain, statement by
statement, with `Continuous` replaced by entrywise analyticity.  The second section repeats
the frozen continuity chain over an arbitrary topological parameter space (used for joint
continuity in curvature and angle). -/
namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant suTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.StatementLaneR6
open AdalyFormal.D1Literal (SU2m)

variable {L : PeriodicLatticeExtent}

/-- A family of link configurations whose link matrices are entrywise real-analytic. -/
def AnFam (U : ℝ → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, AnM fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)

section
variable {U : ℝ → PeriodicLinkConfiguration SU2m L} (hU : AnFam U)
include hU

theorem an_inv_coe (e : PeriodicLatticeEdge L) :
    AnM fun θ => (((U θ e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => (((U θ e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => star ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    rfl
  rw [this]
  exact (hU e).star

theorem an_holonomyElem (p : PeriodicLatticePlaquette L) :
    AnM fun θ => ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => ((U θ (p.1, p.2.1.1) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((U θ (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        (((U θ (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ : SU2m) :
          Matrix (Fin 2) (Fin 2) ℂ) *
        (((U θ (p.1, p.2.1.2))⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    rfl
  rw [this]
  exact (((hU _).mul (hU _)).mul (an_inv_coe hU _)).mul (an_inv_coe hU _)

theorem an_holonomyElemInv (p : PeriodicLatticePlaquette L) :
    AnM fun θ => ((holonomyElemInv (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((holonomyElemInv (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => star ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ; rfl
  rw [this]
  exact (an_holonomyElem hU p).star

theorem an_reHolonomy (p : PeriodicLatticePlaquette L) : AnM fun θ => reHolonomy (U θ) p := by
  unfold reHolonomy
  exact ((an_holonomyElem hU p).add (an_holonomyElemInv hU p)).smul _

theorem an_imHolonomy (p : PeriodicLatticePlaquette L) : AnM fun θ => imHolonomy (U θ) p := by
  unfold imHolonomy
  exact ((an_holonomyElem hU p).sub (an_holonomyElemInv hU p)).smul _

theorem an_RMap (e : PeriodicLatticeEdge L) (X : SuTwo) :
    AnM fun θ => ((RMap (U θ e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((RMap (U θ e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ) *
        star ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    exact AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply (U θ e) X
  rw [this]
  exact ((hU e).mul (anM_const _)).mul (hU e).star

theorem an_curlMat (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    AnM fun θ => curlMatLM (U θ) p A := by
  simp only [curlMatLM_apply]
  unfold curlValueCovariant
  simp only [Submodule.coe_add, Submodule.coe_sub]
  exact (((anM_const _).add (an_RMap hU _ _)).sub (an_RMap hU _ _)).sub (anM_const _)

theorem an_a1 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    AnM fun θ => a1LM (U θ) p A := by
  show AnM fun θ =>
    -(bondMatRLM (U θ (p.1, p.2.1.2)) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) A)
  simp only [bondMatRLM_apply]
  exact (an_RMap hU _ _).neg

theorem an_a4 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    AnM fun θ => a4LM (U θ) p A := by
  show AnM fun θ =>
    bondMatRLM (U θ (p.1, p.2.1.1)) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) A
  simp only [bondMatRLM_apply]
  exact an_RMap hU _ _

theorem an_bilPlaq (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    AnR fun θ => bilPlaq (U θ) p A B := by
  simp only [bilPlaq_atoms]
  have hI : ∀ {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ}, AnM f → AnM fun θ => smulILM (f θ) := by
    intro f hf
    exact hf.smul Complex.I
  have b1A : AnM fun θ => b1LM (U θ) p A := hI (an_a1 hU p A)
  have b4B : AnM fun θ => b4LM (U θ) p B := hI (an_a4 hU p B)
  have hre := an_reHolonomy hU p
  have him := an_imHolonomy hU p
  have hcA : AnM fun θ => smulILM (curlMatLM (U θ) p A) := hI (an_curlMat hU p A)
  have hcB : AnM fun θ => smulILM (curlMatLM (U θ) p B) := hI (an_curlMat hU p B)
  have k : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), AnM fun _ : ℝ => M := fun M => anM_const M
  exact ((((((AnM.tr_re3 hcA hcB (hre.sub (k 1))).add
    ((AnM.tr_re3 (hI b1A) (k _) him).sub (AnM.tr_re3 (k _) b1A him))).add
    ((AnM.tr_re3 (hI b1A) (k _) him).sub (AnM.tr_re3 (k _) b1A him))).add
    ((AnM.tr_re3 (hI b1A) b4B him).sub (AnM.tr_re3 (hI b4B) b1A him))).add
    ((AnM.tr_re3 (k _) (k _) him).sub (AnM.tr_re3 (k _) (k _) him))).add
    ((AnM.tr_re3 (k _) b4B him).sub (AnM.tr_re3 (hI b4B) (k _) him))).add
    ((AnM.tr_re3 (k _) b4B him).sub (AnM.tr_re3 (hI b4B) (k _) him))

open Classical in
theorem an_deltaPrimeBil (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    AnR fun θ => deltaPrimeBilNormLoc (U θ) P A B := by
  have h : ∀ A B : Bond L → SuTwo, AnR fun θ => deltaPrimeBilRawLoc (U θ) P A B := by
    intro A B
    simp only [deltaPrimeBilRawLoc_apply]
    exact AnR.sum _ (fun p _ => by
      by_cases hp : p ∈ P
      · simp only [hp, if_true]; exact an_bilPlaq hU p A B
      · simp only [hp, if_false]; exact anR_const 0)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  exact (anR_const _).mul ((anR_const _).mul ((h A B).add (h B A)))

open Classical in
theorem an_curlInner (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    AnR fun θ =>
      (inner ℝ (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) x))
        (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) y)) : ℝ) := by
  simp only [PiLp.inner_apply]
  refine AnR.sum _ (fun p _ => ?_)
  simp only [plaqMask_apply]
  by_cases hp : p ∈ P
  · simp only [hp, if_true]
    show AnR fun θ => AdalyFormal.Balaban.SuTwoInner.hsInner
      (curlValueCovariant (U θ) (WithLp.ofLp x) p) (curlValueCovariant (U θ) (WithLp.ofLp y) p)
    unfold AdalyFormal.Balaban.SuTwoInner.hsInner
    exact (anR_const _).mul
      ((an_curlMat hU p (WithLp.ofLp x)).mul (an_curlMat hU p (WithLp.ofLp y))).trace_re
  · simp only [hp, if_false, inner_zero_left]
    exact anR_const 0

/-- Every matrix coefficient of the plaquette Hessian is real-analytic in the parameter. -/
theorem an_inner_delta (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    AnR fun θ => (inner ℝ x (deltaKLocCLM (U θ) P y) : ℝ) := by
  simp only [inner_deltaKLocCLM]
  exact (an_curlInner hU P x y).add (an_deltaPrimeBil hU P _ _)

end

/-- `diag(e^{iθ}, e^{-iθ})` is entrywise real-analytic. -/
theorem anM_uMat : AnM fun θ => AdalyFormal.D1Literal.uMat θ := by
  intro θ₀ i j
  fin_cases i <;> fin_cases j
  · refine (analyticAt_exp_I 1 θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · refine (analyticAt_exp_I (-1) θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]

/-- The frozen exterior twist is an analytic family. -/
theorem anFam_Uth (Om : Set (PeriodicLatticeSite L)) : AnFam (AdalyFormal.D1Literal.Uth Om) := by
  intro e
  unfold AdalyFormal.D1Literal.Uth
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb Om
  · simp only [he, if_true]
    show AnM fun θ => AdalyFormal.D1Literal.uMat θ
    exact anM_uMat
  · simp only [he, if_false]
    exact anM_const _

/-! ### The frozen continuity chain over an arbitrary parameter space -/

section Param
variable {Y : Type*} [TopologicalSpace Y]

/-- A family of link configurations over a topological parameter space, continuous link by
link (the frozen `ContFam` with `ℝ` replaced by `Y`). -/
def ContFamY (U : Y → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, Continuous fun y => ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)

section
variable {U : Y → PeriodicLinkConfiguration SU2m L} (hU : ContFamY U)
include hU

theorem contY_inv_coe (e : PeriodicLatticeEdge L) :
    Continuous fun y => (((U y e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => (((U y e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => star ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y
    rfl
  rw [this]
  exact (hU e).star

theorem contY_holonomyElem (p : PeriodicLatticePlaquette L) :
    Continuous fun y => ((holonomyElem (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => ((holonomyElem (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => ((U y (p.1, p.2.1.1) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((U y (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        (((U y (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ : SU2m) :
          Matrix (Fin 2) (Fin 2) ℂ) *
        (((U y (p.1, p.2.1.2))⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y
    rfl
  rw [this]
  exact (((hU _).matrix_mul (hU _)).matrix_mul (contY_inv_coe hU _)).matrix_mul
    (contY_inv_coe hU _)

theorem contY_holonomyElemInv (p : PeriodicLatticePlaquette L) :
    Continuous fun y => ((holonomyElemInv (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => ((holonomyElemInv (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => star ((holonomyElem (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y; rfl
  rw [this]
  exact (contY_holonomyElem hU p).star

theorem contY_reHolonomy (p : PeriodicLatticePlaquette L) :
    Continuous fun y => reHolonomy (U y) p := by
  unfold reHolonomy
  exact continuous_const.smul ((contY_holonomyElem hU p).add (contY_holonomyElemInv hU p))

theorem contY_imHolonomy (p : PeriodicLatticePlaquette L) :
    Continuous fun y => imHolonomy (U y) p := by
  unfold imHolonomy
  exact continuous_const.smul ((contY_holonomyElem hU p).sub (contY_holonomyElemInv hU p))

theorem contY_RMap (e : PeriodicLatticeEdge L) (X : SuTwo) :
    Continuous fun y => ((RMap (U y e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => ((RMap (U y e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ) *
        star ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y
    exact AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply (U y e) X
  rw [this]
  exact ((hU e).matrix_mul continuous_const).matrix_mul (hU e).star

theorem contY_curlMat (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun y => curlMatLM (U y) p A := by
  simp only [curlMatLM_apply]
  unfold curlValueCovariant
  simp only [Submodule.coe_add, Submodule.coe_sub]
  exact (((continuous_const.add (contY_RMap hU _ _)).sub (contY_RMap hU _ _)).sub
    continuous_const)

theorem contY_a1 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun y => a1LM (U y) p A := by
  show Continuous fun y =>
    -(bondMatRLM (U y (p.1, p.2.1.2)) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) A)
  simp only [bondMatRLM_apply]
  exact (contY_RMap hU _ _).neg

theorem contY_a4 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun y => a4LM (U y) p A := by
  show Continuous fun y =>
    bondMatRLM (U y (p.1, p.2.1.1)) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) A
  simp only [bondMatRLM_apply]
  exact contY_RMap hU _ _

omit hU in
theorem contY_tr_re3 {f g h : Y → Matrix (Fin 2) (Fin 2) ℂ} (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) :
    Continuous fun y => (Matrix.trace (f y * g y * h y)).re :=
  Complex.continuous_re.comp (((hf.matrix_mul hg).matrix_mul hh).matrix_trace)

theorem contY_bilPlaq (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    Continuous fun y => bilPlaq (U y) p A B := by
  simp only [bilPlaq_atoms]
  have hI : ∀ {f : Y → Matrix (Fin 2) (Fin 2) ℂ}, Continuous f →
      Continuous fun y => smulILM (f y) := by
    intro f hf
    exact continuous_const.smul hf
  have b1A : Continuous fun y => b1LM (U y) p A := hI (contY_a1 hU p A)
  have b4B : Continuous fun y => b4LM (U y) p B := hI (contY_a4 hU p B)
  have hre := contY_reHolonomy hU p
  have him := contY_imHolonomy hU p
  have hcA : Continuous fun y => smulILM (curlMatLM (U y) p A) := hI (contY_curlMat hU p A)
  have hcB : Continuous fun y => smulILM (curlMatLM (U y) p B) := hI (contY_curlMat hU p B)
  have k : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), Continuous fun _ : Y => M :=
    fun M => continuous_const
  refine ((((((contY_tr_re3 hcA hcB (hre.sub (k 1))).add
    ((contY_tr_re3 (hI b1A) (k _) him).sub (contY_tr_re3 (k _) b1A him))).add
    ((contY_tr_re3 (hI b1A) (k _) him).sub (contY_tr_re3 (k _) b1A him))).add
    ((contY_tr_re3 (hI b1A) b4B him).sub (contY_tr_re3 (hI b4B) b1A him))).add
    ((contY_tr_re3 (k _) (k _) him).sub (contY_tr_re3 (k _) (k _) him))).add
    ((contY_tr_re3 (k _) b4B him).sub (contY_tr_re3 (hI b4B) (k _) him))).add
    ((contY_tr_re3 (k _) b4B him).sub (contY_tr_re3 (hI b4B) (k _) him))

open Classical in
theorem contY_deltaPrimeBil (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    Continuous fun y => deltaPrimeBilNormLoc (U y) P A B := by
  have h : ∀ A B : Bond L → SuTwo, Continuous fun y => deltaPrimeBilRawLoc (U y) P A B := by
    intro A B
    simp only [deltaPrimeBilRawLoc_apply]
    exact continuous_finsetSum _ (fun p _ => by
      by_cases hp : p ∈ P
      · simp only [hp, if_true]; exact contY_bilPlaq hU p A B
      · simp only [hp, if_false]; exact continuous_const)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  exact continuous_const.mul (continuous_const.mul ((h A B).add (h B A)))

open Classical in
theorem contY_curlInner (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    Continuous fun w =>
      (inner ℝ (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U w) x))
        (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U w) y)) : ℝ) := by
  simp only [PiLp.inner_apply]
  refine continuous_finsetSum _ (fun p _ => ?_)
  simp only [plaqMask_apply]
  by_cases hp : p ∈ P
  · simp only [hp, if_true]
    show Continuous fun w => AdalyFormal.Balaban.SuTwoInner.hsInner
      (curlValueCovariant (U w) (WithLp.ofLp x) p) (curlValueCovariant (U w) (WithLp.ofLp y) p)
    unfold AdalyFormal.Balaban.SuTwoInner.hsInner
    refine continuous_const.mul (Complex.continuous_re.comp ?_)
    exact ((contY_curlMat hU p (WithLp.ofLp x)).matrix_mul
      (contY_curlMat hU p (WithLp.ofLp y))).matrix_trace
  · simp only [hp, if_false, inner_zero_left]
    exact continuous_const

theorem contY_inner_delta (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    Continuous fun w => (inner ℝ x (deltaKLocCLM (U w) P y) : ℝ) := by
  simp only [inner_deltaKLocCLM]
  exact (contY_curlInner hU P x y).add (contY_deltaPrimeBil hU P _ _)

end

theorem contY_deltaKLocCLM {U : Y → PeriodicLinkConfiguration SU2m L} (hU : ContFamY U)
    (P : Set (PeriodicLatticePlaquette L)) : Continuous fun w => deltaKLocCLM (U w) P :=
  AdalyFormal.D1Literal.continuous_clm_of_inner (fun x y => contY_inner_delta hU P x y)

end Param

#print axioms AnFam
#print axioms an_inner_delta
#print axioms anM_uMat
#print axioms anFam_Uth
#print axioms ContFamY
#print axioms contY_deltaKLocCLM

#print axioms an_inv_coe
#print axioms an_holonomyElem
#print axioms an_holonomyElemInv
#print axioms an_reHolonomy
#print axioms an_imHolonomy
#print axioms an_RMap
#print axioms an_curlMat
#print axioms an_a1
#print axioms an_a4
#print axioms an_bilPlaq
#print axioms an_deltaPrimeBil
#print axioms an_curlInner
#print axioms contY_inv_coe
#print axioms contY_holonomyElem
#print axioms contY_holonomyElemInv
#print axioms contY_reHolonomy
#print axioms contY_imHolonomy
#print axioms contY_RMap
#print axioms contY_curlMat
#print axioms contY_a1
#print axioms contY_a4
#print axioms contY_tr_re3
#print axioms contY_bilPlaq
#print axioms contY_deltaPrimeBil
#print axioms contY_curlInner
#print axioms contY_inner_delta

end AdalyFormal.Round9.Guarded.QualitativeR2

/-! ## The actual operators: canonical vacuum crossings, and the reduced premise

Everything below concerns the actual pinned assemblies of the round-4/5 dilated family.
* Along an analytic exterior path every matrix coefficient of the actual carrier is
  real-analytic in the path parameter (frozen exterior path formula and the analytic
  plaquette chain above), so its non-units are isolated as soon as it is a unit somewhere.
* At the trivial configuration the all-plaquette carrier dominates the localized one, which is
  positive semidefinite, and a unit at every large scale and radius by the FROZEN localized
  theorem `M2RightInv.p428Target8`.  So the vacuum carrier of the exterior twist is positive
  definite at angle `0`; round 5 gives a negative direction at angle `π`.
* Hence at every large scale and radius the vacuum twist has a canonical crossing (the end of
  its initial positive semidefinite interval) with positive definite carriers arbitrarily close
  before it and negative directions arbitrarily close after it, for the twist run forwards
  (`Uth t`) and backwards (`Uth (-t)`).  Round 9.1 assumed this; here it is proved.
* Joint continuity in curvature and angle follows from continuity in the curvature, at the
  untwisted angle, of the carrier and of the dressing `W`.
* The literal round-8 family may use negative angles.  A positive coupling on the backward
  side gives a pre-crossing separation there, so no post-crossing analysis is needed.
What remains unproved is soft regularity of the interior family at the flat interior and a
definite first-order coupling on the canonical vacuum kernel. -/
namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace
open Filter Topology
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
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.D1Literal (PSD)

/-! ### Analyticity in the exterior angle -/

/-- An analytic exterior path, a fixed profile and a fixed curvature give an analytic family. -/
theorem pathU_anFam (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) : AnFam (pathU q R V f ε) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [pathU, maskedU, if_pos he]
    exact hV e
  · simp only [pathU, maskedU, if_neg he]
    exact anM_const _

theorem uthPath_anFam (q R : ℕ) : AnFam (uthPath q R) := anFam_Uth _

/-- The frozen exterior twist run backwards. -/
noncomputable def uthPathNeg (q R : ℕ) : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun s => uthPath q R (-s)

theorem uthPathNeg_cont (q R : ℕ) : AdalyFormal.D1Literal.ContFam (uthPathNeg q R) :=
  fun e => (uthPath_cont q R e).comp continuous_neg

theorem uthPathNeg_anFam (q R : ℕ) : AnFam (uthPathNeg q R) := by
  intro e θ₀ i j
  have hn : AnalyticAt ℝ (fun θ : ℝ => -θ) θ₀ := by fun_prop
  exact AnalyticAt.comp (g := fun θ => ((uthPath q R θ e : AdalyFormal.D1Literal.SU2m) :
    Matrix (Fin 2) (Fin 2) ℂ) i j) (uthPath_anFam q R e (-θ₀) i j) hn

theorem uthPath_zero (q R : ℕ) : uthPath q R 0 = fun _ => 1 :=
  AdalyFormal.D1Literal.Uth_zero _

theorem uthPathNeg_zero (q R : ℕ) : uthPathNeg q R 0 = fun _ => 1 := by
  show uthPath q R (-0) = _
  rw [neg_zero]
  exact uthPath_zero q R

/-- Along an analytic exterior path, every matrix coefficient of the actual all-plaquette
carrier is real-analytic in the path parameter. -/
theorem pathA_anR {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ)
    (x y : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    AnR (fun t => ⟪x, pathA q R V f ε a t y⟫) := by
  have h : ∀ t, pathA q R V f ε a t = pathA q R V f ε a 0 +
      (pE (geomOf 2 1 (dilTower q R))).comp (((ContinuousLinearMap.adjoint
        (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε 0) Set.univ)).comp
          (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a))).comp
        (iE (geomOf 2 1 (dilTower q R)))) :=
    fun t => exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      a (dilLam q R) (pathU q R V f ε) (fun s e he => path_agrees q R V f ε s 0 e he) selAll t
  have he : ∀ t, ⟪x, pathA q R V f ε a t y⟫ = ⟪x, pathA q R V f ε a 0 y⟫ +
      (⟪Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a (iE (geomOf 2 1 (dilTower q R)) x),
          AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε t) Set.univ
            (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a
              (iE (geomOf 2 1 (dilTower q R)) y))⟫ -
        ⟪Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a (iE (geomOf 2 1 (dilTower q R)) x),
          AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε 0) Set.univ
            (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a
              (iE (geomOf 2 1 (dilTower q R)) y))⟫) := by
    intro t
    rw [h t]
    simp only [add_apply, ContinuousLinearMap.comp_apply, inner_add_right, pE_inner_right,
      ContinuousLinearMap.adjoint_inner_right, sub_apply, inner_sub_right]
  rw [funext he]
  exact (anR_const _).add
    ((an_inner_delta (pathU_anFam q R hV f ε) Set.univ _ _).sub (anR_const _))

/-- Isolated non-units along an analytic exterior path, at every curvature and profile. -/
theorem pathA_isolated {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ) {t₀ : ℝ}
    (hu : IsUnit (pathA q R V f ε a t₀)) (t : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (pathA q R V f ε a s) :=
  isUnit_punctured (fun x y θ₀ => pathA_anR hq hR hroom hV f ε a x y θ₀) hu t

/-- The corrected carrier along an analytic exterior path also has isolated non-units (the
correction does not depend on the exterior). -/
theorem pathC_isolated {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ) {t₀ : ℝ}
    (hu : IsUnit (pathA q R V f ε a t₀ - pathD q R V f ε a t₀)) (t : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η →
      IsUnit (pathA q R V f ε a s - pathD q R V f ε a s) := by
  have hD : ∀ s, pathD q R V f ε a s = pathD q R V f ε a 0 :=
    fun s => pathD_constant hq hR hroom V f ε a s
  have hu' : IsUnit (pathA q R V f ε a t₀ - pathD q R V f ε a 0) := by rw [← hD t₀]; exact hu
  obtain ⟨η, hη, hb⟩ := isUnit_punctured (A := fun s => pathA q R V f ε a s - pathD q R V f ε a 0)
    (fun x y θ₀ => by
      have e : (fun θ => ⟪x, (pathA q R V f ε a θ - pathD q R V f ε a 0) y⟫) =
          fun θ => ⟪x, pathA q R V f ε a θ y⟫ - ⟪x, pathD q R V f ε a 0 y⟫ := by
        funext θ; rw [sub_apply, inner_sub_right]
      rw [e]
      exact (pathA_anR hq hR hroom hV f ε a x y θ₀).fun_sub analyticAt_const) hu' t
  exact ⟨η, hη, fun s hs hst => by rw [hD s]; exact hb s hs hst⟩

/-! ### The vacuum carrier at angle zero is positive definite -/

theorem inner_Ginv_dataS (sD sJ : PlaqSel) (P : IngrBParams) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS sD sJ P).Ginv x⟫ =
      ⟪Wop P.G P.U P.a (iE P.G x), AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (sD _ P.G)
        (Wop P.G P.U P.a (iE P.G x))⟫ + ‖(dataS sD sJ P).T x‖ ^ 2 +
      ⟪x, (dataS sD sJ P).Mass x⟫ := by
  have hD : ⟪x, (dataS sD sJ P).Dpi x⟫ = ⟪Wop P.G P.U P.a (iE P.G x),
      AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (sD _ P.G) (Wop P.G P.U P.a (iE P.G x))⟫ := by
    show ⟪x, ((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) x⟫ = _
    simp only [ContinuousLinearMap.comp_apply, DpiFullS, DeltaS]
    rw [pE_inner_right, ContinuousLinearMap.adjoint_inner_right]
  rw [BaseDataS.inner_Ginv, hD]

/-- At the trivial background the plaquette Hessian is monotone in the plaquette set. -/
theorem flat_delta_le_univ {L : PeriodicLatticeExtent} (P : Set (PeriodicLatticePlaquette L))
    (y : BondFnL2 L) :
    ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM (fun _ => 1) P y⟫ ≤
      ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM (fun _ => 1) Set.univ y⟫ := by
  have h1 : AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) P y y = 0 :=
    AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc_trivialU P _ _
  have h2 : AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) Set.univ y y = 0 :=
    AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc_trivialU Set.univ _ _
  change ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) P y⟫ ≤
    ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) Set.univ y⟫
  rw [AdalyFormal.StatementLaneR6.inner_deltaKLocCLM,
    AdalyFormal.StatementLaneR6.inner_deltaKLocCLM, h1, h2, add_zero, add_zero,
    AdalyFormal.StatementLaneR6.plaqMask_univ]
  simp only [PiLp.inner_apply, AdalyFormal.StatementLaneR6.plaqMask_apply]
  refine Finset.sum_le_sum (fun p _ => ?_)
  by_cases hp : p ∈ P
  · simp only [hp, if_true, le_refl]
  · simp only [hp, if_false, inner_zero_left]
    exact real_inner_self_nonneg

theorem mass_nonneg_dataS (sD sJ : PlaqSel) (P : IngrBParams) (ha : 0 ≤ P.a)
    (x : ↥(bondSupp P.G)) : 0 ≤ ⟪x, (dataS sD sJ P).Mass x⟫ := by
  show 0 ≤ ⟪x, ((pE P.G).comp ((MassFull P.G P.a P.sector).comp (iE P.G))) x⟫
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, pE_inner_right,
    inner_MassFull]
  refine Finset.sum_nonneg (fun p _ => ?_)
  have h1 : (0 : ℝ) ≤ (P.G.ell : ℝ) ^ (p.1 : ℕ) := pow_nonneg (Nat.cast_nonneg _) _
  exact mul_nonneg (mul_nonneg ha h1) (sq_nonneg _)

/-- At the trivial background the localized carrier is positive semidefinite. -/
theorem Ginv_loc_psd_flat (P : IngrBParams) (hU : P.U = fun _ => 1) (ha : 0 ≤ P.a) :
    PSD (dataS selIn selIn P).Ginv := by
  intro x
  rw [inner_Ginv_dataS]
  have h1 : 0 ≤ ⟪Wop P.G P.U P.a (iE P.G x), AdalyFormal.StatementLaneR6.deltaKLocCLM P.U
      (selIn _ P.G) (Wop P.G P.U P.a (iE P.G x))⟫ := by
    generalize Wop P.G P.U P.a (iE P.G x) = y
    rw [hU]
    exact AdalyFormal.StatementLaneR6.deltaKLocCLM_flat_nonneg _ y
  have h2 := mass_nonneg_dataS selIn selIn P ha x
  have h3 := sq_nonneg ‖(dataS selIn selIn P).T x‖
  linarith

/-- At the trivial background the all-plaquette carrier dominates the localized one. -/
theorem Ginv_loc_le_all_flat (P : IngrBParams) (hU : P.U = fun _ => 1)
    (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selIn selIn P).Ginv x⟫ ≤ ⟪x, (dataS selAll selAll P).Ginv x⟫ := by
  rw [inner_Ginv_dataS, inner_Ginv_dataS]
  have hT : (dataS selIn selIn P).T = (dataS selAll selAll P).T := rfl
  have hM : (dataS selIn selIn P).Mass = (dataS selAll selAll P).Mass := rfl
  rw [hT, hM]
  have key : ∀ y, ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (selIn _ P.G) y⟫ ≤
      ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (selAll _ P.G) y⟫ := by
    intro y
    rw [hU]
    exact flat_delta_le_univ _ y
  linarith [key (Wop P.G P.U P.a (iE P.G x))]

/-- A unit localized carrier at the trivial background makes the all-plaquette carrier
positive definite. -/
theorem Ginv_all_pd_flat (P : IngrBParams) (hU : P.U = fun _ => 1) (ha : 0 ≤ P.a)
    (hu : IsUnit (dataS selIn selIn P).Ginv) :
    ∀ x, x ≠ 0 → 0 < ⟪x, (dataS selAll selAll P).Ginv x⟫ := by
  intro x hx
  have h1 := pos_of_psd_unit _ ((dataS selIn selIn P).Ginv_symm (dataS_laws selIn selIn P))
    (Ginv_loc_psd_flat P hU ha) hu x hx
  exact lt_of_lt_of_le h1 (Ginv_loc_le_all_flat P hU x)

/-- The trivial configuration of the dilated geometry, mass `1`. -/
noncomputable def flatP (q R : ℕ) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R)

theorem dilU_flat (q R : ℕ) : dilU q R 0 (fun _ => 1) = fun _ => 1 := by
  classical
  funext e
  simp only [dilU, ite_self, Ug_zero]

/-- **The frozen localized theorem at the trivial configuration.**  At every large scale and
every large even radius the localized carrier of the trivial configuration is a unit
(`M2RightInv.p428Target8`, through the instance inequality and `WellDefAt_loc_of_inst`). -/
theorem flat_loc_unit_eventually :
    ∃ j₁ : ℕ, ∀ j : ℕ, j₁ ≤ j → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → 2 ∣ R → 18 ≤ R →
      IsUnit (dataS selIn selIn (flatP (2^j) R)).Ginv := by
  obtain ⟨m₂, -, hmm⟩ := (AdalyFormal.D1Literal.pin_target8_iff.mpr
    AdalyFormal.M2RightInv.p428Target8 : AdalyFormal.D1Literal.P428Target8S
      AdalyFormal.D1Literal.selIn AdalyFormal.D1Literal.selIn) 2 le_rfl 1 one_pos
  refine ⟨m₂, fun j hj => ?_⟩
  obtain ⟨R₂, hR₂⟩ := hmm (j+1) (by omega)
  refine ⟨R₂, fun R hR hR2 hR18 => ?_⟩
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hcore⟩ := hR₂ R hR
  let q := 2^j
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(j+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let α : ℝ := min (a₀/(24*q)) 1/2
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ) * ((2^(j+1) : ℕ) : ℝ) * α ≤ a₀ := by
    have hm : α ≤ a₀/(24*q) := by
      have hp : 0 < min (a₀/(24*q)) 1 := by positivity
      dsimp [α]; linarith [min_le_left (a₀/(24*q)) 1]
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 24*q)).mp hm
    rw [hpow]; push_cast; nlinarith
  have hT : TorusOK 2 (2^(j+1)) (dilLu q R) := by rw [hpow]; exact dil_torus hq R
  have hS : Admissible 2 (2^(j+1)) R 1 (dilTower q R) := by
    rw [hpow]; exact dil_admissible hq hR2
  have hL : LambdaOK2 2 (2^(j+1)) R 1 (dilTower q R) (dilLam q R) := by
    rw [hpow]; exact dil_lambda hq hR2
  have hreg := dil_regular hq hR2 hα (ε := 0) (by rw [abs_zero]; positivity) (fun _ => 1)
  rw [dilU_flat] at hreg
  have hcl : ClassCoupled 2 (2^(j+1)) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (fun _ => 1) := by
    rw [hpow]; exact ⟨dil_coverage hq hR2 (by omega), hreg⟩
  have hloc := hcore 1 le_rfl (dilLu q R) α hα hcap hT (dilTower q R) hS (dilLam q R) hL _ hcl
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR2
  exact (AdalyFormal.D1Guarded.WellDefAt_loc_of_inst 2 1 (by norm_num) 1 zero_le_one
    (dilLu q R) γ₀ hγ (dilTower q R) (dilLam q R) _ (dilBt hq R) hBt1 hBt2 hE hloc).1

theorem pathU_flat_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    pathU q R V f 0 0 = fun _ => 1 := by
  classical
  funext e
  simp only [pathU, maskedU, hV0, zero_mul, Ug_zero, ite_self]

theorem vacA_zero_flat (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) : vacA q R V 1 0 = (dataS selAll selAll (flatP q R)).Ginv := by
  unfold vacA pathA pathP flatP
  rw [pathU_flat_base q R hV0 (fun _ => 0)]

/-- The vacuum carrier is positive definite at the base point of an exterior path that starts
at the trivial field, as soon as the localized carrier of the trivial configuration is a
unit. -/
theorem vacA_pd_zero {q R : ℕ} {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv) :
    ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 0 x⟫ := by
  rw [vacA_zero_flat q R hV0]
  exact Ginv_all_pd_flat (flatP q R) rfl zero_le_one hloc

/-! ### Negative endpoints and the canonical crossing -/

theorem vacA_uth_pi_negative {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q)) :
    ∃ w, ⟪w, vacA q R (uthPath q R) 1 Real.pi w⟫ < 0 := by
  obtain ⟨w, hw⟩ := twistA_pi_negative hq hR hroom 0
  refine ⟨w, ?_⟩
  rw [twistA_eq_path, pathA_zero] at hw
  exact hw

theorem uθ_neg_pi : AdalyFormal.D1Literal.uθ (-Real.pi) = AdalyFormal.D1Literal.uθ Real.pi := by
  apply Subtype.ext
  show AdalyFormal.D1Literal.uMat (-Real.pi) = AdalyFormal.D1Literal.uMat Real.pi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Complex.exp_neg, Complex.exp_pi_mul_I]

theorem uthPath_neg_pi (q R : ℕ) : uthPath q R (-Real.pi) = uthPath q R Real.pi := by
  funext e
  simp only [uthPath, AdalyFormal.D1Literal.Uth, uθ_neg_pi]

theorem vacA_uthNeg_pi_negative {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) : ∃ w, ⟪w, vacA q R (uthPathNeg q R) 1 Real.pi w⟫ < 0 := by
  obtain ⟨w, hw⟩ := vacA_uth_pi_negative hq hR hroom
  refine ⟨w, ?_⟩
  have hU : pathU q R (uthPathNeg q R) (fun _ => 0) 0 Real.pi =
      pathU q R (uthPath q R) (fun _ => 0) 0 Real.pi := by
    show maskedU q R _ (uthPath q R (-Real.pi)) = maskedU q R _ (uthPath q R Real.pi)
    rw [uthPath_neg_pi]
  have h : vacA q R (uthPathNeg q R) 1 Real.pi = vacA q R (uthPath q R) 1 Real.pi := by
    unfold vacA pathA pathP
    rw [hU]
  rw [h]
  exact hw

/-- The canonical crossing angle of the vacuum carrier along an exterior path: the end of its
initial positive semidefinite interval in `[0, π]`. -/
noncomputable def vacEdge (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : ℝ :=
  psdEdge (vacA q R V 1) 0 Real.pi

/-- The vacuum carrier along `V` crosses at `ts`: it is positive semidefinite and singular
there, positive definite at angles arbitrarily close before `ts`, and has a negative
direction at angles arbitrarily close after `ts`. -/
def VacuumCrossesAt (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (ts : ℝ) : Prop :=
  0 < ts ∧ ts < Real.pi ∧ PSD (vacA q R V 1 ts) ∧ ¬ IsUnit (vacA q R V 1 ts) ∧
    (∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 t₀ x⟫) ∧
    (∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w, ⟪w, vacA q R V 1 t₁ w⟫ < 0)

/-- **The canonical vacuum crossing.**  Along a continuous, analytic exterior path whose vacuum
carrier is positive definite at `0` and has a negative direction at `π`, the vacuum carrier
crosses at `vacEdge`. -/
theorem vacuum_crossing {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hVc : AdalyFormal.D1Literal.ContFam V)
    (hVa : AnFam V) (hpd0 : ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 0 x⟫)
    (hneg : ∃ w, ⟪w, vacA q R V 1 Real.pi w⟫ < 0) :
    VacuumCrossesAt q R V (vacEdge q R V) := by
  obtain ⟨w, hw⟩ := hneg
  have hc : Continuous (vacA q R V 1) := pathA_continuous hq hR hroom hVc (fun _ => 0) 0 1
  have hs : ∀ t x y, ⟪vacA q R V 1 t x, y⟫ = ⟪x, vacA q R V 1 t y⟫ := by
    intro t x y
    exact (dataS selAll selAll (pathP q R V (fun _ => 0) 0 1 t)).Ginv_symm
      (dataS_laws selAll selAll _) x y
  have hiso : ∀ t, ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (vacA q R V 1 s) :=
    fun t => pathA_isolated hq hR hroom hVa (fun _ => 0) 0 1 (t₀ := 0) (unit_of_pd _ hpd0) t
  obtain ⟨h1, h2, h3, h4, -, h6, h7⟩ :=
    psdEdge_spec (vacA q R V 1) hc hs Real.pi_pos hpd0 w hw hiso
  exact ⟨h1, h2, h3, h4, h6, h7⟩

/-- **Unconditional.**  At every large scale and every large even radius the vacuum carrier of
the actual exterior twist crosses at its canonical angle, forwards and backwards. -/
theorem twist_vacuum_crossing :
    ∃ j₁ : ℕ, ∀ j : ℕ, j₁ ≤ j → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → 2 ∣ R → 18 ≤ R →
      VacuumCrossesAt (2^j) R (uthPath (2^j) R) (vacEdge (2^j) R (uthPath (2^j) R)) ∧
      VacuumCrossesAt (2^j) R (uthPathNeg (2^j) R) (vacEdge (2^j) R (uthPathNeg (2^j) R)) := by
  obtain ⟨j₁, hj₁⟩ := flat_loc_unit_eventually
  refine ⟨j₁, fun j hj => ?_⟩
  obtain ⟨R₁, hR₁⟩ := hj₁ j hj
  refine ⟨R₁, fun R hR hR2 hR18 => ?_⟩
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  have hloc := hR₁ R hR hR2 hR18
  exact ⟨vacuum_crossing hq hR2 hroom (uthPath_cont _ _) (uthPath_anFam _ _)
      (vacA_pd_zero (uthPath_zero _ _) hloc) (vacA_uth_pi_negative hq hR2 hroom),
    vacuum_crossing hq hR2 hroom (uthPathNeg_cont _ _) (uthPathNeg_anFam _ _)
      (vacA_pd_zero (uthPathNeg_zero _ _) hloc) (vacA_uthNeg_pi_negative hq hR2 hroom)⟩

/-- **Unconditional.**  At every curvature the non-units of the actual curved twist, and of its
corrected carrier, are isolated in the angle once the respective carrier is a unit somewhere. -/
theorem twist_isolated_nonunits {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    (ε : ℝ) :
    ((∃ t₀, IsUnit (twistA q R ε 1 t₀)) → ∀ t, ∃ η : ℝ, 0 < η ∧
      ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (twistA q R ε 1 s)) ∧
    ((∃ t₀, IsUnit (twistA q R ε 1 t₀ - twistD q R ε 1 t₀)) → ∀ t, ∃ η : ℝ, 0 < η ∧
      ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (twistA q R ε 1 s - twistD q R ε 1 s)) := by
  constructor
  · rintro ⟨t₀, hu⟩ t
    rw [twistA_eq_path] at hu
    obtain ⟨η, hη, hb⟩ := pathA_isolated hq hR hroom (uthPath_anFam q R) (dilMask q R) ε 1 hu t
    exact ⟨η, hη, fun s hs hst => by rw [twistA_eq_path]; exact hb s hs hst⟩
  · rintro ⟨t₀, hu⟩ t
    rw [twistA_eq_path, twistD_eq_path] at hu
    obtain ⟨η, hη, hb⟩ := pathC_isolated hq hR hroom (uthPath_anFam q R) (dilMask q R) ε 1 hu t
    exact ⟨η, hη, fun s hs hst => by rw [twistA_eq_path, twistD_eq_path]; exact hb s hs hst⟩

/-! ### Joint continuity from interior continuity -/

theorem uMat_continuous' : Continuous fun θ : ℝ => AdalyFormal.D1Literal.uMat θ := by
  unfold AdalyFormal.D1Literal.uMat
  refine continuous_matrix (fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- The abelian link `Ug t = exp(i t σ₃)` is `diag(e^{it}, e^{-it})`. -/
theorem Ug_coe_uMat (t : ℝ) :
    ((Ug t : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      AdalyFormal.D1Literal.uMat t := by
  show NormedSpace.exp (Xm t) = _
  have hX : Xm t = Matrix.diagonal ![(t : ℂ) * Complex.I, -((t : ℂ) * Complex.I)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Xm, sig, Matrix.diagonal]
  rw [hX, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.diagonal, ← Complex.exp_eq_exp_ℂ]

/-- Path families are jointly continuous in (curvature, path parameter), link by link. -/
theorem pathU_contFamY (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContFamY (fun p : ℝ × ℝ => pathU q R V f p.1 p.2) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [pathU, maskedU, if_pos he]
    exact (hV e).comp continuous_snd
  · simp only [pathU, maskedU, if_neg he, Ug_coe_uMat]
    exact uMat_continuous'.comp (continuous_fst.mul continuous_const)

/-- Joint continuity of the carrier in (curvature, angle) at zero curvature, from continuity in
the curvature of the carrier at the path's base point and of the dressing `W` there. -/
theorem pathA_jointly_continuousAt {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (hA0 : ContinuousAt (fun ε : ℝ => pathA q R V f ε 1 0) 0)
    (hW0 : ContinuousAt (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) 1) 0)
    (t : ℝ) : ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) (0, t) := by
  let G := geomOf 2 1 (dilTower q R)
  let Wf : ℝ → BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ] BondFnL2 (scaleUp 2 1 (dilLu q R)) :=
    fun ε => Wop G (pathU q R V f ε 0) 1
  let Δf : ℝ × ℝ → BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ] BondFnL2 (scaleUp 2 1 (dilLu q R)) :=
    fun p => AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f p.1 p.2) Set.univ
  have hpath : ∀ p : ℝ × ℝ, pathA q R V f p.1 1 p.2 = pathA q R V f p.1 1 0 +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wf p.1)).comp
        ((Δf p - Δf (p.1, 0)).comp (Wf p.1))).comp (iE G)) := fun p =>
    exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      1 (dilLam q R) (pathU q R V f p.1) (fun s e he => path_agrees q R V f p.1 s 0 e he)
      selAll p.2
  rw [show (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) = fun p => pathA q R V f p.1 1 0 +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wf p.1)).comp
        ((Δf p - Δf (p.1, 0)).comp (Wf p.1))).comp (iE G)) from funext hpath]
  have hΔ : Continuous Δf := contY_deltaKLocCLM (pathU_contFamY q R hV f) _
  have hA : ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 0) (0, t) :=
    ContinuousAt.comp (f := Prod.fst) (x := ((0 : ℝ), t)) hA0 continuousAt_fst
  have hW : ContinuousAt (fun p : ℝ × ℝ => Wf p.1) (0, t) :=
    ContinuousAt.comp (f := Prod.fst) (x := ((0 : ℝ), t)) hW0 continuousAt_fst
  have hadj : Continuous (fun M : BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R)) => ContinuousLinearMap.adjoint M) :=
    (ContinuousLinearMap.adjoint : (BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R))) ≃ₗᵢ⋆[ℝ] (BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R)))).continuous
  have hWa : ContinuousAt (fun p : ℝ × ℝ => ContinuousLinearMap.adjoint (Wf p.1)) (0, t) :=
    hadj.continuousAt.comp hW
  have hD : ContinuousAt (fun p : ℝ × ℝ => Δf p - Δf (p.1, 0)) (0, t) :=
    hΔ.continuousAt.sub ((hΔ.comp (continuous_fst.prodMk continuous_const)).continuousAt)
  have hmid : ContinuousAt (fun p : ℝ × ℝ => (ContinuousLinearMap.adjoint (Wf p.1)).comp
      ((Δf p - Δf (p.1, 0)).comp (Wf p.1))) (0, t) := hWa.clm_comp (hD.clm_comp hW)
  have hout : Continuous fun M : BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R)) => (pE G).comp (M.comp (iE G)) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  exact hA.add (hout.continuousAt.comp hmid)

/-! ### The reduced premise: soft regularity of the interior family and the coupling -/

/-- The curved interior with the trivial exterior field. -/
noncomputable def bulkU (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  maskedU q R (fun e => ε * f e) (fun _ => 1)

noncomputable def bulkP (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)

/-- The actual all-plaquette carrier of the interior family. -/
noncomputable def bulkA (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selAll selAll (bulkP q R f ε)).Ginv

/-- The actual localized correction of the interior family. -/
noncomputable def bulkD (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selIn selIn (bulkP q R f ε)).Delta2 (dataS_laws selIn selIn _)

/-- **Soft regularity of the interior family** `ε ↦ maskedU (ε f) 1` (curved interior, trivial
exterior) at the flat interior: the carrier and the dressing `W` are continuous at `ε = 0`
and the correction has derivative `De` there.  No exterior angle appears.  NOT proved here. -/
def InteriorSoft (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ContinuousAt (fun ε : ℝ => bulkA q R f ε) 0 ∧
  ContinuousAt (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (bulkU q R f ε) 1) 0 ∧
  HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0

theorem pathU_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    pathU q R V f ε 0 = bulkU q R f ε := by
  unfold pathU bulkU
  rw [hV0]

theorem pathP_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    pathP q R V f ε 1 0 = bulkP q R f ε := by
  unfold pathP bulkP
  rw [pathU_base q R hV0 f ε]

theorem pathA_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    pathA q R V f ε 1 0 = bulkA q R f ε := by
  unfold pathA pathP bulkA bulkP
  rw [pathU_base q R hV0 f ε]

theorem pathD_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    pathD q R V f ε 1 0 = bulkD q R f ε := by
  have hd : dataS selIn selIn (pathP q R V f ε 1 0) = dataS selIn selIn (bulkP q R f ε) := by
    unfold pathP bulkP
    rw [pathU_base q R hV0 f ε]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

theorem joint_of_soft {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hVc : AdalyFormal.D1Literal.ContFam V)
    (hV0 : V 0 = fun _ => 1) {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) (t : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) (0, t) := by
  obtain ⟨hA, hW, -⟩ := hs
  refine pathA_jointly_continuousAt hq hR hroom hVc f ?_ ?_ t
  · rw [show (fun ε : ℝ => pathA q R V f ε 1 0) = fun ε => bulkA q R f ε
      from funext (pathA_base q R hV0 f)]
    exact hA
  · rw [show (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) 1) =
        fun ε => Wop (geomOf 2 1 (dilTower q R)) (bulkU q R f ε) 1
      from funext (fun ε => by rw [pathU_base q R hV0 f ε])]
    exact hW

theorem deriv_of_soft {q R : ℕ} {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) : HasDerivAt (fun ε : ℝ => pathD q R V f ε 1 0) De 0 := by
  rw [show (fun ε : ℝ => pathD q R V f ε 1 0) = fun ε => bulkD q R f ε
    from funext (pathD_base q R hV0 f)]
  exact hs.2.2

/-- The first-order coefficient is definite, of either sign, on the kernel of the vacuum carrier
at the canonical crossing of `V`.  NOT proved here. -/
def CanonicalCoupling (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ((∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) ∨
      (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫))

/-- The first-order coefficient is positive definite on the kernel of the vacuum carrier at the
canonical crossing of `V`.  NOT proved here. -/
def CanonicalCouplingPos (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫

/-- Soft regularity and a definite coupling give round 9.1's `VacuumCoupling`; the vacuum
crossing clauses are now theorems. -/
theorem vacuumCoupling_of_soft {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hVc : AdalyFormal.D1Literal.ContFam V)
    (hVa : AnFam V) (hV0 : V 0 = fun _ => 1)
    (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv)
    (hneg : ∃ w, ⟪w, vacA q R V 1 Real.pi w⟫ < 0)
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) (hc : CanonicalCoupling q R V De) : VacuumCoupling q R V f := by
  obtain ⟨-, -, -, -, hbef, haft⟩ :=
    vacuum_crossing hq hR hroom hVc hVa (vacA_pd_zero hV0 hloc) hneg
  obtain ⟨c, hc0, hsign⟩ := hc
  exact ⟨vacEdge q R V, c, De, hbef, haft,
    ⟨1, one_pos, fun t _ => joint_of_soft hq hR hroom hVc hV0 hs t⟩,
    deriv_of_soft hV0 hs, hc0, hsign⟩

/-- Pre-crossing separation at every small curvature from soft regularity and a positive
coupling at the canonical crossing (the profile itself, no reflection). -/
theorem pathSeparation_eventually_of_soft {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hVc : AdalyFormal.D1Literal.ContFam V) (hVa : AnFam V) (hV0 : V 0 = fun _ => 1)
    (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv)
    (hneg : ∃ w, ⟪w, vacA q R V 1 Real.pi w⟫ < 0)
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) (hc : CanonicalCouplingPos q R V De) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSeparation q R V f ε := by
  obtain ⟨-, -, -, -, hbef, haft⟩ :=
    vacuum_crossing hq hR hroom hVc hVa (vacA_pd_zero hV0 hloc) hneg
  obtain ⟨c, hc0, hpos⟩ := hc
  have h3 : 3 ≤ R * (2*q) := by omega
  have hj : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - vacEdge q R V| < η₀ → ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ ∀ ε s : ℝ, |ε| < r → |s - t| < r →
        ‖pathA q R V f ε 1 s - pathA q R V f 0 1 t‖ < δ :=
    ⟨1, one_pos, fun t _ => metric_of_continuousAt (fun ε t => pathA q R V f ε 1 t) t
      (joint_of_soft hq hR hroom hVc hV0 hs t)⟩
  have hDx := expansion_of_hasDerivAt (fun ε => pathD q R V f ε 1 0) De
    (pathD_zero hq hR h3 V f 1 0) (deriv_of_soft hV0 hs)
  refine eventually_pathSeparation_pos hq hR hroom hVc f (vacEdge q R V) c De hbef haft hj ?_
    hc0 hpos
  intro μ hμ
  obtain ⟨r, hr, hb⟩ := hDx μ hμ
  refine ⟨r, hr, fun ε hε hεr => ?_⟩
  have h1 := hb ε (by rw [abs_of_pos hε]; exact hεr)
  rw [abs_of_pos hε] at h1
  exact h1

theorem twistSeparation_of_uth {q R : ℕ} {ε : ℝ}
    (h : PathSeparation q R (uthPath q R) (dilMask q R) ε) : TwistSeparation q R ε := by
  obtain ⟨t, hu, hnu⟩ := h
  refine ⟨t, ?_, ?_⟩
  · rw [twistA_eq_path]; exact hu
  · rw [twistA_eq_path, twistD_eq_path]; exact hnu

/-- A separation of the backward twist is a separation of the literal family at a negative
angle. -/
theorem twistSeparation_of_uthNeg {q R : ℕ} {ε : ℝ}
    (h : PathSeparation q R (uthPathNeg q R) (dilMask q R) ε) : TwistSeparation q R ε := by
  obtain ⟨s, hu, hnu⟩ := h
  refine ⟨-s, ?_, ?_⟩
  · rw [twistA_eq_path]; exact hu
  · rw [twistA_eq_path, twistD_eq_path]; exact hnu

/-! ### The literal round-8 target -/

/-- **The remaining premise for the literal round-8 family at `(q,R)`.**  Soft regularity of
the single-defect interior family at the flat interior, and a positive first-order coupling on
the kernel of the vacuum carrier at the canonical crossing of the twist run forwards OR run
backwards.  NOT proved here. -/
def TwistSoftCoupling (q R : ℕ) : Prop :=
  ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
    InteriorSoft q R (dilMask q R) De ∧
      (CanonicalCouplingPos q R (uthPath q R) De ∨ CanonicalCouplingPos q R (uthPathNeg q R) De)

theorem twistSeparation_eventually {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv) (h : TwistSoftCoupling q R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → TwistSeparation q R ε := by
  have hroom : 17*2 ≤ R*(2*q) := by nlinarith
  obtain ⟨De, hs, hc | hc⟩ := h
  · obtain ⟨ε₀, hε₀, hall⟩ := pathSeparation_eventually_of_soft hq hR hroom (uthPath_cont q R)
      (uthPath_anFam q R) (uthPath_zero q R) hloc (vacA_uth_pi_negative hq hR hroom) hs hc
    exact ⟨ε₀, hε₀, fun ε h1 h2 => twistSeparation_of_uth (hall ε h1 h2)⟩
  · obtain ⟨ε₀, hε₀, hall⟩ := pathSeparation_eventually_of_soft hq hR hroom
      (uthPathNeg_cont q R) (uthPathNeg_anFam q R) (uthPathNeg_zero q R) hloc
      (vacA_uthNeg_pi_negative hq hR hroom) hs hc
    exact ⟨ε₀, hε₀, fun ε h1 h2 => twistSeparation_of_uthNeg (hall ε h1 h2)⟩

/-- The cofinal form of the reduced premise, with the pinned quantifiers. -/
def CofinalTwistSoftCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    TwistSoftCoupling (2^j) R

/-- **Main reduction (literal target).**  The reduced premise implies round 8's
`CofinalTwistSeparation`.  The vacuum crossing, the joint continuity in curvature and angle
and the sign of the separation side are theorems; the premise keeps only interior soft
regularity and a positive coupling on one of the two canonical vacuum kernels. -/
theorem cofinalTwistSeparation_of_cofinalTwistSoftCoupling (h : CofinalTwistSoftCoupling) :
    CofinalTwistSeparation := by
  obtain ⟨j₁, hj₁⟩ := flat_loc_unit_eventually
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h (max j₀ j₁)
  obtain ⟨R₁, hR₁⟩ := hj₁ j (le_trans (le_max_right _ _) hj)
  refine ⟨j, le_trans (le_max_left _ _) hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hsc⟩ := hRs (max R₀ R₁)
  refine ⟨R, le_trans (le_max_left _ _) hRR, hR, hR18, fun δ hδ => ?_⟩
  have hq : 0 < 2^j := by positivity
  obtain ⟨ε₀, hε₀, hall⟩ := twistSeparation_eventually hq hR hR18
    (hR₁ R (le_trans (le_max_right _ _) hRR) hR hR18) hsc
  have hm : 0 < min δ ε₀ := lt_min hδ hε₀
  exact ⟨min δ ε₀ / 2, by positivity, by linarith [min_le_left δ ε₀],
    hall (min δ ε₀ / 2) (by positivity) (by linarith [min_le_right δ ε₀])⟩

theorem goalNeg2_of_cofinalTwistSoftCoupling (h : CofinalTwistSoftCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_cofinalTwistSoftCoupling h)

theorem not_cofinalTwistSoftCoupling_of_goalPos1 (h : GoalPos1) : ¬ CofinalTwistSoftCoupling :=
  fun h' => goalNeg2_of_cofinalTwistSoftCoupling h' (goalPos2_iff_goalPos1.mpr h)

/-! ### Free profile, either sign -/

/-- **The weakest premise of this round at `(q,R)`.**  Some bounded interior profile whose
interior family is softly regular, with a definite first-order coupling (of either sign) on
the canonical vacuum kernel of the twist run forwards or backwards.  NOT proved here. -/
def PathSoftCoupling (q R : ℕ) : Prop :=
  ∃ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
    ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      InteriorSoft q R f De ∧
        (CanonicalCoupling q R (uthPath q R) De ∨ CanonicalCoupling q R (uthPathNeg q R) De)

def CofinalPathSoftCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    PathSoftCoupling (2^j) R

theorem pathSoftCoupling_of_twist {q R : ℕ} (h : TwistSoftCoupling q R) : PathSoftCoupling q R := by
  obtain ⟨De, hs, hc | hc⟩ := h
  · obtain ⟨c, hc0, hpos⟩ := hc
    exact ⟨dilMask q R, dilMask_bound q R, De, hs, Or.inl ⟨c, hc0, Or.inl hpos⟩⟩
  · obtain ⟨c, hc0, hpos⟩ := hc
    exact ⟨dilMask q R, dilMask_bound q R, De, hs, Or.inr ⟨c, hc0, Or.inl hpos⟩⟩

theorem cofinalPathSoftCoupling_of_twist (h : CofinalTwistSoftCoupling) :
    CofinalPathSoftCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, pathSoftCoupling_of_twist hv⟩

theorem cofinalVacuumCoupling_of_cofinalPathSoftCoupling (h : CofinalPathSoftCoupling) :
    CofinalVacuumCoupling := by
  obtain ⟨j₁, hj₁⟩ := flat_loc_unit_eventually
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h (max j₀ j₁)
  obtain ⟨R₁, hR₁⟩ := hj₁ j (le_trans (le_max_right _ _) hj)
  refine ⟨j, le_trans (le_max_left _ _) hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, f, hf, De, hs, hc⟩ := hRs (max R₀ R₁)
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  have hloc := hR₁ R (le_trans (le_max_right _ _) hRR) hR hR18
  rcases hc with hc | hc
  · exact ⟨R, le_trans (le_max_left _ _) hRR, hR, hR18, uthPath (2^j) R, uthPath_cont _ _, f, hf,
      vacuumCoupling_of_soft hq hR hroom (uthPath_cont _ _) (uthPath_anFam _ _)
        (uthPath_zero _ _) hloc (vacA_uth_pi_negative hq hR hroom) hs hc⟩
  · exact ⟨R, le_trans (le_max_left _ _) hRR, hR, hR18, uthPathNeg (2^j) R, uthPathNeg_cont _ _,
      f, hf, vacuumCoupling_of_soft hq hR hroom (uthPathNeg_cont _ _) (uthPathNeg_anFam _ _)
        (uthPathNeg_zero _ _) hloc (vacA_uthNeg_pi_negative hq hR hroom) hs hc⟩

/-- **Main reduction (weakest premise).** -/
theorem goalNeg2_of_cofinalPathSoftCoupling (h : CofinalPathSoftCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalVacuumCoupling (cofinalVacuumCoupling_of_cofinalPathSoftCoupling h)

theorem not_cofinalPathSoftCoupling_of_goalPos1 (h : GoalPos1) : ¬ CofinalPathSoftCoupling :=
  fun h' => goalNeg2_of_cofinalPathSoftCoupling h' (goalPos2_iff_goalPos1.mpr h)

#print axioms pathU_anFam
#print axioms uthPath_anFam
#print axioms uthPathNeg
#print axioms uthPathNeg_cont
#print axioms uthPathNeg_anFam
#print axioms uthPath_zero
#print axioms uthPathNeg_zero
#print axioms pathA_anR
#print axioms pathA_isolated
#print axioms pathC_isolated
#print axioms inner_Ginv_dataS
#print axioms flat_delta_le_univ
#print axioms mass_nonneg_dataS
#print axioms Ginv_loc_psd_flat
#print axioms Ginv_loc_le_all_flat
#print axioms Ginv_all_pd_flat
#print axioms flatP
#print axioms dilU_flat
#print axioms flat_loc_unit_eventually
#print axioms pathU_flat_base
#print axioms vacA_zero_flat
#print axioms vacA_pd_zero
#print axioms vacA_uth_pi_negative
#print axioms uθ_neg_pi
#print axioms uthPath_neg_pi
#print axioms vacA_uthNeg_pi_negative
#print axioms vacEdge
#print axioms VacuumCrossesAt
#print axioms vacuum_crossing
#print axioms twist_vacuum_crossing
#print axioms twist_isolated_nonunits
#print axioms uMat_continuous'
#print axioms Ug_coe_uMat
#print axioms pathU_contFamY
#print axioms pathA_jointly_continuousAt
#print axioms bulkU
#print axioms bulkP
#print axioms bulkA
#print axioms bulkD
#print axioms InteriorSoft
#print axioms pathU_base
#print axioms pathP_base
#print axioms pathA_base
#print axioms pathD_base
#print axioms joint_of_soft
#print axioms deriv_of_soft
#print axioms CanonicalCoupling
#print axioms CanonicalCouplingPos
#print axioms vacuumCoupling_of_soft
#print axioms pathSeparation_eventually_of_soft
#print axioms twistSeparation_of_uth
#print axioms twistSeparation_of_uthNeg
#print axioms TwistSoftCoupling
#print axioms twistSeparation_eventually
#print axioms CofinalTwistSoftCoupling
#print axioms cofinalTwistSeparation_of_cofinalTwistSoftCoupling
#print axioms goalNeg2_of_cofinalTwistSoftCoupling
#print axioms not_cofinalTwistSoftCoupling_of_goalPos1
#print axioms PathSoftCoupling
#print axioms CofinalPathSoftCoupling
#print axioms pathSoftCoupling_of_twist
#print axioms cofinalPathSoftCoupling_of_twist
#print axioms cofinalVacuumCoupling_of_cofinalPathSoftCoupling
#print axioms goalNeg2_of_cofinalPathSoftCoupling
#print axioms not_cofinalPathSoftCoupling_of_goalPos1

end AdalyFormal.Round9.Guarded.QualitativeR2

/-! ## The global gauge flip: the forward and backward twists are equivalent

The frozen gauge-covariance lane (`GaugeCov`, `M1GaugeW4`) proves that the localized data are
covariant under every gauge transformation, and that the plaquette Hessian is covariant for
every plaquette set; so the all-plaquette carrier is covariant as well (`Ginv_all_gauge`).  The
constant gauge transformation by `w = [[0,1],[-1,0]]` conjugates `diag(a, ā)` into `diag(ā, a)`:
it maps the curved twist at curvature `ε` and angle `t` to the curved twist at `-ε` and `-t`.
Hence the backward vacuum twist is unitarily equivalent to the forward one, the canonical
crossings coincide, and the first-order coupling changes sign between the two kernels.  A
coupling of EITHER sign on the forward kernel is therefore a positive coupling on one of the two
kernels, which is what the pre-crossing argument needs. -/
namespace AdalyFormal.Round9.Guarded.QualitativeR2

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
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.GaugeCov (adEL adBL adSL adBL_apply iE_adEL pE_adBL adjoint_intertwine
  bondEqv_gauge deltaKLocCLM_gauge)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.D1Literal (PSD)

/-! ### The all-plaquette carrier is gauge covariant -/

/-- The all-plaquette carrier at `U^γ`, applied to `Ad_γ x`, is `Ad_γ` of the carrier at `U`. -/
theorem Ginv_all_gauge {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (γ : GaugeFn (scaleUp ell k Lu))
    (x : ↥(bondSupp (geomOf ell k S))) :
    (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Ginv
        (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ginv x) := by
  have hB := bondEqv_gauge (gparams ell k Lu hell S U a Lam) γ
  have hD := hB.baseEqv
  have hW : ∀ z, Wop (geomOf ell k S) (periodicGaugeTransform γ U) a (adBL γ z) =
      adBL γ (Wop (geomOf ell k S) U a z) := fun z => hB.W z
  have hΔ : ∀ z, AdalyFormal.StatementLaneR6.deltaKLocCLM (periodicGaugeTransform γ U) Set.univ
      (adBL γ z) = adBL γ (AdalyFormal.StatementLaneR6.deltaKLocCLM U Set.univ z) :=
    fun z => deltaKLocCLM_gauge γ U Set.univ z
  have hDp : ∀ z, DpiFullS selAll (geomOf ell k S) (periodicGaugeTransform γ U) a (adBL γ z) =
      adBL γ (DpiFullS selAll (geomOf ell k S) U a z) := by
    intro z
    simp only [DpiFullS, DeltaS, selAll, ContinuousLinearMap.comp_apply]
    rw [hW, hΔ]
    exact adjoint_intertwine (adBL γ) (adBL γ) hW _
  have hDpi : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Dpi
      (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Dpi x) := by
    show pE (geomOf ell k S) (DpiFullS selAll (geomOf ell k S) (periodicGaugeTransform γ U) a
        (iE (geomOf ell k S) (adEL γ (geomOf ell k S) x))) =
      adEL γ (geomOf ell k S) (pE (geomOf ell k S)
        (DpiFullS selAll (geomOf ell k S) U a (iE (geomOf ell k S) x)))
    rw [iE_adEL, hDp, pE_adBL]
  have hT : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).T
      (adEL γ (geomOf ell k S) x) =
      adSL γ ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).T x) := hD.T x
  have hTs : ∀ s, (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a
      Lam)).Ts (adSL γ s) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ts s) :=
    hD.Ts
  have hM : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Mass
      (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Mass x) :=
    hD.Mass x
  simp only [BaseDataS.Ginv, add_apply, ContinuousLinearMap.comp_apply]
  rw [hDpi, hT, hTs, hM, map_add, map_add]

/-! ### The flip -/

theorem flipMat_mem :
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  · simp [Matrix.det_fin_two]

/-- `w = [[0,1],[-1,0]] ∈ SU(2)`. -/
noncomputable def flipElt : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨!![0, 1; -1, 0], flipMat_mem⟩

/-- The constant gauge transformation by `w`. -/
noncomputable def flipGauge {L : PeriodicLatticeExtent} : GaugeFn L := fun _ => flipElt

theorem flip_conj_uMat (t : ℝ) (g : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = AdalyFormal.D1Literal.uMat t) :
    ((flipElt * g * flipElt⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = AdalyFormal.D1Literal.uMat (-t) := by
  show (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) *
    star (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) = _
  rw [hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]

theorem flip_uθ (t : ℝ) :
    flipElt * AdalyFormal.D1Literal.uθ t * flipElt⁻¹ = AdalyFormal.D1Literal.uθ (-t) :=
  Subtype.ext (flip_conj_uMat t _ rfl)

theorem flip_Ug (s : ℝ) : flipElt * Ug s * flipElt⁻¹ = Ug (-s) := by
  apply Subtype.ext
  rw [flip_conj_uMat s (Ug s) (Ug_coe_uMat s), Ug_coe_uMat]

theorem flip_one : flipElt * (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) * flipElt⁻¹ = 1 := by
  rw [mul_one, mul_inv_cancel]

theorem flip_maskedU (q R : ℕ) (g : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    periodicGaugeTransform flipGauge (maskedU q R g V) =
      maskedU q R (fun e => -g e) (periodicGaugeTransform flipGauge V) := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [periodicGaugeTransform, maskedU, if_pos he, flipGauge]
  · simp only [periodicGaugeTransform, maskedU, if_neg he, flipGauge]
    exact flip_Ug (g e)

theorem flip_uthPath (q R : ℕ) (t : ℝ) :
    periodicGaugeTransform flipGauge (uthPath q R t) = uthPath q R (-t) := by
  classical
  funext e
  simp only [periodicGaugeTransform, uthPath, AdalyFormal.D1Literal.Uth, flipGauge]
  split_ifs
  · exact flip_uθ t
  · exact flip_one

theorem flip_trivial (L : PeriodicLatticeExtent) :
    periodicGaugeTransform (flipGauge (L := L))
      (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) = fun _ => 1 := by
  funext e
  exact flip_one

theorem flip_pathU (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) :
    periodicGaugeTransform flipGauge (pathU q R (uthPath q R) f ε t) =
      pathU q R (uthPath q R) f (-ε) (-t) := by
  unfold pathU
  rw [flip_maskedU, flip_uthPath]
  congr 1
  funext e
  ring

theorem flip_bulkU (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    periodicGaugeTransform flipGauge (bulkU q R f ε) = bulkU q R f (-ε) := by
  unfold bulkU
  rw [flip_maskedU, flip_trivial]
  congr 1
  funext e
  ring

/-! ### Consequences for the twist -/

/-- The flip maps the carrier at `(ε, t)` to the carrier at `(-ε, -t)`. -/
theorem pathA_flip (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ)
    (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    pathA q R (uthPath q R) f (-ε) 1 (-t) (adEL flipGauge (geomOf 2 1 (dilTower q R)) x) =
      adEL flipGauge (geomOf 2 1 (dilTower q R)) (pathA q R (uthPath q R) f ε 1 t x) := by
  have h := Ginv_all_gauge (ell := 2) (k := 1) (Lu := dilLu q R) (by norm_num) (dilTower q R)
    (pathU q R (uthPath q R) f ε t) 1 (dilLam q R) flipGauge x
  rw [flip_pathU] at h
  exact h

/-- **The backward vacuum twist is unitarily equivalent to the forward one.** -/
theorem vacA_flip (q R : ℕ) (t : ℝ) (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    vacA q R (uthPathNeg q R) 1 t (adEL flipGauge (geomOf 2 1 (dilTower q R)) x) =
      adEL flipGauge (geomOf 2 1 (dilTower q R)) (vacA q R (uthPath q R) 1 t x) := by
  have h := pathA_flip q R (fun _ => 0) 0 t x
  rw [neg_zero] at h
  exact h

theorem vacA_flip_psd (q R : ℕ) (t : ℝ) :
    PSD (vacA q R (uthPathNeg q R) 1 t) ↔ PSD (vacA q R (uthPath q R) 1 t) := by
  constructor
  · intro h x
    have h1 := h (adEL flipGauge (geomOf 2 1 (dilTower q R)) x)
    rw [vacA_flip, LinearIsometryEquiv.inner_map_map] at h1
    exact h1
  · intro h y
    obtain ⟨x, rfl⟩ := (adEL flipGauge (geomOf 2 1 (dilTower q R))).surjective y
    rw [vacA_flip, LinearIsometryEquiv.inner_map_map]
    exact h x

/-- The canonical crossings of the forward and backward twists coincide. -/
theorem vacEdge_flip (q R : ℕ) : vacEdge q R (uthPathNeg q R) = vacEdge q R (uthPath q R) := by
  have hS : {t : ℝ | t ∈ Set.Icc (0 : ℝ) Real.pi ∧
        ∀ s ∈ Set.Icc (0 : ℝ) t, PSD (vacA q R (uthPathNeg q R) 1 s)} =
      {t : ℝ | t ∈ Set.Icc (0 : ℝ) Real.pi ∧
        ∀ s ∈ Set.Icc (0 : ℝ) t, PSD (vacA q R (uthPath q R) 1 s)} := by
    ext t
    exact and_congr_right (fun _ => forall₂_congr (fun s _ => vacA_flip_psd q R s))
  exact congrArg sSup hS

/-- The flip maps the correction at `ε` to the correction at `-ε` (quadratic forms). -/
theorem bulkD_flip (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      bulkD q R f (-ε) (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫ =
      ⟪u, bulkD q R f ε u⟫ := by
  have h2 : (0 : ℕ) < 2 := by norm_num
  have h := AdalyFormal.M1GaugeW4.delta2_gauge (ell := 2) (k := 1) (Lu := dilLu q R) h2
    (dilTower q R) 1 (dilLam q R) (bulkU q R f ε) flipGauge u
  have heq : ∀ (d d' : BaseDataS ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  have hd1 : (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform flipGauge (bulkU q R f ε)) 1 (dilLam q R)).data =
      dataS selIn selIn (bulkP q R f (-ε)) := by
    show dataS selIn selIn (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform flipGauge (bulkU q R f ε)) 1 (dilLam q R)) = _
    unfold bulkP
    rw [flip_bulkU]
  have hd2 : (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data =
      dataS selIn selIn (bulkP q R f ε) := rfl
  have e1 : (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform flipGauge (bulkU q R f ε)) 1 (dilLam q R)).data.Delta2
      (gparams 2 1 (dilLu q R) h2 (dilTower q R)
        (periodicGaugeTransform flipGauge (bulkU q R f ε)) 1 (dilLam q R)).data_laws =
      bulkD q R f (-ε) := heq _ _ hd1 _ _
  have e2 : (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data.Delta2
      (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data_laws =
      bulkD q R f ε := heq _ _ hd2 _ _
  rw [e1, e2] at h
  exact h

/-- The derivative of a quadratic form of a differentiable operator family. -/
theorem hasDerivAt_quadForm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {D : ℝ → E →L[ℝ] E} {De : E →L[ℝ] E} {x₀ : ℝ} (hD : HasDerivAt D De x₀) (v : E) :
    HasDerivAt (fun ε => ⟪v, D ε v⟫) ⟪v, De v⟫ x₀ := by
  have hL : HasFDerivAt ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E v))
      ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E v)) (D x₀) :=
    ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E v)).hasFDerivAt
  exact hL.comp_hasDerivAt x₀ hD

/-- **The coupling is odd under the flip**: on the image of a vector under the flip the
first-order coefficient has the opposite quadratic form. -/
theorem De_flip {q R : ℕ} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hD : HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      De (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫ = -⟪u, De u⟫ := by
  have h1 := hasDerivAt_quadForm hD u
  have h2 := hasDerivAt_quadForm hD (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)
  have h2' : HasDerivAt (fun ε : ℝ => ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      bulkD q R f ε (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫)
      ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
        De (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫ (-0) := by
    rw [neg_zero]; exact h2
  have h3 := h2'.comp (0 : ℝ) (hasDerivAt_neg' (x := (0 : ℝ)))
  have e : ((fun ε : ℝ => ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      bulkD q R f ε (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫) ∘ fun x : ℝ => -x) =
      fun ε => ⟪u, bulkD q R f ε u⟫ := by
    funext ε
    exact bulkD_flip q R f ε u
  rw [e] at h3
  have h4 := h3.unique h1
  rw [mul_neg_one] at h4
  linarith

/-- A negative coupling on the forward canonical kernel is a positive coupling on the backward
one. -/
theorem couplingPos_back {q R : ℕ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hflip : ∀ u, ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      De (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫ = -⟪u, De u⟫)
    {c : ℝ} (hneg : ∀ u, vacA q R (uthPath q R) 1 (vacEdge q R (uthPath q R)) u = 0 →
      c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫) :
    ∀ u', vacA q R (uthPathNeg q R) 1 (vacEdge q R (uthPathNeg q R)) u' = 0 →
      c * ‖u'‖ ^ 2 ≤ ⟪u', De u'⟫ := by
  intro u' hu'
  obtain ⟨u, rfl⟩ := (adEL flipGauge (geomOf 2 1 (dilTower q R))).surjective u'
  rw [vacEdge_flip, vacA_flip] at hu'
  have hu : vacA q R (uthPath q R) 1 (vacEdge q R (uthPath q R)) u = 0 :=
    (map_eq_zero_iff _ (adEL flipGauge (geomOf 2 1 (dilTower q R))).injective).mp hu'
  rw [LinearIsometryEquiv.norm_map, hflip]
  exact hneg u hu

/-! ### The literal target with one kernel -/

/-- **The reduced premise for the literal round-8 family at `(q,R)`, one kernel.**  Soft
regularity of the single-defect interior family at the flat interior, and a first-order
coefficient that is definite, of EITHER sign, on the kernel of the vacuum carrier at the
canonical crossing of the forward twist.  NOT proved here. -/
def TwistSoftCouplingFwd (q R : ℕ) : Prop :=
  ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
    InteriorSoft q R (dilMask q R) De ∧ CanonicalCoupling q R (uthPath q R) De

theorem twistSoftCoupling_of_fwd {q R : ℕ} (h : TwistSoftCouplingFwd q R) :
    TwistSoftCoupling q R := by
  obtain ⟨De, hs, c, hc, hpos | hneg⟩ := h
  · exact ⟨De, hs, Or.inl ⟨c, hc, hpos⟩⟩
  · exact ⟨De, hs, Or.inr ⟨c, hc, couplingPos_back (De_flip hs.2.2) hneg⟩⟩

def CofinalTwistSoftCouplingFwd : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    TwistSoftCouplingFwd (2^j) R

theorem cofinalTwistSoftCoupling_of_fwd (h : CofinalTwistSoftCouplingFwd) :
    CofinalTwistSoftCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, twistSoftCoupling_of_fwd hv⟩

/-- **Main reduction of this round (literal target, one kernel, either sign).** -/
theorem cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd (h : CofinalTwistSoftCouplingFwd) :
    CofinalTwistSeparation :=
  cofinalTwistSeparation_of_cofinalTwistSoftCoupling (cofinalTwistSoftCoupling_of_fwd h)

theorem goalNeg2_of_cofinalTwistSoftCouplingFwd (h : CofinalTwistSoftCouplingFwd) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd h)

theorem not_cofinalTwistSoftCouplingFwd_of_goalPos1 (h : GoalPos1) :
    ¬ CofinalTwistSoftCouplingFwd :=
  fun h' => goalNeg2_of_cofinalTwistSoftCouplingFwd h' (goalPos2_iff_goalPos1.mpr h)

/-- **Per instance.**  At every large scale and every large even radius, the reduced premise at
that instance gives a separation of the literal family at every small positive curvature. -/
theorem twistSeparation_eventually_of_fwd :
    ∃ j₁ : ℕ, ∀ j : ℕ, j₁ ≤ j → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → 2 ∣ R → 18 ≤ R →
      TwistSoftCouplingFwd (2^j) R →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → TwistSeparation (2^j) R ε := by
  obtain ⟨j₁, hj₁⟩ := flat_loc_unit_eventually
  refine ⟨j₁, fun j hj => ?_⟩
  obtain ⟨R₁, hR₁⟩ := hj₁ j hj
  refine ⟨R₁, fun R hR hR2 hR18 h => ?_⟩
  exact twistSeparation_eventually (by positivity) hR2 hR18 (hR₁ R hR hR2 hR18)
    (twistSoftCoupling_of_fwd h)

/-- What the positive reading demands, stated directly: at every large scale and every large
even radius the reduced premise fails, i.e. the interior family is not softly regular or the
first-order coupling is not definite on the canonical forward vacuum kernel. -/
theorem goalPos1_forces_no_softCoupling (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ¬ TwistSoftCouplingFwd (2^j) R := by
  have h' := not_cofinalTwistSoftCouplingFwd_of_goalPos1 h
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
  exact ⟨R, hRR, hR2, hR18, not_not.mp hR4⟩

#print axioms Ginv_all_gauge
#print axioms flipMat_mem
#print axioms flipElt
#print axioms flipGauge
#print axioms flip_conj_uMat
#print axioms flip_uθ
#print axioms flip_Ug
#print axioms flip_one
#print axioms flip_maskedU
#print axioms flip_uthPath
#print axioms flip_trivial
#print axioms flip_pathU
#print axioms flip_bulkU
#print axioms pathA_flip
#print axioms vacA_flip
#print axioms vacA_flip_psd
#print axioms vacEdge_flip
#print axioms bulkD_flip
#print axioms hasDerivAt_quadForm
#print axioms De_flip
#print axioms couplingPos_back
#print axioms TwistSoftCouplingFwd
#print axioms twistSoftCoupling_of_fwd
#print axioms CofinalTwistSoftCouplingFwd
#print axioms cofinalTwistSoftCoupling_of_fwd
#print axioms cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd
#print axioms goalNeg2_of_cofinalTwistSoftCouplingFwd
#print axioms not_cofinalTwistSoftCouplingFwd_of_goalPos1
#print axioms twistSeparation_eventually_of_fwd
#print axioms goalPos1_forces_no_softCoupling

end AdalyFormal.Round9.Guarded.QualitativeR2

/-! ## The diagonal `U(1)`: the coupling is a single number on a charged complex line

Every link of the curved twist family is diagonal, so the constant gauge rotations
`diag(e^{iα}, e^{-iα})` leave the configuration unchanged.  By the frozen covariance lane the
vacuum carrier and the correction commute with the induced orthogonal maps `J_α`.  Hence, if the
canonical vacuum kernel is the complex line spanned by a charged vector `u₀` and `J u₀`
(`J = J_{π/4}`, `J (J u₀) = -u₀`), the first-order coefficient acts on it as the scalar
`⟪u₀, De u₀⟫ / ‖u₀‖²`, and the coupling premise is exactly `⟪u₀, De u₀⟫ ≠ 0`: round 8's
`c₁(q,R) ≠ 0`.  Round 9.1 assumed the commutation; here it is proved. -/
namespace AdalyFormal.Round9.Guarded.QualitativeR2

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
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.D1Literal (PSD)

/-- The constant diagonal gauge rotation by `diag(e^{iα}, e^{-iα})`. -/
noncomputable def rotGauge {L : PeriodicLatticeExtent} (α : ℝ) : GaugeFn L :=
  fun _ => AdalyFormal.D1Literal.uθ α

theorem uθ_comm (α s : ℝ) :
    AdalyFormal.D1Literal.uθ α * AdalyFormal.D1Literal.uθ s =
      AdalyFormal.D1Literal.uθ s * AdalyFormal.D1Literal.uθ α := by
  apply Subtype.ext
  show AdalyFormal.D1Literal.uMat α * AdalyFormal.D1Literal.uMat s =
    AdalyFormal.D1Literal.uMat s * AdalyFormal.D1Literal.uMat α
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem uθ_conj (α s : ℝ) :
    AdalyFormal.D1Literal.uθ α * AdalyFormal.D1Literal.uθ s * (AdalyFormal.D1Literal.uθ α)⁻¹ =
      AdalyFormal.D1Literal.uθ s := by
  rw [uθ_comm, mul_assoc, mul_inv_cancel, mul_one]

theorem Ug_eq_uθ (s : ℝ) : Ug s = AdalyFormal.D1Literal.uθ s :=
  Subtype.ext (Ug_coe_uMat s)

theorem rot_maskedU (q R : ℕ) (α : ℝ) (g : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    periodicGaugeTransform (rotGauge α) (maskedU q R g V) =
      maskedU q R g (periodicGaugeTransform (rotGauge α) V) := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [periodicGaugeTransform, maskedU, if_pos he, rotGauge]
  · simp only [periodicGaugeTransform, maskedU, if_neg he, rotGauge, Ug_eq_uθ]
    exact uθ_conj α (g e)

theorem rot_uthPath (q R : ℕ) (α t : ℝ) :
    periodicGaugeTransform (rotGauge α) (uthPath q R t) = uthPath q R t := by
  classical
  funext e
  simp only [periodicGaugeTransform, uthPath, AdalyFormal.D1Literal.Uth, rotGauge]
  split_ifs
  · exact uθ_conj α t
  · rw [mul_one, mul_inv_cancel]

theorem rot_trivial (L : PeriodicLatticeExtent) (α : ℝ) :
    periodicGaugeTransform (rotGauge (L := L) α)
      (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) = fun _ => 1 := by
  funext e
  show AdalyFormal.D1Literal.uθ α * 1 * (AdalyFormal.D1Literal.uθ α)⁻¹ = 1
  rw [mul_one, mul_inv_cancel]

theorem rot_pathU (q R : ℕ) (α : ℝ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) :
    periodicGaugeTransform (rotGauge α) (pathU q R (uthPath q R) f ε t) =
      pathU q R (uthPath q R) f ε t := by
  unfold pathU
  rw [rot_maskedU, rot_uthPath]

theorem rot_bulkU (q R : ℕ) (α : ℝ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    periodicGaugeTransform (rotGauge α) (bulkU q R f ε) = bulkU q R f ε := by
  unfold bulkU
  rw [rot_maskedU, rot_trivial]

/-- The vacuum carrier of the twist commutes with every diagonal rotation. -/
theorem vacA_rot (q R : ℕ) (α t : ℝ) (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    vacA q R (uthPath q R) 1 t (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) x) =
      adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (vacA q R (uthPath q R) 1 t x) := by
  have h := Ginv_all_gauge (ell := 2) (k := 1) (Lu := dilLu q R) (by norm_num) (dilTower q R)
    (pathU q R (uthPath q R) (fun _ => 0) 0 t) 1 (dilLam q R) (rotGauge α) x
  rw [rot_pathU] at h
  exact h

/-- The correction has rotation-invariant quadratic form. -/
theorem bulkD_rot (q R : ℕ) (α : ℝ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    ⟪adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u,
      bulkD q R f ε (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u)⟫ = ⟪u, bulkD q R f ε u⟫ := by
  have h2 : (0 : ℕ) < 2 := by norm_num
  have h := AdalyFormal.M1GaugeW4.delta2_gauge (ell := 2) (k := 1) (Lu := dilLu q R) h2
    (dilTower q R) 1 (dilLam q R) (bulkU q R f ε) (rotGauge α) u
  have heq : ∀ (d d' : BaseDataS ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  have hd1 : (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)).data =
      dataS selIn selIn (bulkP q R f ε) := by
    show dataS selIn selIn (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)) = _
    unfold bulkP
    rw [rot_bulkU]
  have hd2 : (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data =
      dataS selIn selIn (bulkP q R f ε) := rfl
  have e1 : (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)).data.Delta2
      (gparams 2 1 (dilLu q R) h2 (dilTower q R)
        (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)).data_laws =
      bulkD q R f ε := heq _ _ hd1 _ _
  have e2 : (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data.Delta2
      (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data_laws =
      bulkD q R f ε := heq _ _ hd2 _ _
  rw [e1, e2] at h
  exact h

/-- The derivative of a matrix coefficient of a differentiable operator family. -/
theorem hasDerivAt_bilin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {D : ℝ → E →L[ℝ] E} {De : E →L[ℝ] E} {x₀ : ℝ} (hD : HasDerivAt D De x₀) (v w : E) :
    HasDerivAt (fun ε => ⟪v, D ε w⟫) ⟪v, De w⟫ x₀ := by
  have hL : HasFDerivAt ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E w))
      ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E w)) (D x₀) :=
    ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E w)).hasFDerivAt
  exact hL.comp_hasDerivAt x₀ hD

/-- The first-order coefficient of the correction is symmetric. -/
theorem De_symm {q R : ℕ} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hD : HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0)
    (x y : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : ⟪De x, y⟫ = ⟪x, De y⟫ := by
  have h1 := hasDerivAt_bilin hD y x
  have h2 := hasDerivAt_bilin hD x y
  have e : (fun ε : ℝ => ⟪y, bulkD q R f ε x⟫) = fun ε => ⟪x, bulkD q R f ε y⟫ := by
    funext ε
    exact (real_inner_comm (bulkD q R f ε x) y).trans
      (((dataS selIn selIn (bulkP q R f ε)).Delta2_spec (dataS_laws selIn selIn _)).1 x y)
  rw [e] at h1
  rw [real_inner_comm]
  exact h1.unique h2

/-- The first-order coefficient commutes with every diagonal rotation. -/
theorem De_rot_comm {q R : ℕ} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hD : HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0) (α : ℝ)
    (y : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    De (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) y) =
      adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (De y) := by
  set J := adEL (rotGauge α) (geomOf 2 1 (dilTower q R))
  have hq : ∀ u, ⟪J u, De (J u)⟫ = ⟪u, De u⟫ := by
    intro u
    have h1 := hasDerivAt_quadForm hD (J u)
    have h2 := hasDerivAt_quadForm hD u
    have e : (fun ε : ℝ => ⟪J u, bulkD q R f ε (J u)⟫) = fun ε => ⟪u, bulkD q R f ε u⟫ :=
      funext (fun ε => bulkD_rot q R α f ε u)
    rw [e] at h1
    exact h1.unique h2
  have hb : ∀ x, ⟪J x, De (J y)⟫ = ⟪x, De y⟫ := by
    intro x
    have h := hq (x + y)
    have hx := hq x
    have hy := hq y
    have hs1 : ⟪J y, De (J x)⟫ = ⟪J x, De (J y)⟫ := by
      rw [← De_symm hD, real_inner_comm]
    have hs2 : ⟪y, De x⟫ = ⟪x, De y⟫ := by
      rw [← De_symm hD, real_inner_comm]
    simp only [map_add, inner_add_left, inner_add_right] at h
    linarith
  refine ext_inner_left ℝ (fun v => ?_)
  obtain ⟨x, rfl⟩ := J.surjective v
  rw [hb x, LinearIsometryEquiv.inner_map_map]

/-- **Complex-line form of the coupling premise.**  The canonical forward vacuum kernel lies in
the plane spanned by a nonzero vector `u₀` and `J u₀`, where `J` is the quarter rotation and
`J (J u₀) = -u₀` (`u₀` is charged), and `⟪u₀, De u₀⟫ ≠ 0`.  NOT proved here. -/
def CanonicalU1Line (q R : ℕ)
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ∃ u₀ : ↥(bondSupp (geomOf 2 1 (dilTower q R))), u₀ ≠ 0 ∧
    vacA q R (uthPath q R) 1 (vacEdge q R (uthPath q R)) u₀ = 0 ∧
    adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
      (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀) = -u₀ ∧
    (∀ u, vacA q R (uthPath q R) 1 (vacEdge q R (uthPath q R)) u = 0 →
      u ∈ Submodule.span ℝ {u₀, adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀}) ∧
    ⟪u₀, De u₀⟫ ≠ 0

/-- On a charged complex line the coupling is the single number `⟪u₀, De u₀⟫`; its
nonvanishing is the definite coupling of the reduced premise. -/
theorem canonicalCoupling_of_U1 {q R : ℕ} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hD : HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0) (h : CanonicalU1Line q R De) :
    CanonicalCoupling q R (uthPath q R) De := by
  obtain ⟨u₀, hu₀, -, hJJ, hK, hc⟩ := h
  let J := adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
  let Jop : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
    J.toLinearIsometry.toContinuousLinearMap
  obtain ⟨l, hl⟩ := scalar_on_complex_line De Jop (De_symm hD)
    (fun x y => LinearIsometryEquiv.inner_map_map J x y)
    (fun x => De_rot_comm hD (Real.pi / 4) x) u₀ hu₀ hJJ
  have hmem : u₀ ∈ Submodule.span ℝ {u₀, Jop u₀} := Submodule.subset_span (by simp)
  have hn : 0 < ‖u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu₀) 2
  have hl0 : l ≠ 0 := by
    intro h0
    apply hc
    rw [hl u₀ hmem, h0, zero_mul]
  rcases lt_or_gt_of_ne hl0 with hneg | hpos
  · refine ⟨-l, by linarith, Or.inr (fun u hu => ?_)⟩
    have h1 := hl u (hK u hu)
    linarith
  · refine ⟨l, hpos, Or.inl (fun u hu => ?_)⟩
    have h1 := hl u (hK u hu)
    linarith

/-- The literal reduced premise in complex-line form. -/
def TwistSoftU1 (q R : ℕ) : Prop :=
  ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
    InteriorSoft q R (dilMask q R) De ∧ CanonicalU1Line q R De

theorem twistSoftCouplingFwd_of_U1 {q R : ℕ} (h : TwistSoftU1 q R) : TwistSoftCouplingFwd q R := by
  obtain ⟨De, hs, hc⟩ := h
  exact ⟨De, hs, canonicalCoupling_of_U1 hs.2.2 hc⟩

def CofinalTwistSoftU1 : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ TwistSoftU1 (2^j) R

theorem cofinalTwistSeparation_of_cofinalTwistSoftU1 (h : CofinalTwistSoftU1) :
    CofinalTwistSeparation := by
  refine cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd (fun j₀ => ?_)
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, twistSoftCouplingFwd_of_U1 hv⟩

theorem goalNeg2_of_cofinalTwistSoftU1 (h : CofinalTwistSoftU1) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_cofinalTwistSoftU1 h)

#print axioms rotGauge
#print axioms uθ_comm
#print axioms uθ_conj
#print axioms Ug_eq_uθ
#print axioms rot_maskedU
#print axioms rot_uthPath
#print axioms rot_trivial
#print axioms rot_pathU
#print axioms rot_bulkU
#print axioms vacA_rot
#print axioms bulkD_rot
#print axioms hasDerivAt_bilin
#print axioms De_symm
#print axioms De_rot_comm
#print axioms CanonicalU1Line
#print axioms canonicalCoupling_of_U1
#print axioms TwistSoftU1
#print axioms twistSoftCouplingFwd_of_U1
#print axioms CofinalTwistSoftU1
#print axioms cofinalTwistSeparation_of_cofinalTwistSoftU1
#print axioms goalNeg2_of_cofinalTwistSoftU1

end AdalyFormal.Round9.Guarded.QualitativeR2

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

The bridge is then freed from the round-5 twist (any exterior field separates), joint
continuity in `(ε, t)` is derived from the frozen exterior path formula, and the final
reduction is `goalNeg2_of_interiorSoft_vacuumLeftSpectral : InteriorSoft →
VacuumLeftSpectral → GoalNeg2`: soft regularity of the single interior family
`ε ↦ dilU q R ε 1` at `ε = 0⁺`, plus zero-curvature crossing data of the left-only twist.

Nothing here proves a pinned goal.  `InteriorSoft`, `VacuumLeftSpectral`,
`VacuumNondegeneracy` and the other premises are explicit, unproved hypotheses about the
actual operators.
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
    (hjoint : ∀ t, |t - t₀| < η₀ →
      Tendsto (fun p : ℝ × ℝ => X p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t) (𝓝 (X 0 t)))
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
  have hXF : Tendsto (fun p : ℝ × ℝ => X p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t₀) (𝓝 (X 0 t₀)) :=
    hjoint t₀ (by simpa using hη₀)
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
    have hX1 : Tendsto (fun ε : ℝ => X ε (t₀ + τ)) (𝓝[>] 0) (𝓝 (X 0 (t₀ + τ))) :=
      (hjoint (t₀ + τ) hcl).comp (Filter.Tendsto.prodMk tendsto_id tendsto_const_nhds)
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
    (hjoint : ∀ t, |t - t₀| < η₀ →
      Tendsto (fun p : ℝ × ℝ => X p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t) (𝓝 (X 0 t)))
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
    have hjr : ∀ t, |t - t₀| < η₀ →
        Tendsto (fun p : ℝ × ℝ => Xr p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t) (𝓝 (Xr 0 t)) := by
      intro t ht
      have h1 : |2 * t₀ - t - t₀| < η₀ := by
        rw [show 2 * t₀ - t - t₀ = -(t - t₀) by ring, abs_neg]; exact ht
      have h2 := hjoint (2 * t₀ - t) h1
      have hmap : Tendsto (fun p : ℝ × ℝ => (p.1, 2 * t₀ - p.2)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t)
          (𝓝[>] (0 : ℝ) ×ˢ 𝓝 (2 * t₀ - t)) :=
        Filter.Tendsto.prodMk tendsto_fst (tendsto_const_nhds.sub tendsto_snd)
      exact (h2.comp hmap).neg
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
    (hjoint : ∀ t, |t - t₀| < η₀ →
      Tendsto (fun p : ℝ × ℝ => X p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t) (𝓝 (X 0 t)))
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
continuous in `(ε, t)` as `ε → 0⁺`, and the correction has the first-order coefficient
`D₁` as `ε → 0⁺`.  NOT proved here. -/
def ZeroCurvatureRegularity (q R : ℕ) (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R) : Prop :=
  (∀ t : ℝ, Tendsto (fun p : ℝ × ℝ => twistA q R p.1 1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t)
    (𝓝 (twistA q R 0 1 t))) ∧
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
  (∀ t : ℝ, Tendsto (fun p : ℝ × ℝ => extA q R p.1 (V p.2)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t)
    (𝓝 (extA q R 0 (V t)))) ∧
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

/-! ## Continuity of the plaquette operator in several parameters

The frozen `D1Cont` proves that `θ ↦ deltaKLocCLM (U θ) P` is continuous for a
real-parameter family whose link matrices are continuous.  The proofs below are those of
`D1Cont`, verbatim up to renaming, with the parameter space `ℝ` replaced by an arbitrary
topological space `Y` (here `Y = ℝ × ℝ`: curvature and exterior angle). -/
section JointContinuity

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.StatementLaneR6
open AdalyFormal.D1Literal (SU2m)

variable {L : PeriodicLatticeExtent} {Y : Type*} [TopologicalSpace Y]

/-- A family of link configurations over a topological parameter space, continuous link by
link (the frozen `ContFam` with `ℝ` replaced by `Y`). -/
def ContFamT (U : Y → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, Continuous fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)

section
variable {U : Y → PeriodicLinkConfiguration SU2m L} (hU : ContFamT U)
include hU

theorem contT_inv_coe (e : PeriodicLatticeEdge L) :
    Continuous fun θ => (((U θ e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => (((U θ e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => star ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    rfl
  rw [this]
  exact (hU e).star

theorem contT_holonomyElem (p : PeriodicLatticePlaquette L) :
    Continuous fun θ => ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => ((U θ (p.1, p.2.1.1) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((U θ (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        (((U θ (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        (((U θ (p.1, p.2.1.2))⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    rfl
  rw [this]
  exact (((hU _).matrix_mul (hU _)).matrix_mul (contT_inv_coe hU _)).matrix_mul (contT_inv_coe hU _)

theorem contT_holonomyElemInv (p : PeriodicLatticePlaquette L) :
    Continuous fun θ => ((holonomyElemInv (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((holonomyElemInv (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => star ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ; rfl
  rw [this]
  exact (contT_holonomyElem hU p).star

theorem contT_reHolonomy (p : PeriodicLatticePlaquette L) :
    Continuous fun θ => reHolonomy (U θ) p := by
  unfold reHolonomy
  exact continuous_const.smul ((contT_holonomyElem hU p).add (contT_holonomyElemInv hU p))

theorem contT_imHolonomy (p : PeriodicLatticePlaquette L) :
    Continuous fun θ => imHolonomy (U θ) p := by
  unfold imHolonomy
  exact continuous_const.smul ((contT_holonomyElem hU p).sub (contT_holonomyElemInv hU p))

theorem contT_RMap (e : PeriodicLatticeEdge L) (X : SuTwo) :
    Continuous fun θ => ((RMap (U θ e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((RMap (U θ e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ) *
        star ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    exact AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply (U θ e) X
  rw [this]
  exact ((hU e).matrix_mul continuous_const).matrix_mul (hU e).star

theorem contT_curlMat (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun θ => curlMatLM (U θ) p A := by
  simp only [curlMatLM_apply]
  unfold curlValueCovariant
  simp only [Submodule.coe_add, Submodule.coe_sub]
  exact (((continuous_const.add (contT_RMap hU _ _)).sub (contT_RMap hU _ _)).sub continuous_const)

theorem contT_a1 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun θ => a1LM (U θ) p A := by
  show Continuous fun θ =>
    -(bondMatRLM (U θ (p.1, p.2.1.2)) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) A)
  simp only [bondMatRLM_apply]
  exact (contT_RMap hU _ _).neg

theorem contT_a4 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun θ => a4LM (U θ) p A := by
  show Continuous fun θ =>
    bondMatRLM (U θ (p.1, p.2.1.1)) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) A
  simp only [bondMatRLM_apply]
  exact contT_RMap hU _ _

omit hU in
theorem contT_tr_re3 {f g h : Y → Matrix (Fin 2) (Fin 2) ℂ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) : Continuous fun θ => (Matrix.trace (f θ * g θ * h θ)).re :=
  Complex.continuous_re.comp (((hf.matrix_mul hg).matrix_mul hh).matrix_trace)

theorem contT_bilPlaq (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    Continuous fun θ => bilPlaq (U θ) p A B := by
  simp only [bilPlaq_atoms]
  have hI : ∀ {f : Y → Matrix (Fin 2) (Fin 2) ℂ}, Continuous f →
      Continuous fun θ => smulILM (f θ) := by
    intro f hf
    exact continuous_const.smul hf
  have b1A : Continuous fun θ => b1LM (U θ) p A := hI (contT_a1 hU p A)
  have b4B : Continuous fun θ => b4LM (U θ) p B := hI (contT_a4 hU p B)
  have b4A : Continuous fun θ => b4LM (U θ) p A := hI (contT_a4 hU p A)
  have hre := contT_reHolonomy hU p
  have him := contT_imHolonomy hU p
  have hcA : Continuous fun θ => smulILM (curlMatLM (U θ) p A) := hI (contT_curlMat hU p A)
  have hcB : Continuous fun θ => smulILM (curlMatLM (U θ) p B) := hI (contT_curlMat hU p B)
  have k : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), Continuous fun _ : Y => M := fun M => continuous_const
  refine ((((((contT_tr_re3 hcA hcB (hre.sub (k 1))).add
    ((contT_tr_re3 (hI b1A) (k _) him).sub (contT_tr_re3 (k _) b1A him))).add
    ((contT_tr_re3 (hI b1A) (k _) him).sub (contT_tr_re3 (k _) b1A him))).add
    ((contT_tr_re3 (hI b1A) b4B him).sub (contT_tr_re3 (hI b4B) b1A him))).add
    ((contT_tr_re3 (k _) (k _) him).sub (contT_tr_re3 (k _) (k _) him))).add
    ((contT_tr_re3 (k _) b4B him).sub (contT_tr_re3 (hI b4B) (k _) him))).add
    ((contT_tr_re3 (k _) b4B him).sub (contT_tr_re3 (hI b4B) (k _) him))

open Classical in
theorem contT_deltaPrimeBil (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    Continuous fun θ => deltaPrimeBilNormLoc (U θ) P A B := by
  have h : ∀ A B : Bond L → SuTwo, Continuous fun θ => deltaPrimeBilRawLoc (U θ) P A B := by
    intro A B
    simp only [deltaPrimeBilRawLoc_apply]
    exact continuous_finsetSum _ (fun p _ => by
      by_cases hp : p ∈ P
      · simp only [hp, if_true]; exact contT_bilPlaq hU p A B
      · simp only [hp, if_false]; exact continuous_const)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  exact continuous_const.mul (continuous_const.mul ((h A B).add (h B A)))

open Classical in
theorem contT_curlInner (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    Continuous fun θ => (inner ℝ (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) x))
      (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) y)) : ℝ) := by
  simp only [PiLp.inner_apply]
  refine continuous_finsetSum _ (fun p _ => ?_)
  simp only [plaqMask_apply]
  by_cases hp : p ∈ P
  · simp only [hp, if_true]
    show Continuous fun θ => AdalyFormal.Balaban.SuTwoInner.hsInner
      (curlValueCovariant (U θ) (WithLp.ofLp x) p) (curlValueCovariant (U θ) (WithLp.ofLp y) p)
    unfold AdalyFormal.Balaban.SuTwoInner.hsInner
    refine continuous_const.mul (Complex.continuous_re.comp ?_)
    exact ((contT_curlMat hU p (WithLp.ofLp x)).matrix_mul
      (contT_curlMat hU p (WithLp.ofLp y))).matrix_trace
  · simp only [hp, if_false, inner_zero_left]
    exact continuous_const

theorem contT_inner_delta (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    Continuous fun θ => (inner ℝ x (deltaKLocCLM (U θ) P y) : ℝ) := by
  simp only [inner_deltaKLocCLM]
  exact (contT_curlInner hU P x y).add (contT_deltaPrimeBil hU P _ _)

end

theorem contT_deltaKLocCLM {U : Y → PeriodicLinkConfiguration SU2m L} (hU : ContFamT U)
    (P : Set (PeriodicLatticePlaquette L)) : Continuous fun θ => deltaKLocCLM (U θ) P :=
  AdalyFormal.D1Literal.continuous_clm_of_inner (fun x y => contT_inner_delta hU P x y)

end JointContinuity

/-! ## The exterior-free soft premise

Along any continuous exterior path, joint continuity of the carrier in (curvature, angle)
follows from continuity in the curvature alone, at the path's base point, of the carrier
and of the dressing `W`: the exterior part of the carrier is the frozen path formula
`exterior_carrier_path`, whose plaquette factor is jointly continuous above.  For the left
twist the base point is the trivial exterior field, so the soft premise becomes a statement
about the single interior family `ε ↦ dilU q R ε 1`. -/
section InteriorFamily

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
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)

theorem uMat_continuous : Continuous fun θ : ℝ => AdalyFormal.D1Literal.uMat θ := by
  unfold AdalyFormal.D1Literal.uMat
  refine continuous_matrix (fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- The abelian link `Ug t = exp(i t σ₃)` is the diagonal matrix `diag(e^{it}, e^{-it})`. -/
theorem Ug_coe (t : ℝ) :
    ((Ug t : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      AdalyFormal.D1Literal.uMat t := by
  show NormedSpace.exp (Xm t) = _
  have hX : Xm t = Matrix.diagonal ![(t : ℂ) * Complex.I, -((t : ℂ) * Complex.I)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Xm, sig, Matrix.diagonal]
  rw [hX, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.diagonal, ← Complex.exp_eq_exp_ℂ]

/-- The curved family with a continuous exterior path is continuous in (curvature, angle). -/
theorem dilU_contFamT (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (hV : AdalyFormal.D1Literal.ContFam V) :
    ContFamT (fun p : ℝ × ℝ => dilU q R p.1 (V p.2)) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [dilU, if_pos he]
    exact (hV e).comp continuous_snd
  · simp only [dilU, if_neg he]
    by_cases hp : dilPattern q R e
    · simp only [if_pos hp, Ug_coe]
      exact uMat_continuous.comp continuous_fst
    · simp only [if_neg hp]
      exact continuous_const

/-- Limits commute with composition of bounded operators. -/
theorem tendsto_clm_comp {α : Type*} {l : Filter α} {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : α → F →L[ℝ] G} {f : α → E →L[ℝ] F} {g₀ : F →L[ℝ] G} {f₀ : E →L[ℝ] F}
    (hg : Tendsto g l (𝓝 g₀)) (hf : Tendsto f l (𝓝 f₀)) :
    Tendsto (fun a => (g a).comp (f a)) l (𝓝 (g₀.comp f₀)) := by
  have hc : Continuous (fun p : (F →L[ℝ] G) × (E →L[ℝ] F) => p.1.comp p.2) :=
    continuous_fst.clm_comp continuous_snd
  exact (hc.tendsto (g₀, f₀)).comp (hg.prodMk_nhds hf)

/-- Joint one-sided continuity of the carrier at zero curvature along an exterior path, from
continuity in the curvature of the carrier at the base point of the path and of `W`. -/
theorem extA_joint_tendsto {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (hV : AdalyFormal.D1Literal.ContFam V)
    (hA : Tendsto (fun ε : ℝ => extA q R ε (V 0)) (𝓝[>] 0) (𝓝 (extA q R 0 (V 0))))
    (hW : Tendsto (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (dilU q R ε (V 0)) 1) (𝓝[>] 0)
      (𝓝 (Wop (geomOf 2 1 (dilTower q R)) (dilU q R 0 (V 0)) 1)))
    (t : ℝ) :
    Tendsto (fun p : ℝ × ℝ => extA q R p.1 (V p.2)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t)
      (𝓝 (extA q R 0 (V t))) := by
  let G := geomOf 2 1 (dilTower q R)
  let Wf : ℝ → BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ] BondFnL2 (scaleUp 2 1 (dilLu q R)) :=
    fun ε => Wop G (dilU q R ε (V 0)) 1
  let Δf : ℝ × ℝ → BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ] BondFnL2 (scaleUp 2 1 (dilLu q R)) :=
    fun p => AdalyFormal.StatementLaneR6.deltaKLocCLM (dilU q R p.1 (V p.2)) Set.univ
  have hpath : ∀ ε s : ℝ, extA q R ε (V s) = extA q R ε (V 0) +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wf ε)).comp
        ((Δf (ε, s) - Δf (ε, 0)).comp (Wf ε))).comp (iE G)) := by
    intro ε s
    exact exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      1 (dilLam q R) (fun s => dilU q R ε (V s))
      (fun s e he => dilU_agree q R ε (V s) (V 0) e he) selAll s
  have hΔ : Continuous Δf := contT_deltaKLocCLM (dilU_contFamT q R V hV) _
  have hfst : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t) (𝓝 0) :=
    tendsto_fst.mono_right nhdsWithin_le_nhds
  have hp1 : Tendsto (fun p : ℝ × ℝ => (p.1, p.2)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t) (𝓝 ((0 : ℝ), t)) :=
    hfst.prodMk_nhds tendsto_snd
  have hp0 : Tendsto (fun p : ℝ × ℝ => (p.1, (0 : ℝ))) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t)
      (𝓝 ((0 : ℝ), (0 : ℝ))) :=
    hfst.prodMk_nhds tendsto_const_nhds
  have h1 : Tendsto (fun p : ℝ × ℝ => Δf (p.1, p.2) - Δf (p.1, 0)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t)
      (𝓝 (Δf (0, t) - Δf (0, 0))) :=
    ((hΔ.tendsto _).comp hp1).sub ((hΔ.tendsto _).comp hp0)
  have hWl : Tendsto (fun p : ℝ × ℝ => Wf p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t) (𝓝 (Wf 0)) :=
    hW.comp tendsto_fst
  have hadj : Continuous (fun M : BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R)) => ContinuousLinearMap.adjoint M) :=
    (ContinuousLinearMap.adjoint : (BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R))) ≃ₗᵢ⋆[ℝ] (BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R)))).continuous
  have hWa : Tendsto (fun p : ℝ × ℝ => ContinuousLinearMap.adjoint (Wf p.1))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t) (𝓝 (ContinuousLinearMap.adjoint (Wf 0))) :=
    (hadj.tendsto _).comp hWl
  have hmid : Tendsto (fun p : ℝ × ℝ => (ContinuousLinearMap.adjoint (Wf p.1)).comp
      ((Δf (p.1, p.2) - Δf (p.1, 0)).comp (Wf p.1))) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t)
      (𝓝 ((ContinuousLinearMap.adjoint (Wf 0)).comp ((Δf (0, t) - Δf (0, 0)).comp (Wf 0)))) :=
    tendsto_clm_comp hWa (tendsto_clm_comp h1 hWl)
  have hout : Continuous fun M : BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R)) => (pE G).comp (M.comp (iE G)) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  have hall := (hA.comp tendsto_fst).add ((hout.tendsto _).comp hmid)
  rw [hpath 0 t]
  refine hall.congr' (Filter.Eventually.of_forall (fun p => ?_))
  exact (hpath p.1 p.2).symm

theorem leftTwist_zero (q R : ℕ) : leftTwist q R 0 = 1 := by
  funext e
  simp only [leftTwist, AdalyFormal.D1Literal.uθ_zero, ite_self, Pi.one_apply]

/-- Soft regularity of the single interior family `ε ↦ dilU q R ε 1` (curved interior,
trivial exterior), as `ε → 0⁺`: continuity of the carrier and of the dressing `W`, and the
first-order coefficient `D₁` of the correction.  No exterior angle appears.  NOT proved here. -/
def InteriorRegularity (q R : ℕ) (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R) : Prop :=
  Tendsto (fun ε : ℝ => extA q R ε 1) (𝓝[>] 0) (𝓝 (extA q R 0 1)) ∧
  Tendsto (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (dilU q R ε 1) 1) (𝓝[>] 0)
    (𝓝 (Wop (geomOf 2 1 (dilTower q R)) (dilU q R 0 1) 1)) ∧
  Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε 1) (𝓝[>] 0) (𝓝 D₁)

theorem leftRegularity_of_interior {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {D₁ : TwistSpace q R →L[ℝ] TwistSpace q R} (h : InteriorRegularity q R D₁) :
    PathRegularity q R (leftTwist q R) D₁ := by
  obtain ⟨hA, hW, hD⟩ := h
  have h0 : leftTwist q R 0 = 1 := leftTwist_zero q R
  refine ⟨fun t => extA_joint_tendsto hq hR hroom (leftTwist q R) (leftTwist_cont q R)
    (by rw [h0]; exact hA) (by rw [h0]; exact hW) t, ?_⟩
  rw [h0]
  exact hD

/-- The soft half of the final premise, exterior-free.  NOT proved here. -/
def InteriorSoft : Prop :=
  ∀ q R : ℕ, 0 < q → 2 ∣ R → 18 ≤ R →
    ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R, InteriorRegularity q R D₁

/-- The spectral half of the final premise: zero-curvature crossing data of the left twist,
for the first-order coefficient `D₁ = lim ε⁻¹ D(ε)` of the correction, at cofinal dyadic
scales and radii.  NOT proved here. -/
def VacuumLeftSpectral : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ D₁ : TwistSpace (2^j) R →L[ℝ] TwistSpace (2^j) R,
      Tendsto (fun ε : ℝ => ε⁻¹ • extD (2^j) R ε 1) (𝓝[>] 0) (𝓝 D₁) →
        PathCrossing (2^j) R (leftTwist (2^j) R) D₁

/-- **Final reduction of this round.** -/
theorem goalNeg2_of_interiorSoft_vacuumLeftSpectral (hs : InteriorSoft)
    (hc : VacuumLeftSpectral) : GoalNeg2 := by
  apply goalNeg2_of_cofinalLeftVacuum
  intro j₀
  obtain ⟨j, hj, hRs⟩ := hc j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hcr⟩ := hRs R₀
  have hq : 0 < 2^j := by positivity
  obtain ⟨D₁, hreg⟩ := hs (2^j) R hq hR hR18
  exact ⟨R, hRR, hR, hR18, D₁, leftRegularity_of_interior hq hR (by nlinarith) hreg,
    hcr D₁ hreg.2.2⟩

theorem not_interiorSoft_and_spectral_of_goalPos1 (h : GoalPos1) :
    ¬ (InteriorSoft ∧ VacuumLeftSpectral) :=
  fun h' => goalNeg2_of_interiorSoft_vacuumLeftSpectral h'.1 h'.2 (goalPos2_iff_goalPos1.mpr h)

end InteriorFamily

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
#print axioms ContFamT
#print axioms contT_inv_coe
#print axioms contT_holonomyElem
#print axioms contT_holonomyElemInv
#print axioms contT_reHolonomy
#print axioms contT_imHolonomy
#print axioms contT_RMap
#print axioms contT_curlMat
#print axioms contT_a1
#print axioms contT_a4
#print axioms contT_tr_re3
#print axioms contT_bilPlaq
#print axioms contT_deltaPrimeBil
#print axioms contT_curlInner
#print axioms contT_inner_delta
#print axioms contT_deltaKLocCLM
#print axioms uMat_continuous
#print axioms Ug_coe
#print axioms dilU_contFamT
#print axioms tendsto_clm_comp
#print axioms extA_joint_tendsto
#print axioms leftTwist_zero
#print axioms InteriorRegularity
#print axioms leftRegularity_of_interior
#print axioms InteriorSoft
#print axioms VacuumLeftSpectral
#print axioms goalNeg2_of_interiorSoft_vacuumLeftSpectral
#print axioms not_interiorSoft_and_spectral_of_goalPos1

end AdalyFormal.Round9.Guarded.AnalyticR1

/-!
Round 9 (analytic route, pass 2): the soft premise of pass 1 is a theorem.

Pass 1 (`AnalyticR1`) reduced `GoalNeg2` to `InteriorSoft ∧ VacuumLeftSpectral`.  This
appendix proves `InteriorSoft`: along the curved dilated family `ε ↦ dilU q R ε 1` (curvature
on the round-4 defect line, trivial exterior), for every scale `q > 0` and every even radius
`R ≥ 18`, the all-plaquette carrier and the dressing `W` are continuous at `ε = 0`, and the
localized correction satisfies `Δ⁽²⁾(ε)/ε → D₁`.  The proof is soft analysis of the frozen
assembly:
* the gauge projection is written with the frozen closed form `M1Site.Rproj_eq_strat`
  (`R = 1 - X Γ⁻¹ X*`), continuous where the Dirichlet operator and `Γ` are units;
* the raw blocking step is jointly smooth in (curvature, field) (the frozen `SG` calculus
  over the parameter space `ℝ × X`), so its first and second field jets are continuous;
* the localized source is smooth in the curvature and vanishes at the flat point;
* at the flat point the Dirichlet operator, `Γ` (frozen `MS6.exists_Gami_strat`) and `Q*`
  (frozen `W6F.qs_injective_strat`) are units/injective, and the flat localized carrier of
  the dilated tower is positive definite: a vanishing form forces a curl-free field, which
  is the gradient of an explicit longitudinal potential; the level-1 constraint rows
  telescope along the longitudinal chain of blocks, and the frozen final step applies.

Consequences: `goalNeg2_of_vacuumLeftSpectral : VacuumLeftSpectral → GoalNeg2` and
`cofinalTwistSeparation_of_twistVacuumCrossing : CofinalTwistVacuumCrossing →
CofinalTwistSeparation`.  Both premises are spectral statements about the vacuum (zero
curvature) operators only.  Neither premise is proved here; no pinned goal is proved here.
-/
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## A. Finite-dimensional topology -/
section Topo

theorem tendsto_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {α : Type*} {l : Filter α} {g : α → E} {g₀ : E}
    (h : ∀ w : E, Tendsto (fun a => ⟪w, g a⟫) l (𝓝 ⟪w, g₀⟫)) : Tendsto g l (𝓝 g₀) := by
  let b := stdOrthonormalBasis ℝ E
  have e : ∀ x : E, x = ∑ i, ⟪b i, x⟫ • b i := fun x => (b.sum_repr' x).symm
  rw [e g₀]
  have hg : g = fun a => ∑ i, ⟪b i, g a⟫ • b i := funext fun a => e (g a)
  rw [hg]
  exact tendsto_finsetSum _ (fun i _ => (h (b i)).smul_const (b i))

theorem tendsto_clm_of_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : Type*} {l : Filter α} {f : α → E →L[ℝ] F} {f₀ : E →L[ℝ] F}
    (h : ∀ x, Tendsto (fun a => f a x) l (𝓝 (f₀ x))) : Tendsto f l (𝓝 f₀) := by
  let b := stdOrthonormalBasis ℝ E
  have e : ∀ g : E →L[ℝ] F, g = ∑ i, (innerSL ℝ (b i)).smulRight (g (b i)) := by
    intro g
    ext x
    have hx : x = ∑ i, ⟪b i, x⟫ • b i := (b.sum_repr' x).symm
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul]
  rw [e f₀]
  have hf : f = fun a => ∑ i, (innerSL ℝ (b i)).smulRight (f a (b i)) := funext fun a => e (f a)
  rw [hf]
  refine tendsto_finsetSum _ (fun i _ => ?_)
  exact ((ContinuousLinearMap.smulRightL ℝ E F (innerSL ℝ (b i))).continuous.tendsto _).comp (h (b i))

theorem tendsto_clm_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {α : Type*} {l : Filter α} {f : α → E →L[ℝ] F} {f₀ : E →L[ℝ] F}
    (h : ∀ x y, Tendsto (fun a => ⟪y, f a x⟫) l (𝓝 ⟪y, f₀ x⟫)) : Tendsto f l (𝓝 f₀) :=
  tendsto_clm_of_apply (fun x => tendsto_of_inner (fun y => h x y))

end Topo

/-! ## B. `𝔰𝔲(2)`-valued fields -/
section SuTwoFields

open AdalyFormal.Balaban.CovariantOperators (SuTwo)

theorem inner_suTwo (X Y : SuTwo) :
    ⟪X, Y⟫ = -(1 / 2 : ℝ) * (Matrix.trace ((X : Matrix (Fin 2) (Fin 2) ℂ) *
      (Y : Matrix (Fin 2) (Fin 2) ℂ))).re := rfl

theorem tendsto_suTwo_of_coe {α : Type*} {l : Filter α} {g : α → SuTwo} {g₀ : SuTwo}
    (h : Tendsto (fun a => ((g a : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) l
      (𝓝 ((g₀ : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ))) : Tendsto g l (𝓝 g₀) := by
  apply tendsto_of_inner
  intro w
  simp only [inner_suTwo]
  have hc : Continuous fun Y : Matrix (Fin 2) (Fin 2) ℂ =>
      -(1 / 2 : ℝ) * (Matrix.trace ((w : Matrix (Fin 2) (Fin 2) ℂ) * Y)).re :=
    continuous_const.mul (Complex.continuous_re.comp
      ((continuous_const.matrix_mul continuous_id).matrix_trace))
  exact (hc.tendsto _).comp h

theorem continuous_suTwo_of_coe {X : Type*} [TopologicalSpace X] {g : X → SuTwo}
    (h : Continuous fun x => ((g x : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) : Continuous g :=
  continuous_iff_continuousAt.mpr fun x => tendsto_suTwo_of_coe (h.tendsto x)

theorem tendsto_piLp_suTwo {ι : Type*} [Fintype ι] {α : Type*} {l : Filter α}
    {g : α → PiLp 2 (fun _ : ι => SuTwo)} {g₀ : PiLp 2 (fun _ : ι => SuTwo)}
    (h : ∀ i, Tendsto (fun a => ((WithLp.ofLp (g a) i : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) l
      (𝓝 ((WithLp.ofLp g₀ i : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ))) : Tendsto g l (𝓝 g₀) := by
  apply tendsto_of_inner
  intro w
  simp only [PiLp.inner_apply]
  refine tendsto_finsetSum _ (fun i _ => ?_)
  have hi := tendsto_suTwo_of_coe (h i)
  exact ((continuous_const.inner continuous_id).tendsto _).comp hi

theorem continuous_piLp_suTwo {ι : Type*} [Fintype ι] {X : Type*} [TopologicalSpace X]
    {g : X → PiLp 2 (fun _ : ι => SuTwo)}
    (h : ∀ i, Continuous fun x => ((WithLp.ofLp (g x) i : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) :
    Continuous g :=
  continuous_iff_continuousAt.mpr fun x => tendsto_piLp_suTwo (fun i => (h i).tendsto x)

theorem continuous_coe_suTwo {X : Type*} [TopologicalSpace X] {g : X → SuTwo} (h : Continuous g) :
    Continuous fun x => ((g x : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) :=
  continuous_subtype_val.comp h

end SuTwoFields

/-! ## C. Site-level operators along a continuous family of link configurations -/
section Family

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.D1Literal (ContFam SU2m)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy)
open AdalyFormal.Balaban.QjComposite (stepAverage)

variable {L : PeriodicLatticeExtent}

theorem cont_coarsePathHolonomy {V : ℝ → Cfg L} (hV : ContFam V) (s : ℕ) (p : List (Fin 3)) :
    ∀ y, Continuous fun ε => ((coarsePathHolonomy s (V ε) y p : SU2m) :
      Matrix (Fin 2) (Fin 2) ℂ) := by
  induction p with
  | nil =>
    intro y
    exact continuous_const
  | cons μ rest ih =>
    intro y
    show Continuous fun ε => (((V ε (y, μ)) * coarsePathHolonomy s (V ε)
      (AdalyFormal.Balaban.CoarseCurl.coarseShift y s μ) rest : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)
    exact (hV _).matrix_mul (ih _)

theorem cont_RMap_coe {X : Type*} [TopologicalSpace X] {g : X → SU2m}
    (hg : Continuous fun ε => ((g ε : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) {Y : X → SuTwo}
    (hY : Continuous fun ε => ((Y ε : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) :
    Continuous fun ε => ((RMap (g ε) (Y ε) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have e : (fun ε => ((RMap (g ε) (Y ε) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun ε => (g ε : Matrix (Fin 2) (Fin 2) ℂ) * (Y ε : Matrix (Fin 2) (Fin 2) ℂ) *
        star ((g ε : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext ε
    exact RMap_coe_apply _ _
  rw [e]
  exact (hg.matrix_mul hY).matrix_mul hg.star

theorem cont_gradL2 {V : ℝ → Cfg L} (hV : ContFam V) : Continuous fun ε => gradL2 (V ε) := by
  refine continuous_clm_apply.mpr (fun f => ?_)
  refine continuous_piLp_suTwo (fun b => ?_)
  show Continuous fun ε => ((gradValueCovariant (V ε) (WithLp.ofLp f) b : SuTwo) :
    Matrix (Fin 2) (Fin 2) ℂ)
  unfold gradValueCovariant
  simp only [Submodule.coe_sub]
  exact (cont_RMap_coe (hV b) continuous_const).sub continuous_const

theorem cont_adjoint {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] :
    Continuous fun M : E →L[ℝ] F => ContinuousLinearMap.adjoint M :=
  (ContinuousLinearMap.adjoint : (E →L[ℝ] F) ≃ₗᵢ⋆[ℝ] (F →L[ℝ] E)).continuous

theorem cont_gradAdj {V : ℝ → Cfg L} (hV : ContFam V) : Continuous fun ε => gradAdj (V ε) :=
  cont_adjoint.comp (cont_gradL2 hV)

theorem cont_lapFull {V : ℝ → Cfg L} (hV : ContFam V) : Continuous fun ε => lapFull (V ε) :=
  (cont_gradAdj hV).clm_comp (cont_gradL2 hV)

theorem Qcomposite_one' (bg : ℕ → Cfg L) (ell : ℕ) (lam : PeriodicLatticeSite L → SuTwo) :
    AdalyFormal.Balaban.QjComposite.Qcomposite bg ell 1 lam = stepAverage (ell ^ 0) (bg 0) ell lam :=
  rfl

theorem bgTower_zero' (G : TowerGeom L) (U : Cfg L) : bgTower G U 0 = U := rfl

theorem cont_Qlev {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) {j : ℕ} (hj : j ≤ 1)
    (y : PeriodicLatticeSite L) : Continuous fun ε => Qlev G (V ε) j y := by
  refine continuous_clm_apply.mpr (fun f => ?_)
  refine continuous_suTwo_of_coe ?_
  simp only [Qlev_apply]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · simp only [AdalyFormal.Balaban.QjComposite.Qcomposite_zero]
    exact continuous_const
  · simp only [Qcomposite_one', bgTower_zero', stepAverage, Submodule.coe_smul, Submodule.coe_sum]
    exact continuous_const.smul (continuous_finsetSum _ (fun x _ =>
      cont_RMap_coe (cont_coarsePathHolonomy hV _ _ _) continuous_const))

theorem cont_Qpa {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) (hk : G.k = 1) (a : ℝ) :
    Continuous fun ε => Qpa G (V ε) a := by
  classical
  unfold Qpa
  refine continuous_finsetSum _ (fun j hj => continuous_finsetSum _ (fun y _ => ?_))
  have hj1 : j ≤ 1 := by rw [Finset.mem_range] at hj; omega
  by_cases hy : y ∈ G.Lam j
  · simp only [hy, if_true]
    exact continuous_const.smul ((cont_adjoint.comp (cont_Qlev hV G hj1 y)).clm_comp
      (cont_Qlev hV G hj1 y))
  · simp only [hy, if_false]
    exact continuous_const

theorem cont_DelpA {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) (hk : G.k = 1) (a : ℝ) :
    Continuous fun ε => DelpA G (V ε) a := by
  unfold DelpA
  exact (continuous_const.clm_comp ((cont_lapFull hV).add (cont_Qpa hV G hk a))).clm_comp
    continuous_const

open AdalyFormal.M1Site in
theorem cont_LP {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) (hk : G.k = 1) (a : ℝ) :
    Continuous fun ε => LP G (V ε) a := by
  unfold LP
  exact (cont_DelpA hV G hk a).add continuous_const

open AdalyFormal.M1Site in
theorem cont_QpP {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) (hk : G.k = 1) (a : ℝ) :
    Continuous fun ε => QpP G (V ε) a := by
  refine continuous_clm_apply.mpr (fun f => ?_)
  refine continuous_piLp_suTwo (fun p => ?_)
  cases p with
  | inl q =>
    have hj : q.1.1.val ≤ 1 := by have := q.1.1.isLt; omega
    simp only [QpP_inl, Submodule.coe_smul]
    exact continuous_const.smul (continuous_coe_suTwo
      ((cont_Qlev hV G hj _).clm_apply continuous_const))
  | inr x =>
    simp only [QpP_inr]
    exact continuous_const

end Family

/-! ## D. The gauge projection, `W` and `T` near a configuration where the constraint Gram is a unit

The frozen `M1Site.Rproj_eq_strat` gives `R v = v - X Γ⁻¹ X* v`, `X = (Δ'_a + 1 - Ω₀)⁻¹ Q'*`,
`Γ = X* X`, at every configuration where `Δ'_a + 1 - Ω₀` and `Γ` are units.  Both conditions are open,
so near such a configuration the projection is a continuous expression. -/
section Gauge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1Site
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.D1Literal (ContFam SU2m)

variable {L : PeriodicLatticeExtent}

/-- `Γ = X* X`. -/
noncomputable def Gam (G : TowerGeom L) (U : Cfg L) (a : ℝ) : YP G →L[ℝ] YP G :=
  ContinuousLinearMap.adjoint (Xop G U a) ∘L Xop G U a

theorem Rproj_formula (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 < wq G a j)
    (hu : IsUnit (LP G U a)) (hΓ : IsUnit (Gam G U a)) :
    Rproj G U = 1 - Xop G U a ∘L (Ring.inverse (Gam G U a) ∘L
      ContinuousLinearMap.adjoint (Xop G U a)) := by
  have hG1 : ∀ u, (ContinuousLinearMap.adjoint (Xop G U a) ∘L Xop G U a)
      (Ring.inverse (Gam G U a) u) = u := by
    intro u
    have h := Ring.mul_inverse_cancel _ hΓ
    exact congrArg (fun T : YP G →L[ℝ] YP G => T u) h
  ext1 v
  rw [Rproj_eq_strat G U a hw hu _ hG1 v]
  simp only [sub_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply]

theorem continuousAt_inverse_comp {X : Type*} [TopologicalSpace X] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : X → E →L[ℝ] E} {x₀ : X} (hf : ContinuousAt f x₀) (hu : IsUnit (f x₀)) :
    ContinuousAt (fun x => Ring.inverse (f x)) x₀ := by
  have h1 := NormedRing.inverse_continuousAt hu.unit
  rw [hu.unit_spec] at h1
  exact h1.comp hf

theorem continuousAt_clm_comp {X : Type*} [TopologicalSpace X] {E F G' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G'] [NormedSpace ℝ G'] {g : X → F →L[ℝ] G'} {f : X → E →L[ℝ] F} {x₀ : X}
    (hg : ContinuousAt g x₀) (hf : ContinuousAt f x₀) :
    ContinuousAt (fun x => (g x).comp (f x)) x₀ := by
  have hc : Continuous (fun p : (F →L[ℝ] G') × (E →L[ℝ] F) => p.1.comp p.2) :=
    continuous_fst.clm_comp continuous_snd
  exact (hc.tendsto (g x₀, f x₀)).comp (hg.prodMk_nhds hf)

section
variable {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) (hk : G.k = 1) (a : ℝ) {ε₀ : ℝ}
  (hu : IsUnit (LP G (V ε₀) a))
include hV hk hu

theorem continuousAt_LinvP : ContinuousAt (fun ε => LinvP G (V ε) a) ε₀ :=
  continuousAt_inverse_comp (cont_LP hV G hk a).continuousAt hu

theorem continuousAt_Xop : ContinuousAt (fun ε => Xop G (V ε) a) ε₀ :=
  continuousAt_clm_comp (continuousAt_LinvP hV G hk a hu)
    (cont_adjoint.comp (cont_QpP hV G hk a)).continuousAt

theorem continuousAt_Gam : ContinuousAt (fun ε => Gam G (V ε) a) ε₀ :=
  continuousAt_clm_comp (cont_adjoint.continuousAt.comp (continuousAt_Xop hV G hk a hu))
    (continuousAt_Xop hV G hk a hu)

variable (hw : ∀ j, 0 < wq G a j) (hΓ : IsUnit (Gam G (V ε₀) a))
include hw hΓ

theorem continuousAt_Rproj : ContinuousAt (fun ε => Rproj G (V ε)) ε₀ := by
  have hX := continuousAt_Xop hV G hk a hu
  have hGc := continuousAt_Gam hV G hk a hu
  have hGi := continuousAt_inverse_comp hGc hΓ
  have hF : ContinuousAt (fun ε => (1 : SiteL2 L →L[ℝ] SiteL2 L) - Xop G (V ε) a ∘L
      (Ring.inverse (Gam G (V ε) a) ∘L ContinuousLinearMap.adjoint (Xop G (V ε) a))) ε₀ :=
    continuousAt_const.sub (continuousAt_clm_comp hX
      (continuousAt_clm_comp hGi (cont_adjoint.continuousAt.comp hX)))
  have h1 : ∀ᶠ ε in 𝓝 ε₀, IsUnit (LP G (V ε) a) :=
    ((cont_LP hV G hk a).tendsto ε₀).eventually
      ((Units.isOpen (R := SiteL2 L →L[ℝ] SiteL2 L)).mem_nhds hu)
  have h2 : ∀ᶠ ε in 𝓝 ε₀, IsUnit (Gam G (V ε) a) :=
    hGc.eventually ((Units.isOpen (R := YP G →L[ℝ] YP G)).mem_nhds hΓ)
  refine hF.congr ?_
  filter_upwards [h1, h2] with ε hε1 hε2
  exact (Rproj_formula G (V ε) a hw hε1 hε2).symm

theorem continuousAt_Tfull : ContinuousAt (fun ε => Tfull G (V ε)) ε₀ :=
  continuousAt_clm_comp (continuousAt_Rproj hV G hk a hu hw hΓ) (cont_gradAdj hV).continuousAt

theorem continuousAt_Wop : ContinuousAt (fun ε => Wop G (V ε) a) ε₀ := by
  have hR := continuousAt_Rproj hV G hk a hu hw hΓ
  have hL := continuousAt_LinvP hV G hk a hu
  unfold Wop
  exact continuousAt_const.sub (continuousAt_clm_comp (cont_gradL2 hV).continuousAt
    (continuousAt_clm_comp (continuousAt_clm_comp hL continuousAt_const)
      (continuousAt_clm_comp hR (cont_gradAdj hV).continuousAt)))

end

end Gauge

/-! ## E. The Dirichlet operator is a unit at every configuration (frozen `CvOX1`, outside the
`DrEquiv` closure; statements and proofs copied verbatim up to the namespace) -/
section DirichletUnit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant)
open AdalyFormal.Balaban.SuTwoInner (hsInner hsInner_RMap hsInner_self_nonneg hsInner_self_eq_zero)

open Fin.NatCast

variable {L : PeriodicLatticeExtent}

theorem ajSeq_pos {a : ℝ} (ha : 0 < a) {ell : ℕ} (hell : 2 ≤ ell) (j : ℕ) : 0 < ajSeq a ell j := by
  unfold ajSeq
  split_ifs with h
  · exact ha
  · unfold AdalyFormal.Balaban.ConstantA.aSeq
    have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
    have hpos : (0 : ℝ) < (ell : ℝ) * ell := by positivity
    have hd : 0 < a / ((ell : ℝ) * ell) := by positivity
    have h4 : (4 : ℝ) ≤ (ell : ℝ) * ell := by nlinarith
    have hda : a / ((ell : ℝ) * ell) < a := by
      rw [div_lt_iff₀ hpos]; nlinarith [mul_le_mul_of_nonneg_left h4 ha.le]
    exact AdalyFormal.Balaban.ConstantA.aSeqAux_pos a _ ha hd hda _

theorem Qpa_nonneg (G : TowerGeom L) (U : Cfg L) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell) (f : SiteL2 L) :
    0 ≤ ⟪f, Qpa G U a f⟫ := by
  rw [inner_Qpa]
  refine Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun y _ => ?_))
  split_ifs
  · exact mul_nonneg (mul_nonneg (ajSeq_pos ha hell j).le (pow_nonneg (Nat.cast_nonneg _) _)) (sq_nonneg _)
  · exact le_rfl


theorem delpA_inner_ge (G : TowerGeom L) (U : Cfg L) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell) (f : SiteL2 L) :
    ‖gradL2 U (siteMask G.Om0 f)‖ ^ 2 + ‖f - siteMask G.Om0 f‖ ^ 2 ≤ ⟪f, (DelpA G U a + (1 - siteMask G.Om0)) f⟫ := by
  set m := siteMask G.Om0 with hm
  have hsym : ∀ u v : SiteL2 L, ⟪m u, v⟫ = ⟪u, m v⟫ := fun u v => siteMask_symm _ u v
  have hidem : ∀ u : SiteL2 L, m (m u) = m u := fun u => siteMask_idem _ u
  have e1 : ⟪f, DelpA G U a f⟫ = ⟪m f, lapFull U (m f)⟫ + ⟪m f, Qpa G U a (m f)⟫ := by
    unfold DelpA
    simp only [ContinuousLinearMap.comp_apply, add_apply]
    rw [← hsym, inner_add_right]
  have e2 : ⟪f, ((1 : SiteL2 L →L[ℝ] SiteL2 L) - m) f⟫ = ‖f - m f‖ ^ 2 := by
    simp only [sub_apply, one_apply_eq_self]
    rw [← real_inner_self_eq_norm_sq]
    have h0 : ⟪m f, f - m f⟫ = 0 := by
      rw [inner_sub_right]
      have a1 : ⟪m f, m f⟫ = ⟪f, m f⟫ := by rw [hsym, hidem]
      have a2 : ⟪m f, f⟫ = ⟪f, m f⟫ := real_inner_comm _ _
      rw [a1, a2, sub_self]
    have hdec : f = (f - m f) + m f := by abel
    calc ⟪f, f - m f⟫ = ⟪(f - m f) + m f, f - m f⟫ := by rw [← hdec]
      _ = ⟪f - m f, f - m f⟫ := by rw [inner_add_left, h0, add_zero]
  have e3 : ⟪m f, lapFull U (m f)⟫ = ‖gradL2 U (m f)‖ ^ 2 := by
    unfold lapFull gradAdj
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have e4 := Qpa_nonneg G U ha hell (m f)
  show _ ≤ ⟪f, DelpA G U a f + ((1 : SiteL2 L →L[ℝ] SiteL2 L) - m) f⟫
  rw [inner_add_right, e1, e2, e3]
  linarith

/-- covariantly constant site fields have constant `hsInner (f x) (f x)`. -/
theorem covConst_norm (U : Cfg L) (f : SiteL2 L) (h : gradL2 U f = 0) (x y : PeriodicLatticeSite L) :
    hsInner (f x) (f x) = hsInner (f y) (f y) := by
  have hb : ∀ b : AdalyFormal.Balaban.AdmissibleSubspace.Bond L, RMap (U b) (f (periodicLatticeShift b.1 b.2)) = f b.1 := by
    intro b
    have := congrFun (congrArg WithLp.ofLp h) b
    rw [gradL2_apply] at this
    simp only [gradValueCovariant] at this
    exact sub_eq_zero.mp this
  have hstep : ∀ (z : PeriodicLatticeSite L) (μ : Fin 3), hsInner (f (periodicLatticeShift z μ)) (f (periodicLatticeShift z μ)) = hsInner (f z) (f z) := by
    intro z μ
    have := hb (z, μ)
    simp only [] at this
    rw [← hsInner_RMap (U (z, μ)) (f (periodicLatticeShift z μ)) (f (periodicLatticeShift z μ)), this]
  have hiter : ∀ (z : PeriodicLatticeSite L) (μ : Fin 3) (j : ℕ),
      hsInner (f (Function.update z μ (z μ + (Nat.cast j : Fin (L μ + 1))))) (f (Function.update z μ (z μ + (Nat.cast j : Fin (L μ + 1))))) = hsInner (f z) (f z) := by
    intro z μ j
    induction j with
    | zero => simp
    | succ j ih =>
      have : Function.update z μ (z μ + (Nat.cast (j + 1) : Fin (L μ + 1))) =
          periodicLatticeShift (Function.update z μ (z μ + (Nat.cast j : Fin (L μ + 1)))) μ := by
        unfold periodicLatticeShift
        rw [Function.update_self, Function.update_idem]
        congr 1
        rw [Nat.cast_succ]
        abel
      rw [this, hstep, ih]
  have hupd : ∀ (z : PeriodicLatticeSite L) (μ : Fin 3) (v : Fin (L μ + 1)),
      hsInner (f (Function.update z μ v)) (f (Function.update z μ v)) = hsInner (f z) (f z) := by
    intro z μ v
    have := hiter z μ (v - z μ).val
    rw [Fin.cast_val_eq_self, add_sub_cancel] at this
    exact this
  have hall : ∀ z w : PeriodicLatticeSite L, hsInner (f w) (f w) = hsInner (f z) (f z) := by
    intro z w
    have hw : w = Function.update (Function.update (Function.update z 0 (w 0)) 1 (w 1)) 2 (w 2) := by
      funext ν
      fin_cases ν <;> simp [Function.update]
    rw [hw, hupd, hupd, hupd]
  exact (hall x y).symm

theorem delpA_unit (G : TowerGeom L) (U : Cfg L) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell)
    (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    IsUnit (DelpA G U a + (1 - siteMask G.Om0)) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  set X : SiteL2 L →L[ℝ] SiteL2 L := DelpA G U a + (1 - siteMask G.Om0) with hX
  have hinj : Function.Injective X := by
    refine (injective_iff_map_eq_zero X).mpr (fun f hf => ?_)
    have h1 := delpA_inner_ge G U ha hell f
    rw [hf, inner_zero_right] at h1
    have hs1 := sq_nonneg ‖gradL2 U (siteMask G.Om0 f)‖
    have hs2 := sq_nonneg ‖f - siteMask G.Om0 f‖
    have hD : ‖gradL2 U (siteMask G.Om0 f)‖ ^ 2 = 0 := by linarith
    have hR : ‖f - siteMask G.Om0 f‖ ^ 2 = 0 := by linarith
    have hfm : f = siteMask G.Om0 f :=
      sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero)).mp hR))
    have hDm : gradL2 U (siteMask G.Om0 f) = 0 := norm_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero)).mp hD)
    have hDf : gradL2 U f = 0 := by rw [← hfm] at hDm; exact hDm
    obtain ⟨x0, hx0⟩ := hout
    have hx0f : f x0 = 0 := by
      have : (siteMask G.Om0 f) x0 = 0 := by rw [siteMask_apply, if_neg hx0]
      rw [← hfm] at this; exact this
    ext x
    have := covConst_norm U f hDf x x0
    rw [hx0f] at this
    have h0 : hsInner (f x) (f x) = 0 := by
      rw [this]; exact AdalyFormal.Balaban.DeltaKU.hsInner_zero_right _
    have := hsInner_self_eq_zero h0
    simp [this]
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (X : SiteL2 L →ₗ[ℝ] SiteL2 L))).mp hinj⟩


theorem wq_pos (G : TowerGeom L) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell) (j : ℕ) :
    0 < AdalyFormal.M1Site.wq G a j := by
  unfold AdalyFormal.M1Site.wq
  have : (0 : ℝ) < G.ell := by exact_mod_cast (by omega : 0 < G.ell)
  exact mul_pos (ajSeq_pos ha hell j) (pow_pos this j)

end DirichletUnit

end AdalyFormal.Round9.Guarded.AnalyticR2

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## F. Jets of the raw averaging along a smooth family of backgrounds

The frozen `SG` calculus (`R2Raw3`, `R2RawX`) is stated over an arbitrary normed parameter space.
Taking the parameter space `ℝ × X` (curvature, coordinate field), the frozen proof of `SG_rawStep`
goes through with the background varying smoothly: the raw one-step averaging is jointly smooth in
(curvature, field) at `(0, 0)` whenever the background at curvature `0` is regular.  Its first and
second field derivatives at the zero field (the printed jets `QlinStepL`, `D2StepL`) are therefore
continuous in the curvature at `0` (`ContDiffAt.fderiv`). -/
section Jets

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS coarseBondVar gammaVarStrided loopVar)

variable {L : PeriodicLatticeExtent}

theorem tendsto_clm_of_apply' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : Type*} {l : Filter α} {f : α → E →L[ℝ] F} {f₀ : E →L[ℝ] F}
    (h : ∀ x, Tendsto (fun a => f a x) l (𝓝 (f₀ x))) : Tendsto f l (𝓝 f₀) := by
  let b := Module.finBasis ℝ E
  let c : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have e : ∀ g : E →L[ℝ] F, g = ∑ i, (c i).smulRight (g (b i)) := by
    intro g
    ext x
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, c,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul]
  rw [e f₀]
  have hf : f = fun a => ∑ i, (c i).smulRight (f a (b i)) := funext fun a => e (f a)
  rw [hf]
  refine tendsto_finsetSum _ (fun i _ => ?_)
  exact ((ContinuousLinearMap.smulRightL ℝ E F (c i)).continuous.tendsto _).comp (h (b i))

/-- Smooth links at curvature `0` (Frobenius matrix norm). -/
def SmoothAt0 (V : ℝ → PeriodicLinkConfiguration SU2 L) : Prop :=
  ∀ b, ContDiffAt ℝ ⊤ (fun ε => ((V ε b : SU2) : M2)) 0

section Fam
variable (V : ℝ → PeriodicLinkConfiguration SU2 L) (hV : SmoothAt0 V)

include hV in
theorem SG_V0 (b : PeriodicLatticeEdge L) : SG (fun q : ℝ × XS L => V q.1 b) := by
  show ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => ((V q.1 b : SU2) : M2)) 0
  exact ContDiffAt.comp (g := fun ε : ℝ => ((V ε b : SU2) : M2)) (f := fun q : ℝ × XS L => q.1)
    (0 : ℝ × XS L) (hV b) contDiffAt_fst

theorem SG_V1 (b : PeriodicLatticeEdge L) : SG (fun q : ℝ × XS L => expCfgX q.2 b) := by
  have h : ContDiffAt ℝ ⊤ (fun a : XS L => ((expCfgX a b : SU2) : M2)) 0 := SG_expCfgX b
  show ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => ((expCfgX q.2 b : SU2) : M2)) 0
  exact ContDiffAt.comp (g := fun a : XS L => ((expCfgX a b : SU2) : M2)) (f := fun q : ℝ × XS L => q.2)
    (0 : ℝ × XS L) h contDiffAt_snd

include hV in
theorem SG_prod (b : PeriodicLatticeEdge L) :
    SG (fun q : ℝ × XS L => expCfgX q.2 b * V q.1 b) :=
  (SG_V1 b).mul (SG_V0 V hV b)

theorem SG_loopVar_fam (s ell : ℕ) (W : ℝ × XS L → PeriodicLinkConfiguration SU2 L)
    (hW : ∀ b, SG (fun q => W q b)) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    SG (fun q => loopVar s ell (W q) c x) := by
  unfold loopVar gammaVarStrided coarseBondVar
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) => SG.hol s W hW p y
  exact (((h _ _).mul (h _ _)).mul (h _ _).inv).mul (h _ _).inv

theorem SG_sbg_fam (s ell : ℕ) (W : ℝ × XS L → PeriodicLinkConfiguration SU2 L)
    (hW : ∀ b, SG (fun q => W q b)) (c : PeriodicLatticeEdge L)
    (hreg : ∀ x ∈ stepBlockOf c.1 s ell, ((loopVar s ell (W 0) c x : SU2) : M2) ∈ LogReg) :
    SG (fun q => stridedBlockedGauge su2LogExp s ell (W q) c) := by
  unfold stridedBlockedGauge
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) => SG.hol s W hW p y
  refine SG.mul ?_ (by unfold coarseBondVar; exact h _ _)
  have := SG_su2Exp_sum_log (E := ℝ × XS L) (stepBlockOf c.1 s ell) (((ell : ℚ) ^ 3)⁻¹)
    (fun x q => loopVar s ell (W q) c x) (fun x _ => SG_loopVar_fam s ell W hW c x)
    (fun x hx => hreg x hx)
  simpa [su2LogExp_log, su2LogExp_exp] using this

include hV in
theorem SG_rProd_fam (s : ℕ) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    SG (fun q : ℝ × XS L => rProd s (V q.1) (expCfgX q.2) y p) := by
  have h1 := SG.hol (E := ℝ × XS L) s (fun q => fun b => expCfgX q.2 b * V q.1 b)
    (fun b => SG_prod V hV b) p y
  have h2 := SG.hol (E := ℝ × XS L) s (fun q => V q.1) (fun b => SG_V0 V hV b) p y
  have e : (fun q : ℝ × XS L => rProd s (V q.1) (expCfgX q.2) y p)
      = fun q => coarsePathHolonomy s (fun b => expCfgX q.2 b * V q.1 b) y p *
          (coarsePathHolonomy s (V q.1) y p)⁻¹ := by
    funext q
    exact rProd_eq s (V q.1) (expCfgX q.2) y p
  rw [e]
  exact SG.mul_inv h1 h2

include hV in
theorem SG_su2Exp_sBlock_fam (s ell : ℕ) (y : PeriodicLatticeSite L) :
    SG (fun q : ℝ × XS L => su2Exp (sBlock s ell (V q.1) (expCfgX q.2) y)) := by
  unfold sBlock
  exact SG_su2Exp_sum_log (E := ℝ × XS L) (stepBlockOf y s ell) (((ell : ℚ) ^ 3)⁻¹)
    (fun x q => rProd s (V q.1) (expCfgX q.2) y (coarseGammaPath s y x))
    (fun x _ => SG_rProd_fam V hV s y _)
    (fun x _ => by
      show ((rProd s (V 0) (expCfgX (0 : XS L)) y _ : SU2) : M2) ∈ LogReg
      rw [rProd_expCfgX_zero]; exact one_mem_LogReg)

include hV in
theorem SG_su2Exp_neg_sBlock_fam (s ell : ℕ) (y : PeriodicLatticeSite L) :
    SG (fun q : ℝ × XS L => su2Exp (-(sBlock s ell (V q.1) (expCfgX q.2) y))) := by
  have := SG_su2Exp_sum_log (E := ℝ × XS L) (stepBlockOf y s ell) (-((ell : ℚ) ^ 3)⁻¹)
    (fun x q => rProd s (V q.1) (expCfgX q.2) y (coarseGammaPath s y x))
    (fun x _ => SG_rProd_fam V hV s y _)
    (fun x _ => by
      show ((rProd s (V 0) (expCfgX (0 : XS L)) y _ : SU2) : M2) ∈ LogReg
      rw [rProd_expCfgX_zero]; exact one_mem_LogReg)
  unfold sBlock
  simpa [neg_smul, Finset.sum_neg_distrib] using this

include hV in
/-- The raw one-step averaging is jointly smooth in (curvature, field) at `(0, 0)`. -/
theorem SG_rawStep_fam (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    SG (fun q : ℝ × XS L => rawStep s ell (V q.1) (expCfgX q.2) c) := by
  have e : (fun q : ℝ × XS L => rawStep s ell (V q.1) (expCfgX q.2) c)
      = fun q => su2Exp (-(sBlock s ell (V q.1) (expCfgX q.2) c.1))
        * stridedBlockedGauge su2LogExp s ell (fun b => expCfgX q.2 b * V q.1 b) c
        * su2Exp (sBlock s ell (V q.1) (expCfgX q.2) (cPlusS s ell c))
        * (stridedBlockedGauge su2LogExp s ell (V q.1) c)⁻¹ := by
    funext q; exact rawStep_simp s ell (V q.1) (expCfgX q.2) c
  unfold SG; rw [e]
  have h1 := SG_su2Exp_neg_sBlock_fam V hV s ell c.1
  have h2 : SG (fun q : ℝ × XS L =>
      stridedBlockedGauge su2LogExp s ell (fun b => expCfgX q.2 b * V q.1 b) c) := by
    refine SG_sbg_fam s ell (fun q => fun b => expCfgX q.2 b * V q.1 b) (fun b => SG_prod V hV b) c ?_
    intro x hx
    have e0 : (fun b => expCfgX (0 : XS L) b * V 0 b) = V 0 := by
      funext b; rw [expCfgX_zero]; exact one_mul _
    show ((loopVar s ell (fun b => expCfgX ((0 : ℝ × XS L).2) b * V ((0 : ℝ × XS L).1) b) c x : SU2) : M2)
      ∈ LogReg
    rw [show ((0 : ℝ × XS L).2) = (0 : XS L) from rfl, show ((0 : ℝ × XS L).1) = (0 : ℝ) from rfl, e0]
    exact hreg c x hx
  have h3 := SG_su2Exp_sBlock_fam V hV s ell (cPlusS s ell c)
  have h4 : SG (fun q : ℝ × XS L => (stridedBlockedGauge su2LogExp s ell (V q.1) c)⁻¹) := by
    refine SG.inv (SG_sbg_fam s ell (fun q => V q.1) (fun b => SG_V0 V hV b) c ?_)
    intro x hx
    exact hreg c x hx
  exact (((h1.mul h2).mul h3).mul h4)

include hV in
theorem contDiffAt_qStep_fam (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => qStepX s ell (V q.1) q.2 c) 0 := by
  have h1 : ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => su2Log (rawStep s ell (V q.1) (expCfgX q.2) c)) 0 :=
    AdalyFormal.Balaban.SmoothLog.su2Log_comp_contDiffAt
      (G := fun q : ℝ × XS L => rawStep s ell (V q.1) (expCfgX q.2) c)
      (SG_rawStep_fam V hV s ell hreg c) (rawStep_expCfgX_zero s ell (V 0) c)
  exact fromM2L.contDiff.contDiffAt.comp (0 : ℝ × XS L) h1

include hV in
/-- First jet: continuity in the curvature of the field derivative at the zero field. -/
theorem continuousAt_fderiv_qStep (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    ContinuousAt (fun ε => fderiv ℝ (qStepComp s ell (V ε) c) 0) 0 := by
  have h := contDiffAt_qStep_fam V hV s ell hreg c
  have h2 : ContDiffAt ℝ 0 (fun ε : ℝ => fderiv ℝ (fun a : XS L => qStepX s ell (V ε) a c)
      ((fun _ : ℝ => (0 : XS L)) ε)) 0 :=
    ContDiffAt.fderiv (f := fun (ε : ℝ) (a : XS L) => qStepX s ell (V ε) a c)
      (g := fun _ : ℝ => (0 : XS L)) h contDiffAt_const (by simp)
  exact h2.continuousAt

include hV in
/-- Second jet: continuity in the curvature of the second field derivative at the zero field. -/
theorem continuousAt_fderiv2_qStep (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    ContinuousAt (fun ε => fderiv ℝ (fderiv ℝ (qStepComp s ell (V ε) c)) 0) 0 := by
  have h := contDiffAt_qStep_fam V hV s ell hreg c
  have hl : ContDiffAt ℝ ⊤ (fun z : (ℝ × XS L) × XS L => ((z.1.1, z.2) : ℝ × XS L))
      ((0 : ℝ × XS L), (0 : XS L)) :=
    (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hΦ' : ContDiffAt ℝ ⊤ ((fun q : ℝ × XS L => qStepX s ell (V q.1) q.2 c) ∘
      (fun z : (ℝ × XS L) × XS L => ((z.1.1, z.2) : ℝ × XS L))) ((0 : ℝ × XS L), (0 : XS L)) :=
    ContDiffAt.comp (g := fun q : ℝ × XS L => qStepX s ell (V q.1) q.2 c)
      (f := fun z : (ℝ × XS L) × XS L => ((z.1.1, z.2) : ℝ × XS L)) ((0 : ℝ × XS L), (0 : XS L)) h hl
  have hΦ : ContDiffAt ℝ ⊤ (Function.uncurry fun (x : ℝ × XS L) (b : XS L) =>
      qStepX s ell (V x.1) b c) ((0 : ℝ × XS L), (fun x : ℝ × XS L => x.2) 0) := hΦ'
  have hΨ : ContDiffAt ℝ ⊤ (fun x : ℝ × XS L =>
      fderiv ℝ (fun b : XS L => qStepX s ell (V x.1) b c) x.2) 0 :=
    ContDiffAt.fderiv (f := fun (x : ℝ × XS L) (b : XS L) => qStepX s ell (V x.1) b c)
      (g := fun x : ℝ × XS L => x.2) hΦ contDiffAt_snd (by simp)
  have h2 : ContDiffAt ℝ 0 (fun ε : ℝ => fderiv ℝ (fun a : XS L =>
      fderiv ℝ (fun b : XS L => qStepX s ell (V ε) b c) a) ((fun _ : ℝ => (0 : XS L)) ε)) 0 :=
    ContDiffAt.fderiv (f := fun (ε : ℝ) (a : XS L) =>
        fderiv ℝ (fun b : XS L => qStepX s ell (V ε) b c) a)
      (g := fun _ : ℝ => (0 : XS L)) hΨ contDiffAt_const (by simp)
  exact h2.continuousAt

end Fam

end Jets

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## G. The assembled pinned data along a smooth curvature family

For a family `ε ↦ V ε` of backgrounds with smooth links and a regular flat point, on a tower of
depth one (`k = 1`): the bond-sector constraint map `Q` is continuous at `ε = 0`, the second jet
`C²` is jointly continuous, and every assembled carrier `dataS sD sJ` is continuous at `ε = 0` as
soon as `W` and `T` are.  The constrained inverse `H` is continuous wherever the carrier and
`Q G Q*` are units.  If the source `J` vanishes at `ε = 0` and has a curvature derivative, the
localized correction `Δ⁽²⁾(ε)/ε` converges. -/
section Assembly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.D1Literal (ContFam)

variable {L : PeriodicLatticeExtent}

theorem tendsto_clm_apply₂ {α : Type*} {l : Filter α} {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : α → E →L[ℝ] F} {x : α → E}
    {f₀ : E →L[ℝ] F} {x₀ : E} (hf : Tendsto f l (𝓝 f₀)) (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun a => f a (x a)) l (𝓝 (f₀ x₀)) :=
  ((continuous_fst.clm_apply continuous_snd).tendsto (f₀, x₀)).comp (hf.prodMk_nhds hx)

/-- The coordinate map of `𝔰𝔲(2)`-valued bond fields, as a bounded operator. -/
noncomputable def suCoordL : BondFnL2 L →L[ℝ] XS L := LinearMap.toContinuousLinearMap suCoord

theorem QfullOf_apply (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (p : BIdx G) :
    WithLp.ofLp (QfullOf G U A) p
      = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G U p.1 A)) p.2.1 := rfl

theorem C2fullOf_apply (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (p : BIdx G) :
    WithLp.ofLp (C2fullOf G U A) p
      = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (C2rawB G U p.1 A)) p.2.1 := rfl

theorem QlinB_one_coe (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (c : PeriodicLatticeEdge L) :
    ((WithLp.ofLp (QlinB G U 1 A) c : SuTwo) : M2) =
      toM2 (fderiv ℝ (qStepComp (G.ell ^ 0) G.ell U c) 0 (suCoord A)) := rfl

theorem C2rawB_zero' (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) : C2rawB G U 0 A = 0 := by
  refine PiLp.ext (fun b => ?_)
  apply Subtype.ext
  show (((1 / 2 : ℝ) • suCoordInv (D2CompL G.ell (bgTower G U) 0 (suCoord A) (suCoord A))) b : M2) = 0
  simp [D2CompL, suCoordInv]

theorem C2rawB_one_coe (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (c : PeriodicLatticeEdge L) :
    ((WithLp.ofLp (C2rawB G U 1 A) c : SuTwo) : M2) =
      (1 / 2 : ℝ) • toM2 (fderiv ℝ (fderiv ℝ (qStepComp (G.ell ^ 0) G.ell U c)) 0
        (suCoord A) (suCoord A)) := by
  show (((1 / 2 : ℝ) • suCoordInv (D2CompL G.ell (bgTower G U) 1 (suCoord A) (suCoord A))) c : M2) = _
  simp only [D2CompL, LinearMap.mk₂_apply, QlinCompL_zero, ContinuousLinearMap.id_apply]
  simp [D2StepL_apply, suCoordInv]
  rfl

section BondSector
variable (V : ℝ → Cfg L) (hV : SmoothAt0 V)
  (G : TowerGeom L) (hk : G.k = 1) (hreg : RegBg (G.ell ^ 0) G.ell (V 0))

include hV hreg in
theorem tendsto_QlinB1_coe (A : BondFnL2 L) (c : PeriodicLatticeEdge L) :
    Tendsto (fun ε => ((WithLp.ofLp (QlinB G (V ε) 1 A) c : SuTwo) : M2)) (𝓝 0)
      (𝓝 ((WithLp.ofLp (QlinB G (V 0) 1 A) c : SuTwo) : M2)) := by
  simp only [QlinB_one_coe]
  have h := continuousAt_fderiv_qStep V hV (G.ell ^ 0) G.ell hreg c
  exact (toM2L.continuous.tendsto _).comp (tendsto_clm_apply₂ h tendsto_const_nhds)

include hV hreg hk in
theorem continuousAt_QfullOf : ContinuousAt (fun ε => QfullOf G (V ε)) 0 := by
  refine tendsto_clm_of_apply (fun A => tendsto_piLp_suTwo (fun p => ?_))
  obtain ⟨⟨j, hj⟩, r⟩ := p
  have hj1 : j = 0 ∨ j = 1 := by omega
  rcases hj1 with rfl | rfl
  · simp only [QfullOf_apply, QlinB_zero]
    exact tendsto_const_nhds
  · simp only [QfullOf_apply, Submodule.coe_smul]
    exact (tendsto_QlinB1_coe V hV G hreg A r.1).const_smul _

include hV hreg hk in
theorem tendsto_C2fullOf {X : ℝ → BondFnL2 L} {X₀ : BondFnL2 L} (hX : Tendsto X (𝓝 0) (𝓝 X₀)) :
    Tendsto (fun ε => C2fullOf G (V ε) (X ε)) (𝓝 0) (𝓝 (C2fullOf G (V 0) X₀)) := by
  refine tendsto_piLp_suTwo (fun p => ?_)
  obtain ⟨⟨j, hj⟩, r⟩ := p
  have hj1 : j = 0 ∨ j = 1 := by omega
  rcases hj1 with rfl | rfl
  · simp only [C2fullOf_apply, C2rawB_zero']
    exact tendsto_const_nhds
  · simp only [C2fullOf_apply, Submodule.coe_smul, C2rawB_one_coe]
    have h2 := continuousAt_fderiv2_qStep V hV (G.ell ^ 0) G.ell hreg r.1
    have hs : Tendsto (fun ε => suCoord (X ε)) (𝓝 0) (𝓝 (suCoord X₀)) :=
      ((suCoordL (L := L)).continuous.tendsto _).comp hX
    exact (((toM2L.continuous.tendsto _).comp
      (tendsto_clm_apply₂ (tendsto_clm_apply₂ h2 hs) hs)).const_smul _).const_smul _

end BondSector

theorem Ginv_dataS_eq (sD sJ : PlaqSel) (P : IngrBParams) :
    (dataS sD sJ P).Ginv = (pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))
      + (ContinuousLinearMap.adjoint ((Tfull P.G P.U).comp (iE P.G))).comp
          ((Tfull P.G P.U).comp (iE P.G))
      + (pE P.G).comp ((MassFull P.G P.a (bondSectorOf P.G P.U)).comp (iE P.G)) := rfl

/-- The assembled data along a curvature family, typed on the fixed carrier of the tower. -/
noncomputable def dataFam (sD sJ : PlaqSel) {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (V : ℝ → Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) :
    ℝ → BaseDataS ↥(bondSupp (geomOf ell k S)) (SiteL2 (scaleUp ell k Lu)) (FSp (geomOf ell k S)) :=
  fun ε => dataS sD sJ (gparams ell k Lu hell S (V ε) a Lam)

theorem Ginv_dataFam_eq (sD sJ : PlaqSel) {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (V : ℝ → Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (ε : ℝ) :
    (dataFam sD sJ hell S V a Lam ε).Ginv =
      (pE (geomOf ell k S)).comp ((DpiFullS sD (geomOf ell k S) (V ε) a).comp (iE (geomOf ell k S)))
      + (ContinuousLinearMap.adjoint ((Tfull (geomOf ell k S) (V ε)).comp (iE (geomOf ell k S)))).comp
          ((Tfull (geomOf ell k S) (V ε)).comp (iE (geomOf ell k S)))
      + (pE (geomOf ell k S)).comp ((MassFull (geomOf ell k S) a
          (bondSectorOf (geomOf ell k S) (V ε))).comp (iE (geomOf ell k S))) := rfl

/-- Continuity of every assembled carrier at `ε = 0`, from continuity of `W`, `T` and `Q`. -/
theorem continuousAt_Ginv_dataS (sD sJ : PlaqSel) {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (V : ℝ → Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (hVc : ContFam V)
    (hW : ContinuousAt (fun ε => Wop (geomOf ell k S) (V ε) a) 0)
    (hT : ContinuousAt (fun ε => Tfull (geomOf ell k S) (V ε)) 0)
    (hQ : ContinuousAt (fun ε => QfullOf (geomOf ell k S) (V ε)) 0) :
    ContinuousAt (fun ε => (dataFam sD sJ hell S V a Lam ε).Ginv) 0 := by
  simp only [Ginv_dataFam_eq]
  have hΔ : ContinuousAt (fun ε => DeltaS sD (geomOf ell k S) (V ε)) 0 :=
    (AdalyFormal.D1Literal.cont_deltaKLocCLM hVc (sD _ (geomOf ell k S))).continuousAt
  have hDpi : ContinuousAt (fun ε => DpiFullS sD (geomOf ell k S) (V ε) a) 0 :=
    continuousAt_clm_comp (cont_adjoint.continuousAt.comp hW) (continuousAt_clm_comp hΔ hW)
  have hTi : ContinuousAt (fun ε => (Tfull (geomOf ell k S) (V ε)).comp (iE (geomOf ell k S))) 0 :=
    continuousAt_clm_comp hT continuousAt_const
  have hM : ContinuousAt (fun ε => MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) (V ε))) 0 :=
    continuousAt_clm_comp (cont_adjoint.continuousAt.comp hQ)
      (continuousAt_clm_comp continuousAt_const hQ)
  refine ((continuousAt_clm_comp continuousAt_const (continuousAt_clm_comp hDpi continuousAt_const)).add
    (continuousAt_clm_comp (cont_adjoint.continuousAt.comp hTi) hTi)).add ?_
  exact continuousAt_clm_comp continuousAt_const (continuousAt_clm_comp hM continuousAt_const)

/-- The constrained inverse `H = G Q* (Q G Q*)⁻¹` is continuous where both inverses are units. -/
theorem continuousAt_H {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hGinv : ContinuousAt (fun ε => (D ε).Ginv) 0)
    (hQ : ContinuousAt (fun ε => (D ε).Q) 0) (hQs : ContinuousAt (fun ε => (D ε).Qs) 0)
    (hu : IsUnit (D 0).Ginv) (hN : IsUnit (((D 0).Q.comp (D 0).G).comp (D 0).Qs)) :
    ContinuousAt (fun ε => (D ε).H) 0 := by
  have hG : ContinuousAt (fun ε => (D ε).G) 0 := continuousAt_inverse_comp hGinv hu
  have hNc : ContinuousAt (fun ε => ((D ε).Q.comp (D ε).G).comp (D ε).Qs) 0 :=
    continuousAt_clm_comp (continuousAt_clm_comp hQ hG) hQs
  exact continuousAt_clm_comp (continuousAt_clm_comp hG hQs) (continuousAt_inverse_comp hNc hN)

theorem inner_polarization {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : E →L[ℝ] E) (hM : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫) (x y : E) :
    ⟪y, M x⟫ = (⟪x + y, M (x + y)⟫ - ⟪x - y, M (x - y)⟫) / 4 := by
  have h1 : ⟪x, M y⟫ = ⟪y, M x⟫ := by rw [← hM, real_inner_comm]
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, h1]
  ring

/-- The quadratic form of `Δ⁽²⁾(ε)/ε` converges to `2⟪H(0) C²(0) A, J'⟫`. -/
theorem tendsto_Delta2_div_form {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hL : ∀ ε, (D ε).Laws)
    (hH : ContinuousAt (fun ε => (D ε).H) 0)
    (hC2 : ∀ A, Tendsto (fun ε => (D ε).C2 A) (𝓝 0) (𝓝 ((D 0).C2 A)))
    (J' : E) (hJ : Tendsto (fun ε => ε⁻¹ • (D ε).J) (𝓝[≠] 0) (𝓝 J')) (A : E) :
    Tendsto (fun ε => ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫) (𝓝[≠] 0)
      (𝓝 (2 * ⟪(D 0).H ((D 0).C2 A), J'⟫)) := by
  have e : ∀ ε : ℝ, ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫
      = 2 * ⟪(D ε).H ((D ε).C2 A), ε⁻¹ • (D ε).J⟫ := by
    intro ε
    rw [smul_apply, real_inner_smul_right, ((D ε).Delta2_spec (hL ε)).2 A,
      real_inner_smul_right]
    ring
  simp only [e]
  have hHC : Tendsto (fun ε => (D ε).H ((D ε).C2 A)) (𝓝[≠] 0) (𝓝 ((D 0).H ((D 0).C2 A))) :=
    tendsto_clm_apply₂ (hH.tendsto.mono_left nhdsWithin_le_nhds)
      ((hC2 A).mono_left nhdsWithin_le_nhds)
  exact (Filter.Tendsto.inner (𝕜 := ℝ) hHC hJ).const_mul (2 : ℝ)

/-- **The first-order coefficient of the localized correction.**  If `H` is continuous at `0`, the
second jet `C²` converges pointwise, and the source has a curvature derivative `J'` (with
`J(0) = 0` built into the hypothesis), then `Δ⁽²⁾(ε)/ε` converges. -/
theorem tendsto_Delta2_div {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hL : ∀ ε, (D ε).Laws)
    (hH : ContinuousAt (fun ε => (D ε).H) 0)
    (hC2 : ∀ A, Tendsto (fun ε => (D ε).C2 A) (𝓝 0) (𝓝 ((D 0).C2 A)))
    (J' : E) (hJ : Tendsto (fun ε => ε⁻¹ • (D ε).J) (𝓝[≠] 0) (𝓝 J')) :
    ∃ D₁ : E →L[ℝ] E, Tendsto (fun ε => ε⁻¹ • (D ε).Delta2 (hL ε)) (𝓝[≠] 0) (𝓝 D₁) := by
  obtain ⟨β, hβ⟩ := (hL 0).C2_quad
  let β1 : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun x y => 2 * ⟪(D 0).H (β x y), J'⟫)
    (fun x1 x2 y => by simp only [map_add, LinearMap.add_apply, inner_add_left]; ring)
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, real_inner_smul_left, smul_eq_mul]; ring)
    (fun x y1 y2 => by simp only [map_add, inner_add_left]; ring)
    (fun c x y => by simp only [map_smul, real_inner_smul_left, smul_eq_mul]; ring)
  refine ⟨symmOp β1, ?_⟩
  have hdiag : ∀ A, Tendsto (fun ε => ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫) (𝓝[≠] 0)
      (𝓝 ⟪A, symmOp β1 A⟫) := by
    intro A
    rw [inner_symmOp_diag]
    have e2 : β1 A A = 2 * ⟪(D 0).H ((D 0).C2 A), J'⟫ := by
      simp only [β1, LinearMap.mk₂_apply, hβ A]
    rw [e2]
    exact tendsto_Delta2_div_form D hL hH hC2 J' hJ A
  have hsym : ∀ ε : ℝ, ∀ x y, ⟪(ε⁻¹ • (D ε).Delta2 (hL ε)) x, y⟫ = ⟪x, (ε⁻¹ • (D ε).Delta2 (hL ε)) y⟫ := by
    intro ε x y
    simp only [smul_apply, real_inner_smul_left, real_inner_smul_right,
      ((D ε).Delta2_spec (hL ε)).1 x y]
  apply tendsto_clm_of_inner
  intro x y
  have e1 : ∀ ε : ℝ, ⟪y, (ε⁻¹ • (D ε).Delta2 (hL ε)) x⟫ =
      (⟪x + y, (ε⁻¹ • (D ε).Delta2 (hL ε)) (x + y)⟫ - ⟪x - y, (ε⁻¹ • (D ε).Delta2 (hL ε)) (x - y)⟫) / 4 :=
    fun ε => inner_polarization _ (hsym ε) x y
  rw [inner_polarization (symmOp β1) (symmOp_symm β1) x y]
  simp only [e1]
  exact ((hdiag (x + y)).sub (hdiag (x - y))).div_const 4

/-- Any limit of `Δ⁽²⁾(ε)/ε` along `ε ↓ 0` has the quadratic form `A ↦ 2⟪H(0) C²(0) A, J'⟫`. -/
theorem limit_Delta2_div_form {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hL : ∀ ε, (D ε).Laws)
    (hH : ContinuousAt (fun ε => (D ε).H) 0)
    (hC2 : ∀ A, Tendsto (fun ε => (D ε).C2 A) (𝓝 0) (𝓝 ((D 0).C2 A)))
    (J' : E) (hJ : Tendsto (fun ε => ε⁻¹ • (D ε).J) (𝓝[≠] 0) (𝓝 J'))
    (D₁ : E →L[ℝ] E) (hD₁ : Tendsto (fun ε => ε⁻¹ • (D ε).Delta2 (hL ε)) (𝓝[>] 0) (𝓝 D₁)) (A : E) :
    ⟪A, D₁ A⟫ = 2 * ⟪(D 0).H ((D 0).C2 A), J'⟫ := by
  have h1 : Tendsto (fun ε => ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫) (𝓝[>] 0) (𝓝 ⟪A, D₁ A⟫) :=
    (Filter.Tendsto.inner (𝕜 := ℝ) tendsto_const_nhds (tendsto_clm_apply₂ hD₁ tendsto_const_nhds))
  have h2 := (tendsto_Delta2_div_form D hL hH hC2 J' hJ A).mono_left
    (nhdsWithin_mono _ (fun x (hx : (0 : ℝ) < x) => ne_of_gt hx))
  exact tendsto_nhds_unique h1 h2

end Assembly

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## H. The curvature derivative of the localized source

The localized source `J = D* Im ∂U` (`ZLocJ.JSU2Loc`) is a finite expression in link matrices,
plaquette holonomies, the trace and conjugate transposes; along a family with smooth links it is
smooth, it vanishes at the flat point (`JSU2Loc_trivial`), so `J(ε)/ε` converges. -/
section SourceSmooth

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2 (SG SG.mul SG.inv conjTR conjTR_apply)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem holonomyElemInv imHolonomy)
open AdalyFormal.Balaban.SourceJ (piProj DstarDir)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo conjByAmbient)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.IngredientFamily (JSU2Loc JfieldLoc FnuMuLoc)

variable {L : PeriodicLatticeExtent} (V : ℝ → PeriodicLinkConfiguration SU2 L) (hV : SmoothAt0 V)
include hV

theorem SG_holonomyElem (p : PeriodicLatticePlaquette L) :
    SG (fun ε => holonomyElem (V ε) p) := by
  have hS : ∀ b, SG (fun ε => V ε b) := hV
  have e : (fun ε => holonomyElem (V ε) p) = fun ε =>
      V ε (p.1, p.2.1.1) * V ε (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) *
        (V ε (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ * (V ε (p.1, p.2.1.2))⁻¹ := by
    funext ε; rfl
  rw [e]
  exact (((hS _).mul (hS _)).mul (hS _).inv).mul (hS _).inv

theorem cd_imHolonomy (p : PeriodicLatticePlaquette L) :
    ContDiffAt ℝ ⊤ (fun ε => imHolonomy (V ε) p) 0 := by
  have h1 : ContDiffAt ℝ ⊤ (fun ε => ((holonomyElem (V ε) p : SU2) : M2)) 0 := SG_holonomyElem V hV p
  have h2 : ContDiffAt ℝ ⊤ (fun ε => ((holonomyElemInv (V ε) p : SU2) : M2)) 0 :=
    (SG_holonomyElem V hV p).inv
  exact (h1.sub h2).const_smul _

omit hV in
theorem cd_piProj {f : ℝ → M2} (hf : ContDiffAt ℝ ⊤ f 0) :
    ContDiffAt ℝ ⊤ (fun ε => piProj (f ε)) 0 := by
  have htr : ContDiffAt ℝ ⊤ (fun ε => Matrix.trace (f ε)) 0 :=
    (((Matrix.traceLinearMap (Fin 2) ℝ ℂ).toContinuousLinearMap).contDiff.contDiffAt).comp 0 hf
  simp only [piProj]
  exact hf.sub ((htr.div_const 2).smul contDiffAt_const)

theorem cd_FnuMuLoc (P : Set (PeriodicLatticePlaquette L)) (ν μ : Fin 3) (y : PeriodicLatticeSite L) :
    ContDiffAt ℝ ⊤ (fun ε => FnuMuLoc P (V ε) ν μ y) 0 := by
  classical
  unfold FnuMuLoc
  by_cases hlt : ν < μ
  · simp only [dif_pos hlt]
    by_cases hp : (y, (⟨(ν, μ), hlt⟩ : PeriodicPlaquetteDirections)) ∈ P
    · simp only [if_pos hp]
      exact cd_piProj (cd_imHolonomy V hV _)
    · simp only [if_neg hp]
      exact contDiffAt_const
  · simp only [dif_neg hlt]
    by_cases hgt : μ < ν
    · simp only [dif_pos hgt]
      by_cases hp : (y, (⟨(μ, ν), hgt⟩ : PeriodicPlaquetteDirections)) ∈ P
      · simp only [if_pos hp]
        exact (cd_piProj (cd_imHolonomy V hV _)).neg
      · simp only [if_neg hp]
        exact contDiffAt_const
    · simp only [dif_neg hgt]
      exact contDiffAt_const

theorem cd_DstarDir (ν : Fin 3) {Gf : ℝ → PeriodicLatticeSite L → M2}
    (hG : ∀ y, ContDiffAt ℝ ⊤ (fun ε => Gf ε y) 0) (x : PeriodicLatticeSite L) :
    ContDiffAt ℝ ⊤ (fun ε => DstarDir (V ε) ν (Gf ε) x) 0 := by
  have hS : ∀ b, SG (fun ε => V ε b) := hV
  have hg : ContDiffAt ℝ ⊤ (fun ε => (((V ε (periodicLatticeShiftBack x ν, ν))⁻¹ : SU2) : M2)) 0 :=
    (hS _).inv
  have hgH : ContDiffAt ℝ ⊤ (fun ε => ((((V ε (periodicLatticeShiftBack x ν, ν))⁻¹ : SU2) : M2))ᴴ) 0 :=
    conjTR.contDiff.contDiffAt.comp 0 hg
  have e : (fun ε => DstarDir (V ε) ν (Gf ε) x) = fun ε =>
      (((V ε (periodicLatticeShiftBack x ν, ν))⁻¹ : SU2) : M2) * Gf ε (periodicLatticeShiftBack x ν) *
        ((((V ε (periodicLatticeShiftBack x ν, ν))⁻¹ : SU2) : M2))ᴴ - Gf ε x := by
    funext ε; rfl
  rw [e]
  exact ((hg.mul (hG _)).mul hgH).sub (hG x)

theorem cd_JfieldLoc (P : Set (PeriodicLatticePlaquette L)) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ContDiffAt ℝ ⊤ (fun ε => JfieldLoc P (V ε) x μ) 0 := by
  classical
  unfold JfieldLoc
  refine ContDiffAt.sum (fun ν _ => ?_)
  by_cases h : ν = μ
  · simp only [if_pos h]
    exact contDiffAt_const
  · simp only [if_neg h]
    exact cd_DstarDir V hV ν (fun y => cd_FnuMuLoc V hV P ν μ y) x

theorem cd_JSU2Loc (P : Set (PeriodicLatticePlaquette L)) (b : PeriodicLatticeEdge L) :
    ContDiffAt ℝ ⊤ (fun ε => ((JSU2Loc 1 P (V ε) b : SuTwo) : M2)) 0 := by
  have e : (fun ε => ((JSU2Loc 1 P (V ε) b : SuTwo) : M2)) = fun ε =>
      ((-Complex.I) * (((1 : ℝ)⁻¹ ^ 3 : ℝ) : ℂ)) • JfieldLoc P (V ε) b.1 b.2 := by
    funext ε; rfl
  rw [e]
  exact (cd_JfieldLoc V hV P b.1 b.2).const_smul _

/-- The slope of one source component at the flat point. -/
theorem source_slope (P : Set (PeriodicLatticePlaquette L)) (b : PeriodicLatticeEdge L)
    (h0 : ((JSU2Loc 1 P (V 0) b : SuTwo) : M2) = 0) :
    ∃ d : M2, d ∈ suTwo ∧
      Tendsto (fun t : ℝ => t⁻¹ • ((JSU2Loc 1 P (V t) b : SuTwo) : M2)) (𝓝[≠] 0) (𝓝 d) := by
  have hc := cd_JSU2Loc V hV P b
  have hd := (hc.differentiableAt (by simp)).hasDerivAt
  have ht := hd.tendsto_slope_zero
  simp only [zero_add, h0, sub_zero] at ht
  refine ⟨_, ?_, ht⟩
  have hcl : IsClosed (suTwo : Set M2) := Submodule.closed_of_finiteDimensional _
  refine hcl.mem_of_tendsto ht (Filter.Eventually.of_forall (fun t => ?_))
  exact suTwo.smul_mem _ (JSU2Loc 1 P (V t) b).2

end SourceSmooth

section Source

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo BondFnL2)
open AdalyFormal.IngredientFamily (JSU2Loc)

variable {L : PeriodicLatticeExtent}

/-- `J(ε)/ε` converges along a smooth family whose flat point is the trivial background. -/
theorem exists_source_derivative (V : ℝ → PeriodicLinkConfiguration SU2 L) (hV : SmoothAt0 V)
    (hV0 : V 0 = fun _ => 1) (P : Set (PeriodicLatticePlaquette L)) :
    ∃ J' : BondFnL2 L, Tendsto (fun ε : ℝ =>
      ε⁻¹ • (WithLp.toLp 2 (fun b => -(JSU2Loc 1 P (V ε) b)) : BondFnL2 L)) (𝓝[≠] 0) (𝓝 J') := by
  have h0 : ∀ b, ((JSU2Loc 1 P (V 0) b : SuTwo) : M2) = 0 := by
    intro b
    rw [hV0]
    have := AdalyFormal.IngredientFamily.JSU2Loc_trivial (L := L) 1 P b
    exact congrArg Subtype.val this
  choose d hd hlim using fun b => source_slope V hV P b (h0 b)
  refine ⟨WithLp.toLp 2 (fun b => -(⟨d b, hd b⟩ : SuTwo)), tendsto_piLp_suTwo (fun b => ?_)⟩
  have e : ∀ t : ℝ, ((WithLp.ofLp (t⁻¹ • (WithLp.toLp 2 (fun b => -(JSU2Loc 1 P (V t) b)) :
      BondFnL2 L)) b : SuTwo) : M2) = -(t⁻¹ • ((JSU2Loc 1 P (V t) b : SuTwo) : M2)) := by
    intro t
    simp only [PiLp.smul_apply, Submodule.coe_smul, Submodule.coe_neg, smul_neg]
  simp only [e]
  show Tendsto _ _ (𝓝 (-(d b)))
  exact (hlim b).neg

end Source

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## I. The curved dilated family at the flat point: smoothness and the units

`ε ↦ dilU q R ε 1` (curvature `ε` on the round-4 defect line, trivial exterior) has smooth
links and is the trivial background at `ε = 0`.  At the trivial background the Dirichlet
operator, the constraint Gram `Γ` (frozen `MS6.exists_Gami_strat` with `ρ = 0` on the proper
tower of an admissible tower, `MS7.properTower_geomOf`) and `Q*` (frozen `W6F.qs_injective_strat`
with zero drift) are units resp. injective. -/
section DilFamily

open scoped Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (Ug Xm sig Ug_zero)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilPattern dilU)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

theorem contDiff_Xm : ContDiff ℝ ⊤ (fun t : ℝ => Xm t) := by
  have e : (fun t : ℝ => Xm t) = fun t => t • (Complex.I • sig) := by
    funext t
    ext i j
    simp [Xm, Matrix.smul_apply, Complex.real_smul, mul_assoc]
  rw [e]
  exact contDiff_id.smul contDiff_const

theorem contDiffAt_Ug (t₀ : ℝ) : ContDiffAt ℝ ⊤ (fun t : ℝ => ((Ug t : SU2) : M2)) t₀ :=
  (NormedSpace.exp_analytic (Xm t₀)).contDiffAt.comp t₀ contDiff_Xm.contDiffAt

theorem dilU_link_contDiff (q R : ℕ) (e : Bond (scaleUp 2 1 (dilLu q R))) :
    ContDiff ℝ ⊤ (fun ε : ℝ => ((dilU q R ε 1 e : SU2) : M2)) := by
  classical
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [dilU, if_pos he]
    exact contDiff_const
  · simp only [dilU, if_neg he]
    by_cases hp : dilPattern q R e
    · simp only [if_pos hp]
      exact contDiff_iff_contDiffAt.mpr contDiffAt_Ug
    · simp only [if_neg hp]
      exact contDiff_const

theorem dilU_smooth (q R : ℕ) : SmoothAt0 (fun ε : ℝ => dilU q R ε 1) :=
  fun e => (dilU_link_contDiff q R e).contDiffAt

theorem dilU_contFam (q R : ℕ) : AdalyFormal.D1Literal.ContFam (fun ε : ℝ => dilU q R ε 1) :=
  fun e => (dilU_link_contDiff q R e).continuous

end DilFamily

section DilUnits

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLane2 (Ug Ug_zero)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilPattern dilU)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

theorem dilU_zero (q R : ℕ) : dilU q R 0 1 = fun _ => 1 := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [dilU, if_pos he]
    rfl
  · simp only [dilU, if_neg he, ite_self, Ug_zero]

theorem dil_G_k (q R : ℕ) : (geomOf 2 1 (dilTower q R)).k = 1 := rfl
theorem dil_G_ell (q R : ℕ) : (geomOf 2 1 (dilTower q R)).ell = 2 := rfl

theorem dil_out_site (q R : ℕ) (hq : 0 < q) :
    ∃ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)), x ∉ (geomOf 2 1 (dilTower q R)).Om0 := by
  refine ⟨fun _ => 0, ?_⟩
  show ¬ (4 * q ≤ ((0 : Fin _) : ℕ) ∧ _)
  simp only [Fin.val_zero]
  omega

theorem dil_LP_unit (q R : ℕ) (hq : 0 < q) (U : Cfg (scaleUp 2 1 (dilLu q R))) :
    IsUnit (AdalyFormal.M1Site.LP (geomOf 2 1 (dilTower q R)) U 1) :=
  delpA_unit (geomOf 2 1 (dilTower q R)) U one_pos (le_refl 2) (dil_out_site q R hq)

theorem dil_wq_pos (q R : ℕ) (j : ℕ) : 0 < AdalyFormal.M1Site.wq (geomOf 2 1 (dilTower q R)) 1 j :=
  wq_pos (geomOf 2 1 (dilTower q R)) one_pos (le_refl 2) j

theorem bgTower_one {L : PeriodicLatticeExtent} (G : TowerGeom L) (i : ℕ) :
    bgTower G (fun _ => 1) i = fun _ => 1 :=
  AdalyFormal.SliceCoerc.ubarTower_trivial G.ell i

theorem dil_Gam_unit {q R : ℕ} (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    IsUnit (Gam (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1) := by
  obtain ⟨Gi, h1, h2⟩ := AdalyFormal.M1Site.exists_Gami_strat 2 1 (le_refl 2)
    (AdalyFormal.M1Site.hdvd_of_admissible hS) (AdalyFormal.M1Site.properTower_geomOf (by norm_num) hS)
    (fun _ => 1) 1 one_pos 0 le_rfl (by norm_num)
    (fun j _ y _ b _ => by simp)
    (fun j _ y _ i _ z _ _ μ _ => by rw [bgTower_one]; simp)
  refine ⟨⟨Gam (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1, Gi, ?_, ?_⟩, rfl⟩
  · ext1 u; exact h1 u
  · ext1 u; exact h2 u

theorem delW_zero (ell k : ℕ) (hell : 0 < ell) : AdalyFormal.W6.delW ell k (fun _ => 0) = 0 := by
  unfold AdalyFormal.W6.delW AdalyFormal.W6.SS
  simp [AdalyFormal.BondComposite.thetaOf_zero ell hell]

theorem dil_Qs_inj {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R) (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    Function.Injective (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (trivialU (scaleUp 2 1 (dilLu q R))) 1 (dilLam q R)).data.Qs :=
  AdalyFormal.W6.qs_injective_strat (by norm_num) (le_refl 2) hS (by omega) (by omega)
    (trivialU _) 1 (dilLam q R) (fun _ => 0) (AdalyFormal.W6.regTower_triv (by norm_num))
    (AdalyFormal.W6.towerClass_triv (by norm_num)) (fun _ _ => le_rfl)
    (fun _ _ => AdalyFormal.W6.rhoOf_zero_lt 2) (by rw [delW_zero 2 1 (by norm_num)]; norm_num)

end DilUnits

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## J. The flat localized carrier of the dilated tower is positive definite

At the trivial background `⟪x, B x⟫ = ‖χ curl x‖² + ‖T x‖² + Σ a ℓʲ ‖Q x‖²` (`B` the localized
carrier).  If it vanishes, `x` is curl-free on the plaquettes of `Ω₀`, vanishes on every bond not
touching `Ω₁` (level-0 rows of `Q`), and has vanishing level-1 rows.  Integrating `x` along the
longitudinal lines from the left boundary gives a site field `ξ` with `x = D ξ` on the bonds
before the right edge; the level-1 rows telescope along the longitudinal chain of blocks from the
left collar (where `ξ = 0`) to the right collar (where `ξ` is a transverse constant), so the
constant is `0`, `ξ ∈ N(Q')` and `x = D ξ` everywhere; then `T (D ξ) = 0` forces `D ξ = 0`
(the frozen `final_step` argument, copied). -/
section FlatKernel

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dil_fine_size)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one curlValueCovariant
  gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepAverage)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open Fin.NatCast

/-! ### Frozen `NsPtD2.final_step` (outside the `DrEquiv` closure), copied verbatim. -/

theorem siteMask_eq_self_of_supp' {L : PeriodicLatticeExtent} (S : Set (PeriodicLatticeSite L))
    (ξ : SiteL2 L) (h : ∀ x, x ∉ S → ξ x = 0) : siteMask S ξ = ξ := by
  classical
  ext x
  rw [siteMask_apply]
  by_cases hx : x ∈ S
  · rw [if_pos hx]
  · rw [if_neg hx, h x hx]

theorem lapDir_eq_mask_lap' {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (ξ : SiteL2 L)
    (h : ∀ x, x ∉ G.Om0 → ξ x = 0) : lapDir G U ξ = siteMask G.Om0 (lapFull U ξ) := by
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply]
  rw [siteMask_eq_self_of_supp' _ _ h]

theorem final_step' {L : PeriodicLatticeExtent} (G : TowerGeom L) (ξ : SiteL2 L)
    (hξ : ξ ∈ NQp G (flatCfg : Cfg L))
    (hT : Tfull G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ξ) = 0) :
    gradL2 (flatCfg : Cfg L) ξ = 0 := by
  have hsupp := hξ.1
  have hlap := lapDir_eq_mask_lap' G flatCfg ξ hsupp
  have hmem : lapDir G (flatCfg : Cfg L) ξ ∈ RImage G (flatCfg : Cfg L) :=
    Submodule.mem_map.mpr ⟨ξ, hξ, rfl⟩
  have hR : Rproj G (flatCfg : Cfg L) (lapFull (flatCfg : Cfg L) ξ) = 0 := by
    have : Tfull G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ξ) =
        Rproj G (flatCfg : Cfg L) (lapFull (flatCfg : Cfg L) ξ) := rfl
    rw [← this]; exact hT
  have horth : lapFull (flatCfg : Cfg L) ξ ∈ (RImage G (flatCfg : Cfg L))ᗮ := by
    have := hR
    unfold Rproj at this
    exact (Submodule.starProjection_apply_eq_zero_iff _).mp this
  have h1 : ⟪lapDir G (flatCfg : Cfg L) ξ, lapFull (flatCfg : Cfg L) ξ⟫ = 0 :=
    (Submodule.mem_orthogonal _ _).mp horth _ hmem
  have h2 : ⟪lapDir G (flatCfg : Cfg L) ξ, lapFull (flatCfg : Cfg L) ξ⟫ =
      ‖lapDir G (flatCfg : Cfg L) ξ‖ ^ 2 := by
    have e : ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ), lapFull (flatCfg : Cfg L) ξ⟫
        = ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ),
            siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ)⟫ := by
      calc ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ), lapFull (flatCfg : Cfg L) ξ⟫
          = ⟪siteMask G.Om0 (siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ)),
              lapFull (flatCfg : Cfg L) ξ⟫ := by rw [siteMask_idem]
        _ = _ := siteMask_symm _ _ _
    rw [hlap, e, real_inner_self_eq_norm_sq]
  have h3 : lapDir G (flatCfg : Cfg L) ξ = 0 := by
    rw [h2] at h1
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
  have h4 : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = 0 := by
    have : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = ⟪siteMask G.Om0 ξ, lapFull (flatCfg : Cfg L) ξ⟫ := by
      rw [siteMask_eq_self_of_supp' _ _ hsupp]
    rw [this, siteMask_symm, ← hlap, h3, inner_zero_right]
  have h5 : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = ‖gradL2 (flatCfg : Cfg L) ξ‖ ^ 2 := by
    simp only [lapFull, ContinuousLinearMap.comp_apply, gradAdj, ContinuousLinearMap.adjoint_inner_right]
    rw [real_inner_self_eq_norm_sq]
  rw [h5] at h4
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)

/-! ### Coordinates of the dilated tower -/

variable {q R : ℕ}

theorem dsize0 (hq : 0 < q) : scaleUp 2 1 (dilLu q R) 0 + 1 = 12 * (R * q) + 16 * q := by
  have h := dil_fine_size hq R 0
  simpa using h

theorem dsizeT (hq : 0 < q) {μ : Fin 3} (hμ : μ ≠ 0) : scaleUp 2 1 (dilLu q R) μ + 1 = 8 * q := by
  rw [dil_fine_size hq R μ, if_neg hμ]

theorem x0_lt (hq : 0 < q) (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    (x 0).val < 12 * (R * q) + 16 * q := by
  have h1 := (x 0).isLt
  have h2 := dsize0 (R := R) hq
  omega

theorem xT_lt (hq : 0 < q) (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    (x μ).val < 8 * q := by
  have h1 := (x μ).isLt
  have h2 := dsizeT (R := R) hq hμ
  omega

theorem mem_Om0 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∈ (dilTower q R).Om 0 ↔ 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q := Iff.rfl

theorem mem_Om1 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∈ (dilTower q R).Om 1 ↔
      2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q := Iff.rfl

theorem not_mem_Om2 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∉ (dilTower q R).Om 2 := by
  simp [dilTower]

theorem shift_coord_ne {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) {μ ν : Fin 3}
    (h : ν ≠ μ) : (periodicLatticeShift x μ) ν = x ν := by
  unfold periodicLatticeShift
  rw [Function.update_of_ne h]

theorem shift_self_coord {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3) :
    (periodicLatticeShift x μ) μ = x μ + 1 := by
  unfold periodicLatticeShift
  rw [Function.update_self]

theorem shift0_val_lt {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (h : (x 0).val + 1 < L 0 + 1) : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := by
  rw [shift_self_coord, Fin.val_add_one, if_neg]
  intro hc
  rw [hc, Fin.val_last] at h
  omega

theorem shift0_val_last {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (h : (x 0).val + 1 = L 0 + 1) : ((periodicLatticeShift x 0) 0).val = 0 := by
  rw [shift_self_coord, Fin.val_add_one, if_pos]
  ext
  rw [Fin.val_last]
  omega

/-! ### The kernel argument -/

section Kernel
variable (hq : 0 < q) (hR : 1 ≤ R) (A : BondFnL2 (scaleUp 2 1 (dilLu q R)))
  (hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → A b = 0)
  (hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A = 0)

theorem OmGe1_mem {x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))}
    (h : OmGe (geomOf 2 1 (dilTower q R)) 1 x) : x ∈ (dilTower q R).Om 1 := by
  obtain ⟨i, hi1, hik, y, hy, hxy⟩ := h
  have hi : i = 1 := by
    have : i ≤ 1 := hik
    omega
  subst hi
  obtain ⟨hdiv, hyOm, -⟩ := hy
  rw [mem_Om1] at hyOm ⊢
  have h0 := hxy 0
  have hd := hdiv 0
  have hell : (geomOf 2 1 (dilTower q R)).ell = 2 := rfl
  simp only [pow_one, hell] at hd h0
  have hb : 2 ∣ 10 * (R * q) + 12 * q := ⟨5 * (R * q) + 6 * q, by ring⟩
  omega

include hsupp hQ in
theorem A_zero_off {b : Bond (scaleUp 2 1 (dilLu q R))} (h1 : b.1 ∉ (dilTower q R).Om 1)
    (h2 : periodicLatticeShift b.1 b.2 ∉ (dilTower q R).Om 1) : A b = 0 := by
  by_cases hb : b ∈ bondsOm0 (geomOf 2 1 (dilTower q R))
  · have hL : b ∈ bondsLam (geomOf 2 1 (dilTower q R)) 0 := by
      refine ⟨?_, ?_⟩
      · rcases hb with hb | hb
        · exact Or.inl ⟨fun μ => by simp, hb, h1⟩
        · exact Or.inr ⟨fun μ => by simp, hb, h2⟩
      · rintro (h | h)
        · exact h1 (OmGe1_mem h)
        · exact h2 (OmGe1_mem h)
    have h := congrArg (fun v : FSp (geomOf 2 1 (dilTower q R)) => WithLp.ofLp v ⟨0, ⟨b, hL⟩⟩) hQ
    have h' : WithLp.ofLp (QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A) ⟨0, ⟨b, hL⟩⟩ = A b := by
      rw [QfullOf_apply]
      show (((geomOf 2 1 (dilTower q R)).ell : ℝ) ^ 0)⁻¹ •
        (WithLp.ofLp (QlinB (geomOf 2 1 (dilTower q R)) flatCfg 0 A)) b = A b
      rw [QlinB_zero, pow_zero, inv_one, one_smul]
    simp only at h
    rw [h'] at h
    exact h
  · exact hsupp b hb

/-- the site with longitudinal coordinate replaced by `u`. -/
def sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  Function.update z 0 ((u : ℕ) : Fin (scaleUp 2 1 (dilLu q R) 0 + 1))

omit hq A in
theorem sitex_val (hq : 0 < q) (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {u : ℕ}
    (hu : u < 12 * (R * q) + 16 * q) : ((sitex z u) 0).val = u := by
  unfold sitex
  rw [Function.update_self, Fin.val_natCast, dsize0 hq]
  exact Nat.mod_eq_of_lt hu

omit A in
theorem sitex_coord (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) {ν : Fin 3}
    (hν : ν ≠ 0) : (sitex z u) ν = z ν := by
  unfold sitex
  rw [Function.update_of_ne hν]

omit A in
theorem sitex_self (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : sitex z (z 0).val = z := by
  unfold sitex
  rw [Fin.cast_val_eq_self, Function.update_eq_self]

omit A in
theorem sitex_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u v : ℕ) :
    sitex (sitex z v) u = sitex z u := by
  unfold sitex
  rw [Function.update_idem]

omit A in
theorem shift_sitex0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    periodicLatticeShift (sitex z u) 0 = sitex z (u + 1) := by
  unfold periodicLatticeShift sitex
  rw [Function.update_idem, Function.update_self, Nat.cast_succ]

omit A in
theorem shift_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) {μ : Fin 3}
    (hμ : μ ≠ 0) : periodicLatticeShift (sitex z u) μ = sitex (periodicLatticeShift z μ) u := by
  unfold periodicLatticeShift sitex
  rw [Function.update_of_ne hμ, Function.update_comm (Ne.symm hμ)]

omit A in
theorem sitex_of_shift0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    sitex (periodicLatticeShift z 0) u = sitex z u := by
  unfold periodicLatticeShift sitex
  rw [Function.update_idem]

/-- the longitudinal potential. -/
noncomputable def xi (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : SuTwo :=
  ∑ u ∈ Finset.range (z 0).val, A (sitex z u, 0)

include hq in
/-- longitudinal step. -/
theorem xi_shift0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : (z 0).val + 1 < 12 * (R * q) + 16 * q) :
    xi A (periodicLatticeShift z 0) = xi A z + A (z, 0) := by
  unfold xi
  have hz : ((periodicLatticeShift z 0) 0).val = (z 0).val + 1 :=
    shift0_val_lt z (by have h2 := dsize0 (R := R) hq; omega)
  rw [hz, Finset.sum_range_succ]
  simp only [sitex_of_shift0]
  rw [sitex_self]

include hq hR hsupp hQ in
/-- the plaquette identity in the `(0, μ)` plane, from curl-freeness or vanishing of all bonds. -/
theorem trans_step
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (w : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0)
    (hw : (w 0).val + 1 < 12 * (R * q) + 16 * q) :
    A (periodicLatticeShift w μ, 0) - A (w, 0) = A (periodicLatticeShift w 0, μ) - A (w, μ) := by
  classical
  have h0μ : (0 : Fin 3) < μ := by
    rcases Fin.pos_iff_ne_zero.mpr hμ with h
    exact h
  have hw0 : ((periodicLatticeShift w 0) 0).val = (w 0).val + 1 :=
    shift0_val_lt w (by have h2 := dsize0 (R := R) hq; omega)
  have hwμ : (periodicLatticeShift w μ) 0 = w 0 := shift_coord_ne w (Ne.symm hμ)
  have hw0μ : ((periodicLatticeShift (periodicLatticeShift w 0) μ) 0).val = (w 0).val + 1 := by
    rw [shift_coord_ne _ (Ne.symm hμ), hw0]
  have hwμ0 : ((periodicLatticeShift (periodicLatticeShift w μ) 0) 0).val = (w 0).val + 1 := by
    rw [shift0_val_lt _ (by have h2 := dsize0 (R := R) hq; rw [hwμ]; omega), hwμ]
  by_cases hin : 4 * q ≤ (w 0).val ∧ (w 0).val + 1 < 12 * (R * q) + 12 * q
  · let p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)) := (w, ⟨(0, μ), h0μ⟩)
    have hp : p ∈ plaqIn ((dilTower q R).Om 0) := by
      intro e he
      simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton, p] at he
      rcases he with rfl | rfl | rfl | rfl
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
    have hc := hcurl p hp
    simp only [curlValueCovariant, p, flatCfg, RMap_one, LinearMap.id_apply] at hc
    have e : A (periodicLatticeShift w μ, 0) - A (w, 0) - (A (periodicLatticeShift w 0, μ) - A (w, μ)) = 0 := by
      rw [← neg_eq_zero, ← hc]; abel
    exact sub_eq_zero.mp e
  · have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
    have hR1 : ∀ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
        ((x 0).val = (w 0).val ∨ (x 0).val = (w 0).val + 1) → x ∉ (dilTower q R).Om 1 := by
      intro x hx hxm
      rw [mem_Om1] at hxm
      rcases hx with hx | hx <;> rw [hx] at hxm <;>
        (by_cases h4 : 4 * q ≤ (w 0).val
         · have h5 : ¬ ((w 0).val + 1 < 12 * (R * q) + 12 * q) := fun h => hin ⟨h4, h⟩
           omega
         · omega)
    have z1 := A_zero_off A hsupp hQ (b := (w, 0)) (hR1 w (Or.inl rfl)) (hR1 _ (Or.inr hw0))
    have z2 := A_zero_off A hsupp hQ (b := (periodicLatticeShift w 0, μ)) (hR1 _ (Or.inr hw0))
      (hR1 _ (Or.inr hw0μ))
    have z3 := A_zero_off A hsupp hQ (b := (periodicLatticeShift w μ, 0))
      (hR1 (periodicLatticeShift w μ) (Or.inl (by rw [hwμ]))) (hR1 _ (Or.inr hwμ0))
    have z4 := A_zero_off A hsupp hQ (b := (w, μ)) (hR1 w (Or.inl rfl))
      (hR1 (periodicLatticeShift w μ) (Or.inl (by rw [hwμ])))
    rw [z1, z2, z3, z4]

include hq hR hsupp hQ in
/-- transverse step. -/
theorem xi_shiftT
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    xi A (periodicLatticeShift z μ) = xi A z + (A (z, μ) - A (sitex z 0, μ)) := by
  unfold xi
  rw [shift_coord_ne z (Ne.symm hμ)]
  have hz := x0_lt hq z
  have e : ∀ u ∈ Finset.range (z 0).val, A (sitex (periodicLatticeShift z μ) u, 0)
      = A (sitex z u, 0) + (A (sitex z (u + 1), μ) - A (sitex z u, μ)) := by
    intro u hu
    rw [Finset.mem_range] at hu
    have hval : ((sitex z u) 0).val = u := sitex_val hq z (by omega)
    have ht := trans_step hq hR A hsupp hQ hcurl (sitex z u) hμ (by rw [hval]; omega)
    rw [shift_sitex z u hμ, shift_sitex0] at ht
    rw [← sub_eq_iff_eq_add', ht]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_range_sub (fun u => A (sitex z u, μ)),
    sitex_self]

include hq hsupp hQ in
theorem xi_left (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : (z 0).val < 2 * (R * q) + 4 * q) : xi A z = 0 := by
  unfold xi
  refine Finset.sum_eq_zero (fun u hu => ?_)
  rw [Finset.mem_range] at hu
  have hz := x0_lt hq z
  have hv : ((sitex z u) 0).val = u := sitex_val hq z (by omega)
  refine A_zero_off A hsupp hQ ?_ ?_
  · rw [mem_Om1, hv]; omega
  · rw [mem_Om1, shift_sitex0, sitex_val hq z (by omega)]; omega

include hq hsupp hQ in
/-- beyond the right edge of `Ω₁` the potential equals its value at the right edge. -/
theorem xi_right (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : 10 * (R * q) + 12 * q ≤ (z 0).val) :
    xi A z = xi A (sitex z (10 * (R * q) + 12 * q)) := by
  have hz := x0_lt hq z
  have key : ∀ n, 10 * (R * q) + 12 * q + n < 12 * (R * q) + 16 * q →
      xi A (sitex z (10 * (R * q) + 12 * q + n)) = xi A (sitex z (10 * (R * q) + 12 * q)) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have hv : ((sitex z (10 * (R * q) + 12 * q + n)) 0).val = 10 * (R * q) + 12 * q + n :=
        sitex_val hq z (by omega)
      rw [← ih (by omega)]
      have e := xi_shift0 hq A (sitex z (10 * (R * q) + 12 * q + n)) (by rw [hv]; omega)
      rw [shift_sitex0] at e
      rw [show 10 * (R * q) + 12 * q + (n + 1) = 10 * (R * q) + 12 * q + n + 1 by ring, e]
      have h0 : A (sitex z (10 * (R * q) + 12 * q + n), 0) = 0 := by
        refine A_zero_off A hsupp hQ ?_ ?_
        · show sitex z _ ∉ _
          rw [mem_Om1, hv]; omega
        · show periodicLatticeShift (sitex z _) 0 ∉ _
          rw [mem_Om1, shift_sitex0, sitex_val hq z (by omega)]; omega
      rw [h0, add_zero]
  have hk := key ((z 0).val - (10 * (R * q) + 12 * q)) (by omega)
  rw [Nat.add_sub_cancel' h, sitex_self] at hk
  exact hk

/-- the right-edge value of the potential, a function of the transverse coordinates. -/
noncomputable def Iv (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : SuTwo :=
  xi A (sitex z (10 * (R * q) + 12 * q))

include hq hR hsupp hQ in
theorem Iv_shiftT
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    Iv A (periodicLatticeShift z μ) = Iv A z := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  unfold Iv
  rw [← shift_sitex z _ hμ, xi_shiftT hq hR A hsupp hQ hcurl _ hμ]
  have hv : ((sitex z (10 * (R * q) + 12 * q)) 0).val = 10 * (R * q) + 12 * q :=
    sitex_val hq z (by omega)
  have e1 : A (sitex z (10 * (R * q) + 12 * q), μ) = 0 := by
    refine A_zero_off A hsupp hQ ?_ ?_
    · show sitex z _ ∉ _
      rw [mem_Om1, hv]; omega
    · show periodicLatticeShift (sitex z _) μ ∉ _
      rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv]; omega
  have e2 : A (sitex (sitex z (10 * (R * q) + 12 * q)) 0, μ) = 0 := by
    rw [sitex_sitex]
    have hv0 : ((sitex z 0) 0).val = 0 := sitex_val hq z (by omega)
    refine A_zero_off A hsupp hQ ?_ ?_
    · show sitex z 0 ∉ _
      rw [mem_Om1, hv0]; omega
    · show periodicLatticeShift (sitex z 0) μ ∉ _
      rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv0]; omega
  rw [e1, e2, sub_zero, add_zero]

omit hq hR A in
theorem update_shift_succ {L : PeriodicLatticeExtent} (w : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    Function.update w μ (w μ + ((n + 1 : ℕ) : Fin (L μ + 1))) =
      periodicLatticeShift (Function.update w μ (w μ + ((n : ℕ) : Fin (L μ + 1)))) μ := by
  unfold periodicLatticeShift
  rw [Function.update_idem, Function.update_self, Nat.cast_succ, add_assoc]

include hq hR hsupp hQ in
theorem Iv_update
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0)
    (v : Fin (scaleUp 2 1 (dilLu q R) μ + 1)) :
    Iv A (Function.update z μ v) = Iv A z := by
  have hn : ∀ n : ℕ, Iv A (Function.update z μ (z μ + ((n : ℕ) : Fin _))) = Iv A z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [update_shift_succ, Iv_shiftT hq hR A hsupp hQ hcurl _ hμ, ih]
  have h := hn (v - z μ).val
  rw [Fin.cast_val_eq_self, add_sub_cancel] at h
  exact h

omit hq hR A in
theorem Iv_update0 (A : BondFnL2 (scaleUp 2 1 (dilLu q R))) (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (v : Fin (scaleUp 2 1 (dilLu q R) 0 + 1)) : Iv A (Function.update z 0 v) = Iv A z := by
  unfold Iv sitex
  rw [Function.update_idem]

include hq hR hsupp hQ in
theorem Iv_const
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : Iv A z = Iv A (fun _ => 0) := by
  have e : (fun _ => (0 : Fin _) : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) =
      Function.update (Function.update (Function.update z 0 0) 1 0) 2 0 := by
    funext ν
    fin_cases ν <;> simp [Function.update] <;> rfl
  rw [e, Iv_update hq hR A hsupp hQ hcurl _ (by decide), Iv_update hq hR A hsupp hQ hcurl _ (by decide),
    Iv_update0]

omit hq hR A in
theorem coarseShift_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (t : ℕ) :
    coarseShift (sitex z t) 2 0 = sitex z (t + 2) := by
  show periodicLatticeShift (periodicLatticeShift (sitex z t) 0) 0 = _
  rw [shift_sitex0, shift_sitex0]

include hq hR hQ in
/-- one level-1 row along direction `0`: the block sums of the potential agree. -/
theorem row_step (y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (hy1 : 2 ∣ (y 1).val) (hy2 : 2 ∣ (y 2).val) (hy0 : 2 ∣ (y 0).val)
    (hlo : 2 * (R * q) + 4 * q ≤ (y 0).val + 2) (hhi : (y 0).val + 2 ≤ 10 * (R * q) + 12 * q) :
    ∑ w ∈ stepBlockOf (coarseShift y 2 0) 1 2, xi A w = ∑ w ∈ stepBlockOf y 1 2, xi A w := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  have hy0' : ((periodicLatticeShift y 0) 0).val = (y 0).val + 1 := shift0_val_lt y (by omega)
  have hcs0 : ((coarseShift y 2 0) 0).val = (y 0).val + 2 := by
    show ((periodicLatticeShift (periodicLatticeShift y 0) 0) 0).val = _
    rw [shift0_val_lt _ (by rw [hy0']; omega), hy0']
  have hcsT : ∀ ν : Fin 3, ν ≠ 0 → (coarseShift y 2 0) ν = y ν := by
    intro ν hν
    show (periodicLatticeShift (periodicLatticeShift y 0) 0) ν = y ν
    rw [shift_coord_ne _ hν, shift_coord_ne _ hν]
  have hc : (y, (0 : Fin 3)) ∈ bondsLam (geomOf 2 1 (dilTower q R)) 1 := by
    refine ⟨?_, ?_⟩
    · by_cases hya : 2 * (R * q) + 4 * q ≤ (y 0).val
      · left
        show y ∈ (geomOf 2 1 (dilTower q R)).Lam 1
        refine ⟨fun μ => ?_, (mem_Om1 _).mpr ⟨hya, by omega⟩, not_mem_Om2 _⟩
        show 2 ^ 1 ∣ (y μ).val
        fin_cases μ
        · simpa using hy0
        · simpa using hy1
        · simpa using hy2
      · right
        have e1 : coarseShift (y, (0 : Fin 3)).1 ((geomOf 2 1 (dilTower q R)).ell ^ 1) (y, (0 : Fin 3)).2 =
            coarseShift y 2 0 := rfl
        rw [e1]
        show coarseShift y 2 0 ∈ (geomOf 2 1 (dilTower q R)).Lam 1
        refine ⟨fun μ => ?_, (mem_Om1 _).mpr ⟨by rw [hcs0]; omega, by rw [hcs0]; omega⟩, not_mem_Om2 _⟩
        show 2 ^ 1 ∣ ((coarseShift y 2 0) μ).val
        fin_cases μ
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 0).val
          rw [hcs0]; simpa using (Nat.dvd_add hy0 (dvd_refl 2))
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 1).val
          rw [hcsT 1 (by decide)]; simpa using hy1
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 2).val
          rw [hcsT 2 (by decide)]; simpa using hy2
    · rintro (h | h) <;>
        exact not_OmGe_of_lt (G := geomOf 2 1 (dilTower q R)) (lt_of_eq_of_lt (dil_G_k q R) (by norm_num)) _ h
  let p : BIdx (geomOf 2 1 (dilTower q R)) := ⟨1, ⟨(y, 0), hc⟩⟩
  have hrow : WithLp.ofLp (QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A) p = 0 := by
    rw [hQ]; rfl
  have hQrow := AdalyFormal.W6.Qflat_row (ell := 2) (k := 1) (Lu := dilLu q R) (S := dilTower q R)
    (by norm_num) A p
  have hline : AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictSuTwo (2 ^ (p.1 : ℕ))
      (WithLp.ofLp A) (AdalyFormal.W6.rowCB (by norm_num) p) = 0 := by
    rw [← hQrow]; exact hrow
  have hline' : (1 / ((2 : ℕ) : ℝ) ^ 4) • ∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2,
      A (pathSite x 0 i, 0) = 0 := hline
  have hsum : ∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, A (pathSite x 0 i, 0) = 0 := by
    rcases smul_eq_zero.mp hline' with h | h
    · norm_num at h
    · exact h
  have hpt : ∀ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, A (pathSite x 0 i, 0) =
      xi A (coarseShift x 2 0) - xi A x := by
    intro x hx
    have hxb := (mem_blockOf.mp hx) 0
    have hx0 : (x 0).val + 1 < 12 * (R * q) + 16 * q := by omega
    have hsx : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := shift0_val_lt x (by omega)
    have e1 := xi_shift0 hq A x hx0
    have e2 := xi_shift0 hq A (periodicLatticeShift x 0) (by rw [hsx]; omega)
    show _ = xi A (periodicLatticeShift (periodicLatticeShift x 0) 0) - xi A x
    rw [e2, e1, Finset.sum_range_succ, Finset.sum_range_one]
    show A (x, 0) + A (periodicLatticeShift x 0, 0) = _
    abel
  have hfit : ∀ ν : Fin 3, (y ν).val + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; omega
    · have := xT_lt hq y hν
      have h8 := dsizeT (R := R) hq hν
      have hev : 2 ∣ (y ν).val := by
        fin_cases ν
        · exact absurd rfl hν
        · exact hy1
        · exact hy2
      omega
  have hfit' : ∀ ν : Fin 3, ((coarseShift y 2 0) ν).val + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; rw [hcs0]; omega
    · rw [hcsT ν hν]; exact hfit ν
  have hshift := AdalyFormal.CurvBlock.block_sum_shift 1 2 2 0 hfit hfit' (xi A)
  rw [← hshift]
  rw [AdalyFormal.Balaban.QjComposite.stepBlockOf_one] at *
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib] at hsum
  exact sub_eq_zero.mp hsum

include hq hR hsupp hQ in
/-- the block sums vanish along the whole longitudinal chain of blocks. -/
theorem chain_zero (y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (hy1 : 2 ∣ (y 1).val) (hy2 : 2 ∣ (y 2).val) :
    ∀ m : ℕ, 2 * m ≤ 8 * (R * q) + 8 * q + 2 →
      ∑ w ∈ stepBlockOf (sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 1 2, xi A w = 0 := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  intro m
  induction m with
  | zero =>
    intro _
    refine Finset.sum_eq_zero (fun w hw => ?_)
    have hb := ((AdalyFormal.Balaban.QjComposite.mem_stepBlockOf).mp hw) 0
    have hv : ((sitex y (2 * (R * q) + 4 * q - 2 + 2 * 0)) 0).val = 2 * (R * q) + 4 * q - 2 + 2 * 0 :=
      sitex_val hq y (by omega)
    rw [hv] at hb
    exact xi_left hq A hsupp hQ w (by omega)
  | succ m ih =>
    intro hm
    have hv : ((sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 0).val = 2 * (R * q) + 4 * q - 2 + 2 * m :=
      sitex_val hq y (by omega)
    have e : sitex y (2 * (R * q) + 4 * q - 2 + 2 * (m + 1)) =
        coarseShift (sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 2 0 := by
      rw [coarseShift_sitex]
      congr 1
    rw [e, row_step hq hR A hQ _ (by rw [sitex_coord _ _ (by decide)]; exact hy1)
      (by rw [sitex_coord _ _ (by decide)]; exact hy2) (by rw [hv]; omega) (by rw [hv]; omega)
      (by rw [hv]; omega)]
    exact ih (by omega)

include hq hR hsupp hQ in
theorem Iv_zero
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    Iv A (fun _ => 0) = 0 := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  let y0 : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) := fun _ => 0
  have hb := chain_zero hq hR A hsupp hQ y0 (by simp [y0]) (by simp [y0])
    (4 * (R * q) + 4 * q + 1) (by omega)
  have hv : ((sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) 0).val =
      10 * (R * q) + 12 * q := by
    rw [sitex_val hq y0 (by omega)]; omega
  have e : ∀ w ∈ stepBlockOf (sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) 1 2,
      xi A w = Iv A (fun _ => 0) := by
    intro w hw
    have hwb := ((AdalyFormal.Balaban.QjComposite.mem_stepBlockOf).mp hw) 0
    rw [hv] at hwb
    rw [xi_right hq A hsupp hQ w (by omega)]
    exact Iv_const hq hR A hsupp hQ hcurl w
  have hfit : ∀ ν : Fin 3, ((sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) ν).val
      + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; rw [hv]; omega
    · rw [sitex_coord _ _ hν]
      have h8 := dsizeT (R := R) hq hν
      show ((0 : Fin _) : ℕ) + 1 * 2 ≤ _
      simp only [Fin.val_zero]
      omega
  rw [Finset.sum_congr rfl e, Finset.sum_const,
    AdalyFormal.Balaban.QjComposite.card_stepBlockOf _ 1 2 one_pos hfit] at hb
  have h8 : (8 : ℝ) • Iv A (fun _ => 0) = 0 := by
    rw [show (8 : ℝ) = ((2 ^ 3 : ℕ) : ℝ) by norm_num, Nat.cast_smul_eq_nsmul]
    exact hb
  rcases smul_eq_zero.mp h8 with h | h
  · norm_num at h
  · exact h

include hq hR hsupp hQ in
theorem xi_mem_NQp
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    (WithLp.toLp 2 (xi A) : SiteL2 (scaleUp 2 1 (dilLu q R))) ∈
      NQp (geomOf 2 1 (dilTower q R)) flatCfg := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  have hzero : ∀ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
      ¬ ((dilTower q R).Om 1 x) → xi A x = 0 := by
    intro x hx
    have hx' : ¬ (2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q) := hx
    by_cases h : (x 0).val < 2 * (R * q) + 4 * q
    · exact xi_left hq A hsupp hQ x h
    · rw [xi_right hq A hsupp hQ x (by omega)]
      show Iv A x = 0
      rw [Iv_const hq hR A hsupp hQ hcurl x, Iv_zero hq hR A hsupp hQ hcurl]
  refine ⟨fun x hx => ?_, fun j hj y hy => ?_⟩
  · show xi A x = 0
    refine hzero x (fun h1 => hx ?_)
    have h1' : 2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q := h1
    show 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q
    omega
  · have hj1 : j = 0 ∨ j = 1 := by
      have : j ≤ 1 := hj
      omega
    rcases hj1 with rfl | rfl
    · rw [Qlev_apply, AdalyFormal.Balaban.QjComposite.Qcomposite_zero]
      show xi A y = 0
      exact hzero y hy.2.2
    · rw [Qlev_apply, Qcomposite_one', bgTower_zero']
      show stepAverage (2 ^ 0) (trivialU _) 2 (xi A) y = 0
      rw [AdalyFormal.Balaban.QjComposite.stepAverage_trivialU, pow_zero]
      obtain ⟨hdiv, hy1, -⟩ := hy
      have hy1' : 2 * (R * q) + 4 * q ≤ (y 0).val ∧ (y 0).val < 10 * (R * q) + 12 * q := hy1
      have hd0 : 2 ∣ (y 0).val := by simpa using hdiv 0
      have hd1 : 2 ∣ (y 1).val := by simpa using hdiv 1
      have hd2 : 2 ∣ (y 2).val := by simpa using hdiv 2
      obtain ⟨m, hm⟩ : ∃ m, (y 0).val = 2 * (R * q) + 4 * q - 2 + 2 * m := by
        obtain ⟨t, ht⟩ := hd0
        refine ⟨t - (R * q) - 2 * q + 1, ?_⟩
        omega
      have hc := chain_zero hq hR A hsupp hQ y hd1 hd2 m (by omega)
      rw [← hm, sitex_self] at hc
      rw [hc, smul_zero]

include hq hR hsupp hQ in
theorem A_eq_grad
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    A = gradL2 flatCfg (WithLp.toLp 2 (xi A)) := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  refine PiLp.ext (fun e => ?_)
  obtain ⟨z, μ⟩ := e
  show A (z, μ) = gradValueCovariant flatCfg (xi A) (z, μ)
  simp only [gradValueCovariant, flatCfg, RMap_one, LinearMap.id_apply]
  have hz := x0_lt hq z
  by_cases hμ : μ = 0
  · subst hμ
    by_cases hz1 : (z 0).val + 1 < 12 * (R * q) + 16 * q
    · rw [xi_shift0 hq A z hz1]; abel
    · have hzl : (z 0).val + 1 = scaleUp 2 1 (dilLu q R) 0 + 1 := by omega
      have h0 : ((periodicLatticeShift z 0) 0).val = 0 := shift0_val_last z hzl
      have e1 : xi A (periodicLatticeShift z 0) = 0 := xi_left hq A hsupp hQ _ (by rw [h0]; omega)
      have e2 : xi A z = 0 := by
        rw [xi_right hq A hsupp hQ z (by omega)]
        show Iv A z = 0
        rw [Iv_const hq hR A hsupp hQ hcurl z, Iv_zero hq hR A hsupp hQ hcurl]
      have e3 : A (z, 0) = 0 := by
        refine A_zero_off A hsupp hQ ?_ ?_
        · show z ∉ _
          rw [mem_Om1]; omega
        · show periodicLatticeShift z 0 ∉ _
          rw [mem_Om1, h0]; omega
      rw [e1, e2, e3, sub_zero]
  · rw [xi_shiftT hq hR A hsupp hQ hcurl z hμ]
    have hv0 : ((sitex z 0) 0).val = 0 := sitex_val hq z (by omega)
    have e3 : A (sitex z 0, μ) = 0 := by
      refine A_zero_off A hsupp hQ ?_ ?_
      · show sitex z 0 ∉ _
        rw [mem_Om1, hv0]; omega
      · show periodicLatticeShift (sitex z 0) μ ∉ _
        rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv0]; omega
    rw [e3]; abel

include hq hR hsupp hQ in
/-- **The flat kernel of the dilated tower is trivial.** -/
theorem dil_flat_kernel
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (hT : Tfull (geomOf 2 1 (dilTower q R)) flatCfg A = 0) : A = 0 := by
  have hg := A_eq_grad hq hR A hsupp hQ hcurl
  have hmem := xi_mem_NQp hq hR A hsupp hQ hcurl
  rw [hg] at hT ⊢
  exact final_step' _ _ hmem hT

end Kernel

end FlatKernel

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## K. Assembly: the soft premise `InteriorSoft` of round 1 holds -/
section FlatCarrier

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply)

/-- The flat localized carrier form is a sum of three squares (frozen `NsPtD1.flat_ginv_form`,
outside the `DrEquiv` closure, restated for the pinned localized assembly). -/
theorem flat_ginv_form_in (P : IngrBParams) (hU : P.U = flatCfg) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selIn selIn P).Ginv x⟫ =
      ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2
      + ‖Tfull P.G P.U (iE P.G x)‖ ^ 2
      + ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
  rw [BaseDataS.inner_Ginv]
  have hD : ⟪x, (dataS selIn selIn P).Dpi x⟫ =
      ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2 := by
    have : ⟪x, (dataS selIn selIn P).Dpi x⟫ = ⟪iE P.G x, DpiFull P.G P.U P.a (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (DpiFull P.G P.U P.a (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, hU]
    exact AdalyFormal.StatementLaneG.inner_DpiFull_flat P.G P.a (iE P.G x)
  have hM : ⟪x, (dataS selIn selIn P).Mass x⟫ =
      ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
    have : ⟪x, (dataS selIn selIn P).Mass x⟫ = ⟪iE P.G x, MassFull P.G P.a P.sector (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (MassFull P.G P.a P.sector (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, inner_MassFull]
    rfl
  rw [hD, hM]
  rfl

/-- The flat localized carrier of the dilated tower is positive definite. -/
theorem dil_flat_pos {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (hx : x ≠ 0) :
    0 < ⟪x, (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv x⟫ := by
  set P := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R) with hP
  have hform := flat_ginv_form_in P rfl x
  have t1 := sq_nonneg ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖
  have t2 := sq_nonneg ‖Tfull P.G P.U (iE P.G x)‖
  have hell : (0 : ℝ) < P.ell := by show (0 : ℝ) < (2 : ℕ); norm_num
  have t3 : 0 ≤ ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 :=
    Finset.sum_nonneg (fun p _ => by
      have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
      positivity)
  rcases (add_nonneg (add_nonneg t1 t2) t3).lt_or_eq with h | h
  · rw [hform]; exact h
  · exfalso
    apply hx
    have h1 : ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2 = 0 := by
      linarith
    have h2 : ‖Tfull P.G P.U (iE P.G x)‖ ^ 2 = 0 := by linarith
    have h3 : ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by
      linarith
    have hm : plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x)) = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
    have hT : Tfull P.G P.U (iE P.G x) = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
    have hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg (iE P.G x) = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by
        have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
        positivity)).mp h3
      refine PiLp.ext (fun p => ?_)
      have h1 := hz p (Finset.mem_univ p)
      have hp : 0 < P.a * (P.ell : ℝ) ^ (p.1 : ℕ) := by
        have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
        positivity
      have h2 : ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hp.ne'
        · exact h
      have := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
      exact this
    have hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → (iE P.G x) b = 0 :=
      fun b hb => x.2 b hb
    have hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0),
        curlValueCovariant flatCfg (WithLp.ofLp (iE P.G x)) p = 0 := by
      intro p hp
      have h := congrArg (fun v : AdalyFormal.Balaban.CovariantHjMinimizer.PlaqFnL2 P.Lf => WithLp.ofLp v p) hm
      simp only [plaqMask_apply, PiLp.zero_apply] at h
      rw [if_pos (show p ∈ plaqIn P.G.Om0 from hp)] at h
      have e : curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x) =
          WithLp.toLp 2 (curlValueCovariant flatCfg (WithLp.ofLp (iE P.G x))) :=
        curlCovariantCLM_L2_toLp _ _
      rw [e] at h
      exact h
    have hA := dil_flat_kernel hq hR (iE P.G x) hsupp hQ hcurl hT
    exact Subtype.ext hA

theorem dil_flat_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv := by
  set M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
    (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv with hMdef
  have hinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have := dil_flat_pos hq hR x hne
    rw [hx, inner_zero_right] at this
    exact lt_irrefl _ this
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →ₗ[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))))).mp hinj⟩

end FlatCarrier

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

section Final

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU)
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace extP extA extD InteriorRegularity InteriorSoft)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

/-- the curved dilated family. -/
noncomputable abbrev dilV (q R : ℕ) : ℝ → Cfg (scaleUp 2 1 (dilLu q R)) := fun ε => dilU q R ε 1

theorem dataFam_dil_zero (sD sJ : PlaqSel) (q R : ℕ) :
    dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0 =
      dataS sD sJ (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R)) := by
  show dataS sD sJ (gparams 2 1 (dilLu q R) _ (dilTower q R) (dilU q R 0 1) 1 (dilLam q R)) = _
  rw [dilU_zero]

theorem dil_B0_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Ginv := by
  rw [dataFam_dil_zero]
  exact dil_flat_unit hq hR

theorem dil_B0_psd {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    AdalyFormal.D1Literal.PSD
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Ginv := by
  rw [dataFam_dil_zero]
  intro v
  by_cases hv : v = 0
  · rw [hv, inner_zero_left]
  · exact (dil_flat_pos hq hR v hv).le

theorem dil_Qs0_inj {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    Function.Injective
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Qs := by
  rw [dataFam_dil_zero]
  exact dil_Qs_inj hq hR16 hS

theorem dil_N0_unit {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    IsUnit (((dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Q.comp
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).G).comp
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Qs) := by
  set D0 := dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0
  have hL : D0.Laws := dataS_laws selIn selIn _
  obtain ⟨m, hm, hmc⟩ := AdalyFormal.D1Literal.psd_coercive D0.Ginv (D0.Ginv_symm hL)
    (dil_B0_psd hq (by omega)) (dil_B0_unit hq (by omega))
  exact isUnit_Q_inv_Qs (D0.Ginv_symm hL) hm hmc D0.Q_adj (dil_Qs0_inj hq hR16 hS)

theorem extA_eq_dataFam (q R : ℕ) (ε : ℝ) :
    extA q R ε 1 = (dataFam selAll selAll (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Ginv := rfl

theorem extD_eq_dataFam (q R : ℕ) (ε : ℝ) :
    extD q R ε 1 = (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Delta2 (dataS_laws selIn selIn _) := rfl

theorem C2_dataFam (q R : ℕ) (ε : ℝ) (A : TwistSpace q R) :
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) ε).C2 A =
      C2fullOf (geomOf 2 1 (dilTower q R)) (dilV q R ε)
        (Wop (geomOf 2 1 (dilTower q R)) (dilV q R ε) 1 (iE (geomOf 2 1 (dilTower q R)) A)) := rfl

theorem J_dataFam (q R : ℕ) (ε : ℝ) :
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) ε).J =
      pE (geomOf 2 1 (dilTower q R)) (WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1
        (plaqIn (geomOf 2 1 (dilTower q R)).Om0) (dilV q R ε) b))) := rfl

theorem Q_dataFam (q R : ℕ) (ε : ℝ) :
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) ε).Q =
      (QfullOf (geomOf 2 1 (dilTower q R)) (dilV q R ε)).comp (iE (geomOf 2 1 (dilTower q R))) := rfl

theorem Qs_dataFam (q R : ℕ) (ε : ℝ) :
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) ε).Qs =
      ContinuousLinearMap.adjoint
        ((QfullOf (geomOf 2 1 (dilTower q R)) (dilV q R ε)).comp (iE (geomOf 2 1 (dilTower q R)))) := rfl

section DilCont
variable {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))

omit hq hS in
theorem dil_reg0 (q R : ℕ) :
    RegBg ((geomOf 2 1 (dilTower q R)).ell ^ 0) (geomOf 2 1 (dilTower q R)).ell (dilV q R 0) := by
  rw [show dilV q R 0 = fun _ => 1 from dilU_zero q R]; exact RegBg_flat _ _

omit hq hS in
theorem dil_LP0 (hq : 0 < q) : IsUnit (AdalyFormal.M1Site.LP (geomOf 2 1 (dilTower q R)) (dilV q R 0) 1) :=
  dil_LP_unit q R hq _

omit hq hS in
theorem dil_Gam0 (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    IsUnit (Gam (geomOf 2 1 (dilTower q R)) (dilV q R 0) 1) := by
  rw [show dilV q R 0 = fun _ => 1 from dilU_zero q R]; exact dil_Gam_unit hS

include hq hS in
theorem dil_W_cont : ContinuousAt (fun ε => Wop (geomOf 2 1 (dilTower q R)) (dilV q R ε) 1) 0 :=
  continuousAt_Wop (dilU_contFam q R) (geomOf 2 1 (dilTower q R)) rfl 1 (dil_LP0 hq) (dil_wq_pos q R)
    (dil_Gam0 hS)

include hq hS in
theorem dil_T_cont : ContinuousAt (fun ε => Tfull (geomOf 2 1 (dilTower q R)) (dilV q R ε)) 0 :=
  continuousAt_Tfull (dilU_contFam q R) (geomOf 2 1 (dilTower q R)) rfl 1 (dil_LP0 hq) (dil_wq_pos q R)
    (dil_Gam0 hS)

omit hq hS in
theorem dil_Q_cont (q R : ℕ) : ContinuousAt (fun ε => QfullOf (geomOf 2 1 (dilTower q R)) (dilV q R ε)) 0 :=
  continuousAt_QfullOf (dilV q R) (dilU_smooth q R) (geomOf 2 1 (dilTower q R)) rfl (dil_reg0 q R)

include hq hS in
theorem dil_carrier_cont (sD sJ : PlaqSel) :
    ContinuousAt (fun ε => (dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Ginv) 0 :=
  continuousAt_Ginv_dataS sD sJ (by norm_num) (dilTower q R) (dilV q R) 1 (dilLam q R)
    (dilU_contFam q R) (dil_W_cont hq hS) (dil_T_cont hq hS) (dil_Q_cont q R)

include hq hS in
theorem dil_tendsto_extA :
    Tendsto (fun ε : ℝ => extA q R ε 1) (𝓝[>] 0) (𝓝 (extA q R 0 1)) := by
  simp only [extA_eq_dataFam]
  exact (dil_carrier_cont hq hS selAll selAll).tendsto.mono_left nhdsWithin_le_nhds

include hq hS in
theorem dil_tendsto_W :
    Tendsto (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (dilU q R ε 1) 1) (𝓝[>] 0)
      (𝓝 (Wop (geomOf 2 1 (dilTower q R)) (dilU q R 0 1) 1)) :=
  (dil_W_cont hq hS).tendsto.mono_left nhdsWithin_le_nhds

include hq hS in
theorem dil_H_cont (hR : 16 ≤ R) :
    ContinuousAt (fun ε => (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).H) 0 := by
  have hQc : ContinuousAt (fun ε => (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Q) 0 := by
    simp only [Q_dataFam]
    exact continuousAt_clm_comp (dil_Q_cont q R) continuousAt_const
  have hQsc : ContinuousAt (fun ε => (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Qs) 0 := by
    simp only [Qs_dataFam]
    exact cont_adjoint.continuousAt.comp (continuousAt_clm_comp (dil_Q_cont q R) continuousAt_const)
  exact continuousAt_H _ (dil_carrier_cont hq hS selIn selIn) hQc hQsc (dil_B0_unit hq (by omega))
    (dil_N0_unit hq hR hS)

include hq hS in
theorem dil_C2_tendsto (A : TwistSpace q R) :
    Tendsto (fun ε => (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).C2 A) (𝓝 0) (𝓝 ((dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (dilV q R) 1 (dilLam q R) 0).C2 A)) := by
  simp only [C2_dataFam]
  exact tendsto_C2fullOf (dilV q R) (dilU_smooth q R) (geomOf 2 1 (dilTower q R)) rfl (dil_reg0 q R)
    (tendsto_clm_apply₂ (dil_W_cont hq hS) tendsto_const_nhds)

omit hq hS in
theorem dil_J_tendsto (q R : ℕ) : ∃ J' : TwistSpace q R,
    Tendsto (fun ε => ε⁻¹ • (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).J) (𝓝[≠] 0) (𝓝 J') := by
  obtain ⟨J', hJ'⟩ := exists_source_derivative (dilV q R) (dilU_smooth q R) (dilU_zero q R)
    (plaqIn (geomOf 2 1 (dilTower q R)).Om0)
  refine ⟨pE (geomOf 2 1 (dilTower q R)) J', ?_⟩
  simp only [J_dataFam, ← map_smul]
  exact ((pE (geomOf 2 1 (dilTower q R))).continuous.tendsto _).comp hJ'

include hq hS in
theorem dil_exists_D1 (hR : 16 ≤ R) : ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R,
    Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε 1) (𝓝[>] 0) (𝓝 D₁) := by
  obtain ⟨J', hJ⟩ := dil_J_tendsto q R
  have hH := dil_H_cont hq hS hR
  have hC2 := dil_C2_tendsto hq hS
  obtain ⟨D₁, hD₁⟩ := tendsto_Delta2_div
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R))
    (fun ε => dataS_laws selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (dilV q R ε) 1 (dilLam q R))) hH hC2 J' hJ
  refine ⟨D₁, ?_⟩
  simp only [extD_eq_dataFam]
  exact hD₁.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))

include hq hS in
/-- **The first-order coefficient, explicitly.**  Any limit `D₁` of `extD(ε)/ε` has the quadratic form
`A ↦ 2⟪H₀ C²₀(W₀ A), J'⟫`: `H₀`, `C²₀`, `W₀` are the flat (vacuum) constrained inverse, second
jet and dressing of the localized data, and `J'` the curvature derivative of the source. -/
theorem dil_D1_form (hR : 16 ≤ R) (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R)
    (hD₁ : Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε 1) (𝓝[>] 0) (𝓝 D₁)) (J' : TwistSpace q R)
    (hJ : Tendsto (fun ε => ε⁻¹ • (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).J) (𝓝[≠] 0) (𝓝 J')) (A : TwistSpace q R) :
    ⟪A, D₁ A⟫ = 2 * ⟪(dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (fun _ => 1) 1 (dilLam q R))).H
      (C2fullOf (geomOf 2 1 (dilTower q R)) (fun _ => 1)
        (Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1 (iE (geomOf 2 1 (dilTower q R)) A))), J'⟫ := by
  have hD₁' : Tendsto (fun ε => ε⁻¹ • (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Delta2 (dataS_laws selIn selIn
        (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (dilV q R ε) 1 (dilLam q R))))
      (𝓝[>] 0) (𝓝 D₁) := by
    simp only [← extD_eq_dataFam]
    exact hD₁
  have h := limit_Delta2_div_form
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R))
    (fun ε => dataS_laws selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (dilV q R ε) 1 (dilLam q R)))
    (dil_H_cont hq hS hR) (dil_C2_tendsto hq hS) J' hJ D₁ hD₁' A
  rw [h, dataFam_dil_zero]
  rfl

end DilCont

/-- **Soft regularity of the curved dilated family at zero curvature**, for every scale and every
even radius `≥ 18`, given admissibility of the tower: the carrier and `W` are continuous at `ε = 0`
and `Δ⁽²⁾(ε)/ε` converges. -/
theorem interiorRegularity_of_admissible {q R : ℕ} (hq : 0 < q) (hR : 18 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R, InteriorRegularity q R D₁ := by
  obtain ⟨D₁, hD₁⟩ := dil_exists_D1 hq hS (by omega)
  exact ⟨D₁, dil_tendsto_extA hq hS, dil_tendsto_W hq hS, hD₁⟩

/-- `InteriorSoft` (round 1), given admissibility of the dilated towers. -/
theorem interiorSoft_of_admissible
    (hS : ∀ q R : ℕ, 0 < q → 2 ∣ R → Admissible 2 (2 * q) R 1 (dilTower q R)) : InteriorSoft :=
  fun q R hq hR hR18 => interiorRegularity_of_admissible hq hR18 (hS q R hq hR)

end Final

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## L. The soft premise closed; the reductions of this round -/
section Close

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU dil_admissible)
open AdalyFormal.Round5.Guarded.IVTR1 (twistU twistP twistA twistD)
open AdalyFormal.Round8.Guarded.SignFree (CofinalTwistSeparation goalNeg2_of_cofinalTwistSeparation
  not_cofinalTwistSeparation_of_goalPos1)
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- **Round 1's soft premise `InteriorSoft` holds**, for every scale and every even radius `≥ 18`. -/
theorem interiorSoft_proved : InteriorSoft :=
  interiorSoft_of_admissible (fun _ _ hq hR => dil_admissible hq hR)

/-- **Main reduction of this round**: the zero-curvature crossing data of the left twist refute
the guarded all-plaquette reading; no soft premise remains. -/
theorem goalNeg2_of_vacuumLeftSpectral (hc : VacuumLeftSpectral) : GoalNeg2 :=
  goalNeg2_of_interiorSoft_vacuumLeftSpectral interiorSoft_proved hc

/-- The positive reading forbids it. -/
theorem not_vacuumLeftSpectral_of_goalPos1 (h : GoalPos1) : ¬ VacuumLeftSpectral :=
  fun hc => goalNeg2_of_vacuumLeftSpectral hc (goalPos2_iff_goalPos1.mpr h)

/-- **Zero-curvature regularity of the round-8 twist family** (round 1's
`ZeroCurvatureRegularity`), for every scale and every even radius `≥ 18`. -/
theorem zeroCurvatureRegularity_proved {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R, ZeroCurvatureRegularity q R D₁ := by
  obtain ⟨D₁, hA, hW, hD⟩ := interiorSoft_proved q R hq hR hR18
  have hV0 : AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) 0 = 1 :=
    AdalyFormal.D1Literal.Uth_zero _
  refine ⟨D₁, fun t => ?_, ?_⟩
  · exact extA_joint_tendsto hq hR (by nlinarith) (AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0))
      (AdalyFormal.D1Literal.contFam_Uth _) (by rw [hV0]; exact hA) (by rw [hV0]; exact hW) t
  · show Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε (AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) 0))
      (𝓝[>] 0) (𝓝 D₁)
    rw [hV0]
    exact hD

/-- The zero-curvature, spectral part of round 8's premise: for cofinal dyadic scales and,
for each, cofinal even radii `≥ 18`, the vacuum crossing data of the round-8 twist for the
first-order coefficient of its correction.  NOT proved here. -/
def CofinalTwistVacuumCrossing : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ D₁ : TwistSpace (2 ^ j) R →L[ℝ] TwistSpace (2 ^ j) R,
      Tendsto (fun ε : ℝ => ε⁻¹ • twistD (2 ^ j) R ε 1 0) (𝓝[>] 0) (𝓝 D₁) →
        VacuumCrossing (2 ^ j) R D₁

/-- **`X → CofinalTwistSeparation`** (round 8's target), with `X` purely spectral at zero
curvature. -/
theorem cofinalTwistSeparation_of_twistVacuumCrossing (h : CofinalTwistVacuumCrossing) :
    CofinalTwistSeparation := by
  apply cofinalTwistSeparation_of_cofinalVacuum
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  obtain ⟨D₁, hreg⟩ := zeroCurvatureRegularity_proved (q := 2 ^ j) (by positivity) hR hR18
  exact ⟨R, hRR, hR, hR18, D₁, hreg, hc D₁ hreg.2⟩

theorem goalNeg2_of_twistVacuumCrossing (h : CofinalTwistVacuumCrossing) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_twistVacuumCrossing h)

theorem not_twistVacuumCrossing_of_goalPos1 (h : GoalPos1) : ¬ CofinalTwistVacuumCrossing :=
  fun h' => not_cofinalTwistSeparation_of_goalPos1 h (cofinalTwistSeparation_of_twistVacuumCrossing h')

/-! ### The remaining premises with the first-order coefficient written out

`vacCoupling q R J' v = 2⟪H₀ C²₀(W₀ v), J'⟫`: the flat (vacuum) constrained inverse `H₀`, the flat
second jet `C²₀` of the flat dressing `W₀ v`, and the curvature derivative `J'` of the localized
source (`IsSourceDerivative`, which exists: `dil_J_tendsto`).  By `dil_D1_form` this is the
quadratic form of the first-order coefficient `D₁`. -/

/-- The flat localized data of the dilated tower. -/
noncomputable abbrev flatData (q R : ℕ) :=
  dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R))

/-- The explicit vacuum coupling form `2⟪H₀ C²₀(W₀ v), J'⟫`. -/
noncomputable def vacCoupling (q R : ℕ) (J' : TwistSpace q R) (v : TwistSpace q R) : ℝ :=
  2 * ⟪(flatData q R).H (C2fullOf (geomOf 2 1 (dilTower q R)) (fun _ => 1)
    (Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1 (iE (geomOf 2 1 (dilTower q R)) v))), J'⟫

/-- `J'` is the curvature derivative of the localized source of the curved dilated family. -/
def IsSourceDerivative (q R : ℕ) (J' : TwistSpace q R) : Prop :=
  Tendsto (fun ε => ε⁻¹ • (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
    (dilLam q R) ε).J) (𝓝[≠] 0) (𝓝 J')

/-- Crossing data of a vacuum carrier path, with the explicit coupling form.  NOT proved here. -/
def CouplingCrossing (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (J' : TwistSpace q R) :
    Prop :=
  ∃ (t₀ : ℝ) (X' : TwistSpace q R →L[ℝ] TwistSpace q R),
    HasDerivAt (fun t => extA q R 0 (V t)) X' t₀ ∧
    (∃ v, extA q R 0 (V t₀) v = 0 ∧ v ≠ 0) ∧
    (∀ v, extA q R 0 (V t₀) v = 0 → v ≠ 0 → ⟪v, X' v⟫ < 0) ∧
    ((∀ v, extA q R 0 (V t₀) v = 0 → v ≠ 0 → vacCoupling q R J' v < 0) ∨
      (∀ v, extA q R 0 (V t₀) v = 0 → v ≠ 0 → 0 < vacCoupling q R J' v))

/-- The left-twist premise with the explicit coupling form.  NOT proved here. -/
def VacuumLeftCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ J' : TwistSpace (2 ^ j) R, IsSourceDerivative (2 ^ j) R J' →
      CouplingCrossing (2 ^ j) R (leftTwist (2 ^ j) R) J'

theorem pathCrossing_of_couplingCrossing {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (J' : TwistSpace q R) (hJ : IsSourceDerivative q R J')
    (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R)
    (hD₁ : Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε 1) (𝓝[>] 0) (𝓝 D₁))
    (h : CouplingCrossing q R V J') : PathCrossing q R V D₁ := by
  obtain ⟨t₀, X', hder, hne, hslope, hsign⟩ := h
  have hform : ∀ v, ⟪v, D₁ v⟫ = vacCoupling q R J' v := fun v =>
    dil_D1_form hq (dil_admissible hq hR) hR16 D₁ hD₁ J' hJ v
  refine ⟨t₀, X', hder, hne, hslope, ?_⟩
  rcases hsign with h | h
  · exact Or.inl (fun v hv hv0 => by rw [hform]; exact h v hv hv0)
  · exact Or.inr (fun v hv hv0 => by rw [hform]; exact h v hv hv0)

theorem vacuumLeftSpectral_of_coupling (h : VacuumLeftCoupling) : VacuumLeftSpectral := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun D₁ hD₁ => ?_⟩
  obtain ⟨J', hJ'⟩ := dil_J_tendsto (2 ^ j) R
  exact pathCrossing_of_couplingCrossing (by positivity) hR (by omega) _ J' hJ' D₁ hD₁ (hc J' hJ')

/-- **The reduction with every ingredient explicit**: the zero-curvature left-twist crossing
data, with the explicit coupling form, refute the guarded all-plaquette reading. -/
theorem goalNeg2_of_vacuumLeftCoupling (h : VacuumLeftCoupling) : GoalNeg2 :=
  goalNeg2_of_vacuumLeftSpectral (vacuumLeftSpectral_of_coupling h)

/-- The round-8 twist premise with the explicit coupling form.  NOT proved here. -/
def CofinalTwistVacuumCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ J' : TwistSpace (2 ^ j) R, IsSourceDerivative (2 ^ j) R J' →
      CouplingCrossing (2 ^ j) R (AdalyFormal.D1Literal.Uth ((dilTower (2 ^ j) R).Om 0)) J'

/-- **`X → CofinalTwistSeparation`** with `X` the explicit zero-curvature coupling data of the
round-8 twist. -/
theorem cofinalTwistSeparation_of_twistVacuumCoupling (h : CofinalTwistVacuumCoupling) :
    CofinalTwistSeparation := by
  apply cofinalTwistSeparation_of_twistVacuumCrossing
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun D₁ hD₁ => ?_⟩
  obtain ⟨J', hJ'⟩ := dil_J_tendsto (2 ^ j) R
  have hV0 : AdalyFormal.D1Literal.Uth ((dilTower (2 ^ j) R).Om 0) 0 = 1 :=
    AdalyFormal.D1Literal.Uth_zero _
  have hD₁' : Tendsto (fun ε : ℝ => ε⁻¹ • extD (2 ^ j) R ε 1) (𝓝[>] 0) (𝓝 D₁) := by
    have e : (fun ε : ℝ => ε⁻¹ • twistD (2 ^ j) R ε 1 0) =
        fun ε : ℝ => ε⁻¹ • extD (2 ^ j) R ε (AdalyFormal.D1Literal.Uth ((dilTower (2 ^ j) R).Om 0) 0) :=
      rfl
    rw [e, hV0] at hD₁
    exact hD₁
  exact pathCrossing_of_couplingCrossing (by positivity) hR (by omega) _ J' hJ' D₁ hD₁' (hc J' hJ')

theorem goalNeg2_of_twistVacuumCoupling (h : CofinalTwistVacuumCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_twistVacuumCoupling h)

end Close

end AdalyFormal.Round9.Guarded.AnalyticR2


#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_of_inner
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_clm_of_apply
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_clm_of_inner
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.inner_suTwo
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_suTwo_of_coe
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuous_suTwo_of_coe
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_piLp_suTwo
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuous_piLp_suTwo
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuous_coe_suTwo
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_coarsePathHolonomy
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_RMap_coe
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_gradL2
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_adjoint
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_gradAdj
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_lapFull
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Qcomposite_one'
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.bgTower_zero'
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_Qlev
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_Qpa
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_DelpA
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_LP
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cont_QpP
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Gam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Rproj_formula
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_inverse_comp
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_clm_comp
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_LinvP
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_Xop
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_Gam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_Rproj
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_Tfull
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_Wop
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.ajSeq_pos
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Qpa_nonneg
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.delpA_inner_ge
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.covConst_norm
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.delpA_unit
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.wq_pos
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_clm_of_apply'
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SmoothAt0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_V0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_V1
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_prod
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_loopVar_fam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_sbg_fam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_rProd_fam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_su2Exp_sBlock_fam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_su2Exp_neg_sBlock_fam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_rawStep_fam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.contDiffAt_qStep_fam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_fderiv_qStep
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_fderiv2_qStep
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_clm_apply₂
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.suCoordL
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.QfullOf_apply
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.C2fullOf_apply
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.QlinB_one_coe
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.C2rawB_zero'
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.C2rawB_one_coe
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_QlinB1_coe
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_QfullOf
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_C2fullOf
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Ginv_dataS_eq
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dataFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Ginv_dataFam_eq
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_Ginv_dataS
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_H
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.inner_polarization
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_Delta2_div_form
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_Delta2_div
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.limit_Delta2_div_form
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.SG_holonomyElem
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cd_imHolonomy
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cd_piProj
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cd_FnuMuLoc
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cd_DstarDir
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cd_JfieldLoc
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cd_JSU2Loc
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.source_slope
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.exists_source_derivative
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.contDiff_Xm
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.contDiffAt_Ug
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dilU_link_contDiff
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dilU_smooth
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dilU_contFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dilU_zero
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_G_k
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_G_ell
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_out_site
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_LP_unit
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_wq_pos
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.bgTower_one
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_Gam_unit
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.delW_zero
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_Qs_inj
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.siteMask_eq_self_of_supp'
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.lapDir_eq_mask_lap'
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.final_step'
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dsize0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dsizeT
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.x0_lt
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.xT_lt
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.mem_Om0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.mem_Om1
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.not_mem_Om2
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.shift_coord_ne
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.shift_self_coord
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.shift0_val_lt
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.shift0_val_last
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.OmGe1_mem
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.A_zero_off
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.sitex
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.sitex_val
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.sitex_coord
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.sitex_self
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.sitex_sitex
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.shift_sitex0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.shift_sitex
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.sitex_of_shift0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.xi
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.xi_shift0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.trans_step
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.xi_shiftT
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.xi_left
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.xi_right
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Iv
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Iv_shiftT
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.update_shift_succ
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Iv_update
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Iv_update0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Iv_const
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.coarseShift_sitex
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.row_step
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.chain_zero
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Iv_zero
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.xi_mem_NQp
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.A_eq_grad
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_kernel
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.flat_ginv_form_in
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_pos
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_unit
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dilV
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dataFam_dil_zero
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_B0_unit
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_B0_psd
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_Qs0_inj
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_N0_unit
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.extA_eq_dataFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.extD_eq_dataFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.C2_dataFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.J_dataFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Q_dataFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.Qs_dataFam
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_reg0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_LP0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_Gam0
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_W_cont
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_T_cont
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_Q_cont
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_carrier_cont
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_tendsto_extA
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_tendsto_W
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_H_cont
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_C2_tendsto
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_J_tendsto
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_exists_D1
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_D1_form
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.interiorRegularity_of_admissible
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.interiorSoft_of_admissible
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.interiorSoft_proved
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftSpectral
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.not_vacuumLeftSpectral_of_goalPos1
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.zeroCurvatureRegularity_proved
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.CofinalTwistVacuumCrossing
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCrossing
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_twistVacuumCrossing
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.not_twistVacuumCrossing_of_goalPos1
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.flatData
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.vacCoupling
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.IsSourceDerivative
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.CouplingCrossing
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.VacuumLeftCoupling
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.pathCrossing_of_couplingCrossing
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.vacuumLeftSpectral_of_coupling
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftCoupling
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.CofinalTwistVacuumCoupling
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCoupling
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_twistVacuumCoupling

/-!
Round 9.2, qualitative route, second part: the soft premise is a theorem for every profile.

The analytic route's appendices (`AnalyticR1`, `AnalyticR2`, copied verbatim above from
`AHP/round9/analytic-r1/Appendix.lean` and `AHP/round9/analytic-r2/Appendix.lean`) contain a
generic theory of smooth curvature families based at the trivial background
(`AnalyticR2.dataFam`, `continuousAt_Ginv_dataS`, `continuousAt_H`, `tendsto_Delta2_div`,
`exists_source_derivative`), and the unit `AnalyticR2.dil_flat_unit` of the flat localized
carrier at every scale and radius.  Here that theory is instantiated at the interior family
`ε ↦ maskedU (ε f) 1` of an ARBITRARY profile `f`, with the two-sided limit.  This proves this
round's soft premise `QualitativeR2.InteriorSoft q R f (corrDeriv q R f)` for every `f`, every
`q > 0` and every even `R ≥ 16`, where `corrDeriv q R f` is the actual derivative at `0` of the
localized correction.  The canonical vacuum crossing of the twist holds at every instance.

The premise that remains is one statement per instance: the first-order coefficient
`corrDeriv` is definite, of either sign, on the kernel of the vacuum carrier of the round-8
twist at its canonical crossing (`CofinalCanonicalCoupling`; free-profile form
`CofinalAnyProfileCoupling`; explicit form `CofinalExplicitCoupling` with the analytic route's
coupling `2⟪H₀ C²₀(W₀ u), J'⟫`; complex-line form `CofinalExplicitU1`).  Nothing here proves
a pinned goal.
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.Round9.Guarded.QualitativeR2Joint

open scoped RealInnerProductSpace
open Filter Topology
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
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.D1Literal (PSD)

/-! ## A. The interior family of an arbitrary profile: smooth, flat at `ε = 0` -/

section BulkFamily

open scoped Matrix.Norms.Frobenius

/-- The interior family of the profile `f` (curvature `ε f` on the bonds touching `Ω₀`,
trivial exterior), as a curvature family. -/
noncomputable abbrev bulkV (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun ε => QualitativeR2.bulkU q R f ε

theorem bulkU_link_contDiff (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R))) :
    ContDiff ℝ ⊤ (fun ε : ℝ => ((QualitativeR2.bulkU q R f ε e : SU2) : M2)) := by
  classical
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [QualitativeR2.bulkU, maskedU, if_pos he]
    exact contDiff_const
  · simp only [QualitativeR2.bulkU, maskedU, if_neg he]
    have hl : ContDiff ℝ ⊤ (fun ε : ℝ => ε * f e) := contDiff_id.mul contDiff_const
    refine contDiff_iff_contDiffAt.mpr (fun ε => ?_)
    have h := (AnalyticR2.contDiffAt_Ug (ε * f e)).comp ε hl.contDiffAt
    exact h

theorem bulkV_smooth (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    AnalyticR2.SmoothAt0 (bulkV q R f) :=
  fun e => (bulkU_link_contDiff q R f e).contDiffAt

theorem bulkV_contFam (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    AdalyFormal.D1Literal.ContFam (bulkV q R f) :=
  fun e => (bulkU_link_contDiff q R f e).continuous

end BulkFamily

theorem bulkU_zero (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    QualitativeR2.bulkU q R f 0 = fun _ => 1 := by
  classical
  funext e
  simp only [QualitativeR2.bulkU, maskedU, zero_mul, Ug_zero, ite_self]

theorem bulk_dataFam_zero (sD sJ : PlaqSel) (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    AnalyticR2.dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1 (dilLam q R) 0 =
      dataS sD sJ (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1
        (dilLam q R)) := by
  show dataS sD sJ (gparams 2 1 (dilLu q R) _ (dilTower q R) (QualitativeR2.bulkU q R f 0) 1
    (dilLam q R)) = _
  rw [bulkU_zero]

theorem bulk_dataFam_zero_eq (sD sJ : PlaqSel) (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    AnalyticR2.dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1 (dilLam q R) 0 =
      AnalyticR2.dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (AnalyticR2.dilV q R) 1
        (dilLam q R) 0 := by
  rw [bulk_dataFam_zero, AnalyticR2.dataFam_dil_zero]

theorem bulkD_eq_dataFam (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    QualitativeR2.bulkD q R f ε =
      (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1
        (dilLam q R) ε).Delta2 (dataS_laws selIn selIn _) := rfl

theorem bulkA_eq_dataFam (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    QualitativeR2.bulkA q R f ε =
      (AnalyticR2.dataFam selAll selAll (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1
        (dilLam q R) ε).Ginv := rfl

/-! ## B. Continuity at the flat interior and the first-order coefficient -/

theorem bulk_LP0 {q R : ℕ} (hq : 0 < q) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    IsUnit (AdalyFormal.M1Site.LP (geomOf 2 1 (dilTower q R)) (bulkV q R f 0) 1) :=
  AnalyticR2.dil_LP_unit q R hq _

theorem bulk_Gam0 {q R : ℕ} (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    IsUnit (AnalyticR2.Gam (geomOf 2 1 (dilTower q R)) (bulkV q R f 0) 1) := by
  rw [show bulkV q R f 0 = fun _ => 1 from bulkU_zero q R f]
  exact AnalyticR2.dil_Gam_unit hS

theorem bulk_reg0 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    RegBg ((geomOf 2 1 (dilTower q R)).ell ^ 0) (geomOf 2 1 (dilTower q R)).ell (bulkV q R f 0) := by
  rw [show bulkV q R f 0 = fun _ => 1 from bulkU_zero q R f]
  exact RegBg_flat _ _

theorem bulk_W_cont {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContinuousAt (fun ε => Wop (geomOf 2 1 (dilTower q R)) (bulkV q R f ε) 1) 0 :=
  AnalyticR2.continuousAt_Wop (bulkV_contFam q R f) (geomOf 2 1 (dilTower q R)) rfl 1
    (bulk_LP0 hq f) (AnalyticR2.dil_wq_pos q R) (bulk_Gam0 hS f)

theorem bulk_T_cont {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContinuousAt (fun ε => Tfull (geomOf 2 1 (dilTower q R)) (bulkV q R f ε)) 0 :=
  AnalyticR2.continuousAt_Tfull (bulkV_contFam q R f) (geomOf 2 1 (dilTower q R)) rfl 1
    (bulk_LP0 hq f) (AnalyticR2.dil_wq_pos q R) (bulk_Gam0 hS f)

theorem bulk_Q_cont (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContinuousAt (fun ε => QfullOf (geomOf 2 1 (dilTower q R)) (bulkV q R f ε)) 0 :=
  AnalyticR2.continuousAt_QfullOf (bulkV q R f) (bulkV_smooth q R f) (geomOf 2 1 (dilTower q R))
    rfl (bulk_reg0 q R f)

theorem bulk_carrier_cont {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (sD sJ : PlaqSel) :
    ContinuousAt (fun ε => (AnalyticR2.dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) ε).Ginv) 0 :=
  AnalyticR2.continuousAt_Ginv_dataS sD sJ (by norm_num) (dilTower q R) (bulkV q R f) 1
    (dilLam q R) (bulkV_contFam q R f) (bulk_W_cont hq hS f) (bulk_T_cont hq hS f)
    (bulk_Q_cont q R f)

theorem bulk_H_cont {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContinuousAt (fun ε => (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) ε).H) 0 := by
  have hQc : ContinuousAt (fun ε => (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2)
      (dilTower q R) (bulkV q R f) 1 (dilLam q R) ε).Q) 0 := by
    show ContinuousAt (fun ε => (QfullOf (geomOf 2 1 (dilTower q R)) (bulkV q R f ε)).comp
      (iE (geomOf 2 1 (dilTower q R)))) 0
    exact AnalyticR2.continuousAt_clm_comp (bulk_Q_cont q R f) continuousAt_const
  have hQsc : ContinuousAt (fun ε => (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2)
      (dilTower q R) (bulkV q R f) 1 (dilLam q R) ε).Qs) 0 := by
    show ContinuousAt (fun ε => ContinuousLinearMap.adjoint
      ((QfullOf (geomOf 2 1 (dilTower q R)) (bulkV q R f ε)).comp
        (iE (geomOf 2 1 (dilTower q R))))) 0
    exact AnalyticR2.cont_adjoint.continuousAt.comp
      (AnalyticR2.continuousAt_clm_comp (bulk_Q_cont q R f) continuousAt_const)
  have hB0 : IsUnit (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) 0).Ginv := by
    rw [bulk_dataFam_zero]
    exact AnalyticR2.dil_flat_unit hq (by omega)
  have hN0 : IsUnit (((AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) 0).Q.comp
      (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (bulkV q R f) 1 (dilLam q R) 0).G).comp
      (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (bulkV q R f) 1 (dilLam q R) 0).Qs) := by
    rw [bulk_dataFam_zero_eq]
    exact AnalyticR2.dil_N0_unit hq hR16 hS
  exact AnalyticR2.continuousAt_H
    (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1
      (dilLam q R))
    (bulk_carrier_cont hq hS f selIn selIn) hQc hQsc hB0 hN0

theorem bulk_C2_tendsto {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (A : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    Tendsto (fun ε => (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) ε).C2 A) (𝓝 0)
      (𝓝 ((AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (bulkV q R f) 1 (dilLam q R) 0).C2 A)) := by
  show Tendsto (fun ε => C2fullOf (geomOf 2 1 (dilTower q R)) (bulkV q R f ε)
      (Wop (geomOf 2 1 (dilTower q R)) (bulkV q R f ε) 1 (iE (geomOf 2 1 (dilTower q R)) A))) (𝓝 0)
    (𝓝 (C2fullOf (geomOf 2 1 (dilTower q R)) (bulkV q R f 0)
      (Wop (geomOf 2 1 (dilTower q R)) (bulkV q R f 0) 1 (iE (geomOf 2 1 (dilTower q R)) A))))
  exact AnalyticR2.tendsto_C2fullOf (bulkV q R f) (bulkV_smooth q R f) (geomOf 2 1 (dilTower q R))
    rfl (bulk_reg0 q R f) (AnalyticR2.tendsto_clm_apply₂ (bulk_W_cont hq hS f) tendsto_const_nhds)

/-- The localized source of the interior family has a curvature derivative (two-sided). -/
theorem bulk_J_tendsto (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ∃ J' : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      Tendsto (fun ε => ε⁻¹ • (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (bulkV q R f) 1 (dilLam q R) ε).J) (𝓝[≠] 0) (𝓝 J') := by
  obtain ⟨J', hJ'⟩ := AnalyticR2.exists_source_derivative (bulkV q R f) (bulkV_smooth q R f)
    (bulkU_zero q R f) (plaqIn (geomOf 2 1 (dilTower q R)).Om0)
  refine ⟨pE (geomOf 2 1 (dilTower q R)) J', ?_⟩
  show Tendsto (fun ε : ℝ => ε⁻¹ • pE (geomOf 2 1 (dilTower q R))
      (WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1
        (plaqIn (geomOf 2 1 (dilTower q R)).Om0) (bulkV q R f ε) b)))) (𝓝[≠] 0)
    (𝓝 (pE (geomOf 2 1 (dilTower q R)) J'))
  simp only [← map_smul]
  exact ((pE (geomOf 2 1 (dilTower q R))).continuous.tendsto _).comp hJ'

/-- `Δ⁽²⁾(ε)/ε` converges as `ε → 0` from both sides, for every profile. -/
theorem bulk_exists_D1 {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ∃ D₁ : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      Tendsto (fun ε : ℝ => ε⁻¹ • QualitativeR2.bulkD q R f ε) (𝓝[≠] 0) (𝓝 D₁) := by
  obtain ⟨J', hJ⟩ := bulk_J_tendsto q R f
  obtain ⟨D₁, hD₁⟩ := AnalyticR2.tendsto_Delta2_div
    (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1
      (dilLam q R))
    (fun ε => dataS_laws selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (bulkV q R f ε) 1 (dilLam q R)))
    (bulk_H_cont hq hR16 hS f) (bulk_C2_tendsto hq hS f) J' hJ
  refine ⟨D₁, ?_⟩
  simp only [bulkD_eq_dataFam]
  exact hD₁

/-- At zero curvature the correction of the interior family vanishes. -/
theorem bulkD_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (h3 : 3 ≤ R * (2*q))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : QualitativeR2.bulkD q R f 0 = 0 := by
  rw [← QualitativeR2.pathD_base q R (QualitativeR2.uthPath_zero q R) f 0]
  exact pathD_zero hq hR h3 (uthPath q R) f 1 0

/-- **The correction of the interior family is differentiable at the flat interior**, for every
profile. -/
theorem bulk_hasDerivAt {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R f ε) De 0 := by
  obtain ⟨D₁, hD₁⟩ := bulk_exists_D1 hq hR16 (dil_admissible hq hR) f
  have hq1 : 1 ≤ q := hq
  have h3 : 3 ≤ R * (2*q) := by nlinarith
  have h0 := bulkD_zero hq hR h3 f
  refine ⟨D₁, (hasDerivAt_iff_tendsto_slope_zero (f := fun ε : ℝ => QualitativeR2.bulkD q R f ε)
    (f' := D₁) (x := 0)).mpr ?_⟩
  refine hD₁.congr' (Filter.Eventually.of_forall (fun t => ?_))
  simp only [zero_add, h0, sub_zero]

/-- The actual first-order coefficient of the localized correction along the interior family of
the profile `f`. -/
noncomputable def corrDeriv (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  deriv (fun ε : ℝ => QualitativeR2.bulkD q R f ε) 0

theorem hasDerivAt_corrDeriv {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R f ε) (corrDeriv q R f) 0 := by
  obtain ⟨De, h⟩ := bulk_hasDerivAt hq hR hR16 f
  have e : corrDeriv q R f = De :=
    HasDerivAt.deriv (f := fun ε : ℝ => QualitativeR2.bulkD q R f ε) (f' := De) (x := 0) h
  rw [e]
  exact h

/-- **This round's soft premise is a theorem**, for every profile, every scale `q > 0` and every
even radius `R ≥ 16`. -/
theorem interiorSoft_corrDeriv {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    QualitativeR2.InteriorSoft q R f (corrDeriv q R f) := by
  have hS := dil_admissible hq hR
  refine ⟨?_, bulk_W_cont hq hS f, hasDerivAt_corrDeriv hq hR hR16 f⟩
  show ContinuousAt (fun ε => (AnalyticR2.dataFam selAll selAll (by norm_num : 0 < 2)
    (dilTower q R) (bulkV q R f) 1 (dilLam q R) ε).Ginv) 0
  exact bulk_carrier_cont hq hS f selAll selAll

theorem interiorSoft_exists {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      QualitativeR2.InteriorSoft q R f De :=
  ⟨_, interiorSoft_corrDeriv hq hR hR16 f⟩

/-! ## C. The canonical crossing at every instance -/

/-- The flat localized carrier is a unit at every scale and radius (analytic route). -/
theorem flat_loc_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataS selIn selIn (QualitativeR2.flatP q R)).Ginv :=
  AnalyticR2.dil_flat_unit hq hR

/-- **Unconditional, at every instance.**  For every scale `q > 0` and every even `R ≥ 18` the
vacuum carrier of the round-8 twist crosses at its canonical angle, forwards and backwards. -/
theorem twist_vacuum_crossing_all {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    QualitativeR2.VacuumCrossesAt q R (uthPath q R) (QualitativeR2.vacEdge q R (uthPath q R)) ∧
    QualitativeR2.VacuumCrossesAt q R (QualitativeR2.uthPathNeg q R)
      (QualitativeR2.vacEdge q R (QualitativeR2.uthPathNeg q R)) := by
  have hq1 : 1 ≤ q := hq
  have hroom : 17*2 ≤ R*(2*q) := by nlinarith
  have hloc := flat_loc_unit hq (by omega : 1 ≤ R)
  exact ⟨QualitativeR2.vacuum_crossing hq hR hroom (uthPath_cont _ _)
      (QualitativeR2.uthPath_anFam _ _)
      (QualitativeR2.vacA_pd_zero (QualitativeR2.uthPath_zero _ _) hloc)
      (QualitativeR2.vacA_uth_pi_negative hq hR hroom),
    QualitativeR2.vacuum_crossing hq hR hroom (QualitativeR2.uthPathNeg_cont _ _)
      (QualitativeR2.uthPathNeg_anFam _ _)
      (QualitativeR2.vacA_pd_zero (QualitativeR2.uthPathNeg_zero _ _) hloc)
      (QualitativeR2.vacA_uthNeg_pi_negative hq hR hroom)⟩

/-! ## D. The reduced premise: the coupling alone -/

/-- **Per instance.**  For every scale `q > 0` and every even `R ≥ 18`: if the actual first-order
coefficient of the single-defect correction is definite, of either sign, on the kernel of the
vacuum carrier at the canonical crossing of the round-8 twist, then the literal round-8 family
separates at every small positive curvature. -/
theorem twistSeparation_eventually_of_coupling {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hR18 : 18 ≤ R)
    (hc : QualitativeR2.CanonicalCoupling q R (uthPath q R) (corrDeriv q R (dilMask q R))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → TwistSeparation q R ε :=
  QualitativeR2.twistSeparation_eventually hq hR hR18 (flat_loc_unit hq (by omega))
    (QualitativeR2.twistSoftCoupling_of_fwd
      ⟨corrDeriv q R (dilMask q R), interiorSoft_corrDeriv hq hR (by omega) _, hc⟩)

/-- **X (literal family).**  For cofinal dyadic scales and, for each, cofinal even radii
`≥ 18`: the actual first-order coefficient of the single-defect correction is definite, of
either sign, on the kernel of the vacuum carrier of the round-8 twist at its canonical
crossing.  NOT proved here. -/
def CofinalCanonicalCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R) (corrDeriv (2^j) R (dilMask (2^j) R))

/-- **Main reduction: `X → CofinalTwistSeparation`** (round 8's target). -/
theorem cofinalTwistSeparation_of_cofinalCanonicalCoupling (h : CofinalCanonicalCoupling) :
    CofinalTwistSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun δ hδ => ?_⟩
  obtain ⟨ε₀, hε₀, hall⟩ := twistSeparation_eventually_of_coupling (by positivity) hR hR18 hc
  have hm : 0 < min δ ε₀ := lt_min hδ hε₀
  exact ⟨min δ ε₀ / 2, by positivity, by linarith [min_le_left δ ε₀],
    hall (min δ ε₀ / 2) (by positivity) (by linarith [min_le_right δ ε₀])⟩

/-- **Main reduction: `X → GoalNeg2`.** -/
theorem goalNeg2_of_cofinalCanonicalCoupling (h : CofinalCanonicalCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_cofinalCanonicalCoupling h)

theorem not_cofinalCanonicalCoupling_of_goalPos1 (h : GoalPos1) : ¬ CofinalCanonicalCoupling :=
  fun h' => goalNeg2_of_cofinalCanonicalCoupling h' (goalPos2_iff_goalPos1.mpr h)

/-- What the positive reading demands: at every large scale and every large even radius the
first-order coupling is NOT definite on the canonical vacuum kernel. -/
theorem goalPos1_forces_degenerate_coupling (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ¬ QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R)
        (corrDeriv (2^j) R (dilMask (2^j) R)) := by
  have h' := not_cofinalCanonicalCoupling_of_goalPos1 h
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
  exact ⟨R, hRR, hR2, hR18, not_not.mp hR4⟩

/-- At one instance, the reduced premise of the first part of this round
(`QualitativeR2.TwistSoftCouplingFwd`: soft regularity and a definite coupling) is exactly the
coupling clause for the actual derivative: its soft clause is a theorem, and any derivative in it
is `corrDeriv`. -/
theorem twistSoftCouplingFwd_iff {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R) :
    QualitativeR2.TwistSoftCouplingFwd q R ↔
      QualitativeR2.CanonicalCoupling q R (uthPath q R) (corrDeriv q R (dilMask q R)) := by
  constructor
  · rintro ⟨De, hs, hc⟩
    have e : De = corrDeriv q R (dilMask q R) :=
      HasDerivAt.unique (f := fun ε : ℝ => QualitativeR2.bulkD q R (dilMask q R) ε) (f₀' := De)
        (f₁' := corrDeriv q R (dilMask q R)) (x := 0) hs.2.2
        (hasDerivAt_corrDeriv hq hR hR16 (dilMask q R))
    rw [← e]
    exact hc
  · intro hc
    exact ⟨_, interiorSoft_corrDeriv hq hR hR16 _, hc⟩

/-- `CofinalCanonicalCoupling` is the first part's `CofinalTwistSoftCouplingFwd` with its soft
clause removed. -/
theorem cofinalCanonicalCoupling_iff :
    CofinalCanonicalCoupling ↔ QualitativeR2.CofinalTwistSoftCouplingFwd := by
  constructor
  · intro h j₀
    obtain ⟨j, hj, hRs⟩ := h j₀
    refine ⟨j, hj, fun R₀ => ?_⟩
    obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
    exact ⟨R, hRR, hR, hR18, (twistSoftCouplingFwd_iff (by positivity) hR (by omega)).mpr hc⟩
  · intro h j₀
    obtain ⟨j, hj, hRs⟩ := h j₀
    refine ⟨j, hj, fun R₀ => ?_⟩
    obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
    exact ⟨R, hRR, hR, hR18, (twistSoftCouplingFwd_iff (by positivity) hR (by omega)).mp hc⟩

/-! ## E. Free profile -/

theorem bulkU_smul (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (c ε : ℝ) :
    QualitativeR2.bulkU q R (fun e => c * f e) ε = QualitativeR2.bulkU q R f (c * ε) := by
  unfold QualitativeR2.bulkU
  congr 1
  funext e
  ring

theorem bulkD_smul (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (c ε : ℝ) :
    QualitativeR2.bulkD q R (fun e => c * f e) ε = QualitativeR2.bulkD q R f (c * ε) := by
  have hd : dataS selIn selIn (QualitativeR2.bulkP q R (fun e => c * f e) ε) =
      dataS selIn selIn (QualitativeR2.bulkP q R f (c * ε)) := by
    unfold QualitativeR2.bulkP
    rw [bulkU_smul]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

/-- Rescaling the profile rescales the first-order coefficient. -/
theorem corrDeriv_smul {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (c : ℝ) :
    corrDeriv q R (fun e => c * f e) = c • corrDeriv q R f := by
  have h1 := hasDerivAt_corrDeriv hq hR hR16 f
  have hl : HasDerivAt (fun ε : ℝ => c * ε) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
  have h1' : HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R f ε) (corrDeriv q R f) (c * 0) := by
    rw [mul_zero]
    exact h1
  have h2 : HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R f (c * ε)) (c • corrDeriv q R f) 0 :=
    HasDerivAt.scomp (g₁ := fun ε : ℝ => QualitativeR2.bulkD q R f ε) (h := fun ε : ℝ => c * ε)
      0 h1' hl
  have e : (fun ε : ℝ => QualitativeR2.bulkD q R (fun e => c * f e) ε) =
      fun ε => QualitativeR2.bulkD q R f (c * ε) := funext (bulkD_smul q R f c)
  have h3 : HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R (fun e => c * f e) ε)
      (c • corrDeriv q R f) 0 := by
    rw [e]
    exact h2
  exact HasDerivAt.deriv (f := fun ε : ℝ => QualitativeR2.bulkD q R (fun e => c * f e) ε)
    (f' := c • corrDeriv q R f) (x := 0) h3

/-- A definite coupling stays definite under a nonzero rescaling. -/
theorem canonicalCoupling_smul {q R : ℕ} {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    {c : ℝ} (hc : c ≠ 0) (h : QualitativeR2.CanonicalCoupling q R V De) :
    QualitativeR2.CanonicalCoupling q R V (c • De) := by
  obtain ⟨c₀, hc₀, hs⟩ := h
  have e : ∀ u, ⟪u, (c • De) u⟫ = c * ⟪u, De u⟫ := fun u => by
    rw [smul_apply, real_inner_smul_right]
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have hc' : 0 ≤ -c := by linarith
    refine ⟨(-c) * c₀, mul_pos (neg_pos.mpr hneg) hc₀, ?_⟩
    rcases hs with hp | hn
    · refine Or.inr (fun u hu => ?_)
      have h1 := mul_le_mul_of_nonneg_left (hp u hu) hc'
      rw [e]
      nlinarith [h1]
    · refine Or.inl (fun u hu => ?_)
      have h1 := mul_le_mul_of_nonneg_left (hn u hu) hc'
      rw [e]
      nlinarith [h1]
  · refine ⟨c * c₀, mul_pos hpos hc₀, ?_⟩
    rcases hs with hp | hn
    · refine Or.inl (fun u hu => ?_)
      have h1 := mul_le_mul_of_nonneg_left (hp u hu) hpos.le
      rw [e]
      nlinarith [h1]
    · refine Or.inr (fun u hu => ?_)
      have h1 := mul_le_mul_of_nonneg_left (hn u hu) hpos.le
      rw [e]
      nlinarith [h1]

/-- **X (free profile, weakest form).**  For cofinal dyadic scales and, for each, cofinal even
radii `≥ 18`: SOME interior profile has a first-order coefficient that is definite, of either
sign, on the kernel of the vacuum carrier at the canonical crossing of the round-8 twist.
NOT proved here. -/
def CofinalAnyProfileCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
      QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R) (corrDeriv (2^j) R f)

/-- Every profile has a positive multiple within the class bound `|f| ≤ 1`. -/
theorem exists_profile_scale {L : PeriodicLatticeExtent} (f : Bond L → ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ e, |c * f e| ≤ 1 := by
  have hs0 : 0 ≤ ∑ e, |f e| := Finset.sum_nonneg (fun e _ => abs_nonneg (f e))
  have hpos : (0 : ℝ) < 1 + ∑ e, |f e| := by linarith
  refine ⟨1 / (1 + ∑ e, |f e|), one_div_pos.mpr hpos, fun e => ?_⟩
  have h1 : |f e| ≤ ∑ e, |f e| :=
    Finset.single_le_sum (f := fun e => |f e|) (fun e _ => abs_nonneg (f e)) (Finset.mem_univ e)
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hpos), one_div, inv_mul_le_iff₀ hpos]
  linarith

/-- Any profile with a definite coupling, rescaled into the class bound, gives round 9.2's
weakest premise at that instance. -/
theorem pathSoftCoupling_of_profile {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (hc : QualitativeR2.CanonicalCoupling q R (uthPath q R) (corrDeriv q R f)) :
    QualitativeR2.PathSoftCoupling q R := by
  obtain ⟨c, hcpos, hcb⟩ := exists_profile_scale f
  refine ⟨fun e => c * f e, hcb, corrDeriv q R (fun e => c * f e),
    interiorSoft_corrDeriv hq hR hR16 _, Or.inl ?_⟩
  rw [corrDeriv_smul hq hR hR16 f c]
  exact canonicalCoupling_smul hcpos.ne' hc

theorem cofinalPathSoftCoupling_of_anyProfile (h : CofinalAnyProfileCoupling) :
    QualitativeR2.CofinalPathSoftCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, f, hc⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, pathSoftCoupling_of_profile (by positivity) hR (by omega) f hc⟩

/-- **Main reduction (weakest premise): `X → GoalNeg2`.** -/
theorem goalNeg2_of_cofinalAnyProfileCoupling (h : CofinalAnyProfileCoupling) : GoalNeg2 :=
  QualitativeR2.goalNeg2_of_cofinalPathSoftCoupling (cofinalPathSoftCoupling_of_anyProfile h)

theorem not_cofinalAnyProfileCoupling_of_goalPos1 (h : GoalPos1) : ¬ CofinalAnyProfileCoupling :=
  fun h' => goalNeg2_of_cofinalAnyProfileCoupling h' (goalPos2_iff_goalPos1.mpr h)

theorem cofinalAnyProfileCoupling_of_canonical (h : CofinalCanonicalCoupling) :
    CofinalAnyProfileCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, dilMask (2^j) R, hc⟩

/-- What the positive reading demands, over all profiles: at every large scale and every large
even radius, NO interior profile has a definite first-order coupling on the canonical vacuum
kernel. -/
theorem goalPos1_forces_degenerate_profiles (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ∀ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
        ¬ QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R) (corrDeriv (2^j) R f) := by
  have h' := not_cofinalAnyProfileCoupling_of_goalPos1 h
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
  obtain ⟨f, hf⟩ := not_forall.mp hR4
  exact ⟨R, hRR, hR2, hR18, f, not_not.mp hf⟩

/-! ## F. The explicit coupling `2⟪H₀ C²₀(W₀ u), J'⟫` (analytic route) -/

theorem bulkU_dilMask (q R : ℕ) (ε : ℝ) :
    QualitativeR2.bulkU q R (dilMask q R) ε = dilU q R ε 1 := by
  classical
  funext e
  simp only [QualitativeR2.bulkU, maskedU, dilU, dilMask]
  split_ifs <;> first | rfl | simp

theorem bulkD_dilMask (q R : ℕ) (ε : ℝ) :
    QualitativeR2.bulkD q R (dilMask q R) ε = AnalyticR1.extD q R ε 1 := by
  have hd : dataS selIn selIn (QualitativeR2.bulkP q R (dilMask q R) ε) =
      dataS selIn selIn (AnalyticR1.extP q R ε 1) := by
    unfold QualitativeR2.bulkP AnalyticR1.extP
    rw [bulkU_dilMask]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

/-- The quadratic form of the actual first-order coefficient of the single-defect correction is
the analytic route's explicit vacuum coupling `2⟪H₀ C²₀(W₀ u), J'⟫`. -/
theorem corrDeriv_dilMask_form {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (J' : AnalyticR1.TwistSpace q R) (hJ : AnalyticR2.IsSourceDerivative q R J')
    (u : AnalyticR1.TwistSpace q R) :
    ⟪u, corrDeriv q R (dilMask q R) u⟫ = AnalyticR2.vacCoupling q R J' u := by
  have hD := hasDerivAt_corrDeriv hq hR hR16 (dilMask q R)
  have hq1 : 1 ≤ q := hq
  have h3 : 3 ≤ R * (2*q) := by nlinarith
  have h0 : AnalyticR1.extD q R 0 1 = 0 := by
    rw [← bulkD_dilMask]
    exact bulkD_zero hq hR h3 (dilMask q R)
  have hT : Tendsto (fun ε : ℝ => ε⁻¹ • AnalyticR1.extD q R ε 1) (𝓝[>] 0)
      (𝓝 (corrDeriv q R (dilMask q R))) := by
    refine (HasDerivAt.tendsto_slope_zero_right
      (f := fun ε : ℝ => QualitativeR2.bulkD q R (dilMask q R) ε)
      (f' := corrDeriv q R (dilMask q R)) (x := 0) hD).congr'
      (Filter.Eventually.of_forall (fun t => ?_))
    simp only [zero_add, bulkD_dilMask, h0, sub_zero]
  exact AnalyticR2.dil_D1_form hq (dil_admissible hq hR) hR16 _ hT J' hJ u

/-- **X at one instance, explicit form.**  For the curvature derivative `J'` of the localized
source, the explicit coupling `2⟪H₀ C²₀(W₀ u), J'⟫` is definite, of either sign, on the kernel
of the vacuum carrier at the canonical crossing of the round-8 twist.  NOT proved here. -/
def ExplicitCoupling (q R : ℕ) : Prop :=
  ∀ J' : AnalyticR1.TwistSpace q R, AnalyticR2.IsSourceDerivative q R J' →
    ∃ c : ℝ, 0 < c ∧
      ((∀ u, vacA q R (uthPath q R) 1 (QualitativeR2.vacEdge q R (uthPath q R)) u = 0 →
          c * ‖u‖ ^ 2 ≤ AnalyticR2.vacCoupling q R J' u) ∨
        (∀ u, vacA q R (uthPath q R) 1 (QualitativeR2.vacEdge q R (uthPath q R)) u = 0 →
          c * ‖u‖ ^ 2 ≤ -AnalyticR2.vacCoupling q R J' u))

theorem canonicalCoupling_of_explicit {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (h : ExplicitCoupling q R) :
    QualitativeR2.CanonicalCoupling q R (uthPath q R) (corrDeriv q R (dilMask q R)) := by
  obtain ⟨J', hJ'⟩ := AnalyticR2.dil_J_tendsto q R
  obtain ⟨c, hc, hp | hn⟩ := h J' hJ'
  · exact ⟨c, hc, Or.inl (fun u hu => by
      rw [corrDeriv_dilMask_form hq hR hR16 J' hJ' u]; exact hp u hu)⟩
  · exact ⟨c, hc, Or.inr (fun u hu => by
      rw [corrDeriv_dilMask_form hq hR hR16 J' hJ' u]; exact hn u hu)⟩

def CofinalExplicitCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ExplicitCoupling (2^j) R

theorem cofinalCanonicalCoupling_of_explicit (h : CofinalExplicitCoupling) :
    CofinalCanonicalCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, canonicalCoupling_of_explicit (by positivity) hR (by omega) hc⟩

theorem cofinalTwistSeparation_of_cofinalExplicitCoupling (h : CofinalExplicitCoupling) :
    CofinalTwistSeparation :=
  cofinalTwistSeparation_of_cofinalCanonicalCoupling (cofinalCanonicalCoupling_of_explicit h)

theorem goalNeg2_of_cofinalExplicitCoupling (h : CofinalExplicitCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalCanonicalCoupling (cofinalCanonicalCoupling_of_explicit h)

/-- **X at one instance, complex-line form.**  The canonical forward vacuum kernel is the complex
line of one charged vector `u₀` (`J (J u₀) = -u₀`, `J` the quarter rotation), and the explicit
coupling of `u₀` is nonzero: round 8's `c₁(q,R) ≠ 0`.  NOT proved here. -/
def ExplicitU1 (q R : ℕ) : Prop :=
  ∃ u₀ : AnalyticR1.TwistSpace q R, u₀ ≠ 0 ∧
    vacA q R (uthPath q R) 1 (QualitativeR2.vacEdge q R (uthPath q R)) u₀ = 0 ∧
    adEL (QualitativeR2.rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
      (adEL (QualitativeR2.rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀) = -u₀ ∧
    (∀ u, vacA q R (uthPath q R) 1 (QualitativeR2.vacEdge q R (uthPath q R)) u = 0 →
      u ∈ Submodule.span ℝ {u₀,
        adEL (QualitativeR2.rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀}) ∧
    ∀ J' : AnalyticR1.TwistSpace q R, AnalyticR2.IsSourceDerivative q R J' →
      AnalyticR2.vacCoupling q R J' u₀ ≠ 0

theorem canonicalCoupling_of_explicitU1 {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (h : ExplicitU1 q R) :
    QualitativeR2.CanonicalCoupling q R (uthPath q R) (corrDeriv q R (dilMask q R)) := by
  obtain ⟨u₀, hu₀, hk, hJJ, hK, hc⟩ := h
  obtain ⟨J', hJ'⟩ := AnalyticR2.dil_J_tendsto q R
  refine QualitativeR2.canonicalCoupling_of_U1 (hasDerivAt_corrDeriv hq hR hR16 (dilMask q R))
    ⟨u₀, hu₀, hk, hJJ, hK, ?_⟩
  rw [corrDeriv_dilMask_form hq hR hR16 J' hJ' u₀]
  exact hc J' hJ'

def CofinalExplicitU1 : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ ExplicitU1 (2^j) R

theorem goalNeg2_of_cofinalExplicitU1 (h : CofinalExplicitU1) : GoalNeg2 := by
  apply goalNeg2_of_cofinalCanonicalCoupling
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, canonicalCoupling_of_explicitU1 (by positivity) hR (by omega) hc⟩

theorem cofinalTwistSeparation_of_cofinalExplicitU1 (h : CofinalExplicitU1) :
    CofinalTwistSeparation := by
  apply cofinalTwistSeparation_of_cofinalCanonicalCoupling
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, canonicalCoupling_of_explicitU1 (by positivity) hR (by omega) hc⟩

/-! ## G. Any analytic exterior path -/

/-- **X (weakest form, over exterior paths and profiles).**  For cofinal dyadic scales and, for
each, cofinal even radii `≥ 18`: SOME continuous, real-analytic exterior path starting at the
trivial field, whose vacuum carrier has a negative direction at angle `π`, and SOME interior
profile, whose first-order coefficient is definite, of either sign, on the kernel of the vacuum
carrier at the canonical crossing of that path.  NOT proved here. -/
def CofinalAnyPathCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
      QualitativeR2.AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
        QualitativeR2.CanonicalCoupling (2^j) R V (corrDeriv (2^j) R f)

theorem cofinalVacuumCoupling_of_anyPath (h : CofinalAnyPathCoupling) : CofinalVacuumCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hVc, hVa, hV0, hneg, f, hc⟩ := hRs R₀
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  obtain ⟨c, hcpos, hcb⟩ := exists_profile_scale f
  have hc' : QualitativeR2.CanonicalCoupling (2^j) R V (corrDeriv (2^j) R (fun e => c * f e)) := by
    rw [corrDeriv_smul hq hR (by omega) f c]
    exact canonicalCoupling_smul hcpos.ne' hc
  exact ⟨R, hRR, hR, hR18, V, hVc, fun e => c * f e, hcb,
    QualitativeR2.vacuumCoupling_of_soft hq hR hroom hVc hVa hV0 (flat_loc_unit hq (by omega))
      hneg (interiorSoft_corrDeriv hq hR (by omega) _) hc'⟩

/-- **Main reduction (weakest premise over paths and profiles): `X → GoalNeg2`.** -/
theorem goalNeg2_of_cofinalAnyPathCoupling (h : CofinalAnyPathCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalVacuumCoupling (cofinalVacuumCoupling_of_anyPath h)

theorem not_cofinalAnyPathCoupling_of_goalPos1 (h : GoalPos1) : ¬ CofinalAnyPathCoupling :=
  fun h' => goalNeg2_of_cofinalAnyPathCoupling h' (goalPos2_iff_goalPos1.mpr h)

/-- The round-8 twist is such a path. -/
theorem cofinalAnyPathCoupling_of_anyProfile (h : CofinalAnyProfileCoupling) :
    CofinalAnyPathCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, f, hc⟩ := hRs R₀
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  exact ⟨R, hRR, hR, hR18, uthPath (2^j) R, uthPath_cont _ _, QualitativeR2.uthPath_anFam _ _,
    QualitativeR2.uthPath_zero _ _, QualitativeR2.vacA_uth_pi_negative hq hR hroom, f, hc⟩

end AdalyFormal.Round9.Guarded.QualitativeR2Joint

#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkV
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkU_link_contDiff
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkV_smooth
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkV_contFam
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkU_zero
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_dataFam_zero
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_dataFam_zero_eq
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkD_eq_dataFam
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkA_eq_dataFam
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_LP0
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_Gam0
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_reg0
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_W_cont
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_T_cont
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_Q_cont
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_carrier_cont
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_H_cont
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_C2_tendsto
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_J_tendsto
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_exists_D1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkD_zero
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_hasDerivAt
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.hasDerivAt_corrDeriv
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.interiorSoft_corrDeriv
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.interiorSoft_exists
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.flat_loc_unit
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.twist_vacuum_crossing_all
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.twistSeparation_eventually_of_coupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalCanonicalCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalCanonicalCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalCanonicalCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.not_cofinalCanonicalCoupling_of_goalPos1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalPos1_forces_degenerate_coupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.twistSoftCouplingFwd_iff
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalCanonicalCoupling_iff
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkU_smul
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkD_smul
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv_smul
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_smul
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyProfileCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.exists_profile_scale
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.pathSoftCoupling_of_profile
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalPathSoftCoupling_of_anyProfile
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyProfileCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.not_cofinalAnyProfileCoupling_of_goalPos1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalAnyProfileCoupling_of_canonical
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalPos1_forces_degenerate_profiles
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkU_dilMask
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkD_dilMask
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv_dilMask_form
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.ExplicitCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_of_explicit
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalExplicitCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalCanonicalCoupling_of_explicit
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalExplicitCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalExplicitCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.ExplicitU1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_of_explicitU1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalExplicitU1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalExplicitU1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalExplicitU1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyPathCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalVacuumCoupling_of_anyPath
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyPathCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.not_cofinalAnyPathCoupling_of_goalPos1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalAnyPathCoupling_of_anyProfile
