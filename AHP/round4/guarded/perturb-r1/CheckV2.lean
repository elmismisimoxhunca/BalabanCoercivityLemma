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
Round 4, perturbation route. No pinned goal is changed. The small-correction
estimate below is conditional on the genuine localized D-layer estimates.
The continuity result concerns the actual frozen exterior-twist family, not a
scalar substitute for the lattice operators.
-/
namespace AdalyFormal.Round4.Guarded.PerturbR1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round2.Guarded.R2Prove
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- Verbatim finite-dimensional criterion from round 2. -/
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

/-- A lower singular-value bound suffices; positivity is unnecessary. -/
theorem unit_of_gain (T : E →L[ℝ] E) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x, δ * ‖x‖ ≤ ‖T x‖) : IsUnit T := by
  apply unit_of_kernel_zero T
  intro x hx
  have hh := h x
  rw [hx, norm_zero] at hh
  exact norm_eq_zero.mp (le_antisymm (by nlinarith [norm_nonneg x]) (norm_nonneg x))

omit [FiniteDimensional ℝ E] in
/-- Symmetry turns the diagonal form bound into the full operator norm bound. -/
theorem norm_le_of_quadratic (D : E →L[ℝ] E) {ε : ℝ} (hε : 0 ≤ ε)
    (hs : ∀ x y, ⟪D x, y⟫ = ⟪x, D y⟫)
    (hq : ∀ x, |⟪x, D x⟫| ≤ ε * ‖x‖ ^ 2) : ‖D‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hε
  intro x y hx hy
  have hp := (abs_le.mp (hq (x + y))).2
  have hm := (abs_le.mp (hq (x - y))).1
  have hpar := parallelogram_law_with_norm ℝ x y
  rw [hx, hy] at hpar
  simp only [map_add, map_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right] at hp hm
  have hsxy : ⟪y, D x⟫ = ⟪x, D y⟫ := by rw [real_inner_comm, hs]
  rw [hsxy] at hp hm
  change ⟪D x, y⟫ ≤ ε
  rw [hs]
  nlinarith

omit [FiniteDimensional ℝ E] in
/-- An explicit pointwise radius, not a uniform class radius. -/
theorem gain_of_unit (A : E →L[ℝ] E) (hA : IsUnit A) :
    ∀ x, (‖Ring.inverse A‖ + 1)⁻¹ * ‖x‖ ≤ ‖A x‖ := by
  intro x
  have hi : Ring.inverse A (A x) = x :=
    congrArg (fun T : E →L[ℝ] E => T x) (Ring.inverse_mul_cancel A hA)
  have hn := (Ring.inverse A).le_opNorm (A x)
  rw [hi] at hn
  have hc : 0 < ‖Ring.inverse A‖ + 1 := by positivity
  apply (le_of_mul_le_mul_left ?_ hc)
  calc (‖Ring.inverse A‖ + 1) * ((‖Ring.inverse A‖ + 1)⁻¹ * ‖x‖) = ‖x‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    _ ≤ ‖Ring.inverse A‖ * ‖A x‖ := hn
    _ ≤ (‖Ring.inverse A‖ + 1) * ‖A x‖ := by nlinarith [norm_nonneg (A x)]

/-- A correction smaller than a genuine gain preserves invertibility. -/
theorem unit_sub_of_gain (A D : E →L[ℝ] E) {δ : ℝ} (_hδ : 0 < δ)
    (hA : ∀ x, δ * ‖x‖ ≤ ‖A x‖) (hD : ‖D‖ < δ) : IsUnit (A - D) := by
  apply unit_of_kernel_zero
  intro x hx
  have heq : A x = D x := sub_eq_zero.mp hx
  have hh := hA x
  rw [heq] at hh
  have hb := D.le_opNorm x
  by_contra hne
  have ht := mul_lt_mul_of_pos_right hD (norm_pos_iff.mpr hne)
  exact (not_lt_of_ge (hh.trans hb)) ht

/-- Compactness applies if EVERY point of the compact parameter set is a unit.
Restricting afterward to an open guard domain does not meet this premise. -/
theorem compact_units_inverse_bound {X : Type*} [TopologicalSpace X]
    (F : X → (E →L[ℝ] E)) {K : Set X} (hK : IsCompact K)
    (hF : ContinuousOn F K) (hu : ∀ t ∈ K, IsUnit (F t)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ K, ‖Ring.inverse (F t)‖ ≤ C := by
  have hc : ContinuousOn (fun t => ‖Ring.inverse (F t)‖) K := by
    intro t ht
    obtain ⟨u, heq⟩ := hu t ht
    have hi : ContinuousAt Ring.inverse (F t) := by
      rw [← heq]
      exact NormedRing.inverse_continuousAt u
    exact (hi.comp_continuousWithinAt (hF t ht)).norm
  obtain ⟨C, hC⟩ := hK.bddAbove_image hc
  refine ⟨max C 0 + 1, by positivity, fun t ht => ?_⟩
  exact (hC (Set.mem_image_of_mem _ ht)).trans (by linarith [le_max_left C 0])

/-- On a connected parameter space a path from a unit to a non-unit has
arbitrarily small gain AT GUARDED POINTS. The near-singular points are not
silently excluded from the assertion. -/
theorem connected_guard_small_gain {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (F : X → (E →L[ℝ] E)) (hF : Continuous F)
    (p q : X) (hp : IsUnit (F p)) (hq : ¬ IsUnit (F q))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ t : X, IsUnit (F t) ∧ ∃ x : E, x ≠ 0 ∧ ‖F t x‖ < δ * ‖x‖ := by
  by_contra hn
  push Not at hn
  have hlow : ∀ t, IsUnit (F t) → ∀ x, δ * ‖x‖ ≤ ‖F t x‖ := by
    intro t ht x
    by_cases hx : x = 0
    · simp [hx]
    · exact hn t ht x hx
  have heq : {t : X | IsUnit (F t)} =
      ⋂ x : E, {t : X | δ * ‖x‖ ≤ ‖F t x‖} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨hlow t, unit_of_gain (F t) hδ⟩
  have hc : IsClosed {t : X | IsUnit (F t)} := by
    rw [heq]
    apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const (by fun_prop)
  have ho : IsOpen {t : X | IsUnit (F t)} := Units.isOpen.preimage hF
  have hall := (IsClopen.eq_univ ⟨hc, ho⟩ ⟨p, hp⟩)
  apply hq
  change q ∈ {t : X | IsUnit (F t)}
  rw [hall]
  trivial

/-- The same failure of uniformity already occurs on one compact interval. -/
theorem interval_guard_small_gain (F : ℝ → (E →L[ℝ] E)) (hF : Continuous F)
    {T : ℝ} (hT : 0 ≤ T) (h0 : IsUnit (F 0)) (hbad : ¬ IsUnit (F T))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ t ∈ Set.Icc (0 : ℝ) T, IsUnit (F t) ∧
      ∃ x : E, x ≠ 0 ∧ ‖F t x‖ < δ * ‖x‖ := by
  letI : PreconnectedSpace (Set.Icc (0 : ℝ) T) := Subtype.preconnectedSpace isPreconnected_Icc
  obtain ⟨t, ht, x, hx, hg⟩ := connected_guard_small_gain
    (fun t : Set.Icc (0 : ℝ) T => F t) (hF.comp continuous_subtype_val)
    ⟨0, le_rfl, hT⟩ ⟨T, hT, le_rfl⟩ h0 hbad δ hδ
  exact ⟨t, t.property, ht, x, hx, hg⟩

/-- Verbatim response/unit equivalence from round 2. -/
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

/-- A quantitative gain of the boundary response controls the carrier even
though the response range depends on the operator. -/
theorem response_gain_controls_carrier (A B : E →L[ℝ] E) (hB : IsUnit B)
    {δ T : ℝ} (hδ : 0 < δ) (hT : ‖A - B‖ ≤ T)
    (hK : ∀ y : (A - B).range, δ * ‖y‖ ≤ ‖response (A - B) B y‖) (x : E) :
    δ * ‖x‖ ≤ (δ * ‖Ring.inverse B‖ + ‖Ring.inverse B‖ * T * ‖Ring.inverse B‖) * ‖A x‖ := by
  let Θ := A - B
  let C := ‖Ring.inverse B‖
  let y : Θ.range := ⟨Θ x, ⟨x, rfl⟩⟩
  have hi : Ring.inverse B (B x) = x :=
    congrArg (fun F : E →L[ℝ] E => F x) (Ring.inverse_mul_cancel B hB)
  have hxy : x = Ring.inverse B (A x) - Ring.inverse B (y : E) := by
    change x = Ring.inverse B (A x) - Ring.inverse B (A x - B x)
    rw [map_sub, hi]
    abel
  have hKy : (response Θ B y : E) = Θ (Ring.inverse B (A x)) := by
    change Θ x + Θ (Ring.inverse B (A x - B x)) = _
    rw [map_sub, hi, map_sub]
    abel
  have hxn : ‖x‖ ≤ C * ‖A x‖ + C * ‖y‖ := by
    calc ‖x‖ = ‖Ring.inverse B (A x) - Ring.inverse B (y : E)‖ := congrArg norm hxy
      _ ≤ ‖Ring.inverse B (A x)‖ + ‖Ring.inverse B (y : E)‖ := norm_sub_le _ _
      _ ≤ C * ‖A x‖ + C * ‖y‖ := add_le_add
        ((Ring.inverse B).le_opNorm _) ((Ring.inverse B).le_opNorm _)
  have hyn : δ * ‖y‖ ≤ T * (C * ‖A x‖) := by
    calc δ * ‖y‖ ≤ ‖response Θ B y‖ := hK y
      _ = ‖Θ (Ring.inverse B (A x))‖ := congrArg norm hKy
      _ ≤ ‖Θ‖ * ‖Ring.inverse B (A x)‖ := Θ.le_opNorm _
      _ ≤ T * (C * ‖A x‖) := mul_le_mul hT ((Ring.inverse B).le_opNorm _)
        (norm_nonneg _) ((norm_nonneg (A - B)).trans hT)
  have hC : 0 ≤ C := norm_nonneg _
  have hhx := mul_le_mul_of_nonneg_left hxn hδ.le
  have hhy := mul_le_mul_of_nonneg_left hyn hC
  change δ * ‖x‖ ≤ (δ * C + C * T * C) * ‖A x‖
  nlinarith

/-- Compactness does NOT supply a uniform boundary-response gap on the guarded
part of a continuous path that meets a carrier singularity. The reference B is
a fixed unit. This handles the changing response ranges without identifying them. -/
theorem interval_guard_small_response (F : ℝ → (E →L[ℝ] E)) (hF : Continuous F)
    (B : E →L[ℝ] E) (hB : IsUnit B) {T : ℝ} (hT : 0 ≤ T)
    (h0 : IsUnit (F 0)) (hbad : ¬ IsUnit (F T)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ t ∈ Set.Icc (0 : ℝ) T, IsUnit (F t) ∧ IsUnit (response (F t - B) B) ∧
      ∃ y : (F t - B).range, y ≠ 0 ∧ ‖response (F t - B) B y‖ < δ * ‖y‖ := by
  by_contra hn
  push Not at hn
  have hK : ∀ t ∈ Set.Icc (0 : ℝ) T, IsUnit (F t) →
      ∀ y : (F t - B).range, δ * ‖y‖ ≤ ‖response (F t - B) B y‖ := by
    intro t ht hu y
    have hKu : IsUnit (response (F t - B) B) :=
      (unit_add_iff_response (F t - B) B hB).mp (by simpa only [add_sub_cancel_left] using hu)
    by_cases hy : y = 0
    · simp [hy]
    · exact hn t ht hu hKu y hy
  obtain ⟨T', hb⟩ := isCompact_Icc.bddAbove_image
    (show ContinuousOn (fun t => ‖F t - B‖) (Set.Icc (0 : ℝ) T) by fun_prop)
  let C := ‖Ring.inverse B‖
  let H := δ * C + C * max T' 0 * C + 1
  have hH : 0 < H := by dsimp [H, C]; positivity
  have hg : 0 < δ / H := div_pos hδ hH
  obtain ⟨t, ht, hu, x, hx, hsmall⟩ := interval_guard_small_gain F hF hT h0 hbad (δ / H) hg
  have hb' : ‖F t - B‖ ≤ max T' 0 := (hb (Set.mem_image_of_mem _ ht)).trans (le_max_left _ _)
  have hc := response_gain_controls_carrier (F t) B hB hδ hb' (hK t ht hu) x
  have hh : H * ‖F t x‖ < δ * ‖x‖ := by
    have := mul_lt_mul_of_pos_left hsmall hH
    simpa only [mul_assoc, mul_div_cancel₀ _ hH.ne', ← mul_assoc] using this
  have hnn : 0 ≤ ‖F t x‖ := norm_nonneg _
  change δ * ‖x‖ ≤ (H - 1) * ‖F t x‖ at hc
  nlinarith

end Algebra

/-- The ordinary operator-norm bound extracted from the actual localized
weighted form estimate. No depth factor is lost in this direction. -/
theorem local_delta_norm_of_strat (P : IngrBParams) (hell : 0 < P.ell)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hq : ∀ x : ↥(bondSupp P.G), |⟪x, P.data.Delta2 P.data_laws x⟫| ≤
      ε * AdalyFormal.M1.wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf)) :
    ‖P.data.Delta2 P.data_laws‖ ≤ ε := by
  apply norm_le_of_quadratic _ hε (P.data.Delta2_spec P.data_laws).1
  intro x
  exact (hq x).trans (mul_le_mul_of_nonneg_left
    (AdalyFormal.M1W2.wnorm_le_sq P.S P.ell P.k hell (x : BondFnL2 P.Lf)) hε)

/-- Linear dependence in the smallness parameter from the genuine source,
raw-jet and Wop bounds. These analytic premises are NOT the carrier guard. -/
theorem local_delta_norm_linear (P : IngrBParams) (hell : 0 < P.ell)
    (t Cψ K2 CW : ℝ) (ht : 0 ≤ t) (hψ0 : 0 ≤ Cψ) (hK2 : 0 ≤ K2) (hCW : 0 ≤ CW)
    (hψ : ∀ p, ‖AdalyFormal.DLayer.psiD P p‖ ≤ Cψ * t)
    (hC : ∀ z : BondFnL2 P.Lf, ∑ p, ‖C2fullOf P.G P.U z p‖ ≤
      K2 * AdalyFormal.M1.wnormSq P.S P.ell P.k z)
    (hW : ∀ x : ↥(bondSupp P.G),
      AdalyFormal.M1.wnormSq P.S P.ell P.k (Wop P.G P.U P.a (iE P.G x)) ≤
        CW * AdalyFormal.M1.wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf)) :
    ‖P.data.Delta2 P.data_laws‖ ≤ (2 * Cψ * K2 * CW) * t := by
  apply local_delta_norm_of_strat P hell (by positivity)
  intro x
  convert AdalyFormal.M1DStrat.delta2_strat P (Cψ * t) K2 CW
    (mul_nonneg hψ0 ht) hK2 hψ hC hW x using 1
  ring

/-- Concrete pencil stability given an actual quantitative gain. This is not
a proof that such a gain is uniform on the guarded class. -/
theorem pencil_unit_of_gain (P : IngrBParams) {δ ε : ℝ} (hδ : 0 < δ)
    (hA : ∀ x, δ * ‖x‖ ≤ ‖(dataS selAll selAll P).Ginv x‖)
    (hD : ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ ≤ ε)
    (he : ε < δ) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) :=
  unit_sub_of_gain _ _ hδ hA (hD.trans_lt he)

/-- For the actual exterior-twist path, the guard has no uniform gain as soon
as its initial flat carrier is a unit. The correction on this path is zero,
so this is an obstruction to the proposed proof method, NOT a refutation. -/
theorem actual_twist_guard_small_gain
    {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    {z : PeriodicLatticeSite (scaleUp ell k Lu)} (hbd : AdalyFormal.D1Literal.BdPt (S.Om 0) z)
    (ha : 0 ≤ a) (ha4 : a < 4)
    (h0 : IsUnit (dataS selAll selAll
      (gparams ell k Lu hell0 S (AdalyFormal.D1Literal.Uth (S.Om 0) 0) a Lam)).Ginv)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      IsUnit (dataS selAll selAll
        (gparams ell k Lu hell0 S (AdalyFormal.D1Literal.Uth (S.Om 0) θ) a Lam)).Ginv ∧
      ∃ x : ↥(bondSupp (geomOf ell k S)), x ≠ 0 ∧
        ‖(dataS selAll selAll
          (gparams ell k Lu hell0 S (AdalyFormal.D1Literal.Uth (S.Om 0) θ) a Lam)).Ginv x‖ < δ * ‖x‖ := by
  obtain ⟨T, hT0, hTpi, hbad⟩ := AdalyFormal.D1Literal.exists_nonunit_Ginv
    selAll hell0 a Lam hS hell hroom hbd ha ha4
  obtain ⟨θ, hθ, hu, x, hx, hg⟩ := interval_guard_small_gain
    (AdalyFormal.D1Literal.Fth selAll ell k Lu hell0 S a Lam)
    (AdalyFormal.D1Literal.Fth_cont selAll hell0 a Lam hS hell hroom)
    hT0 h0 hbad δ hδ
  exact ⟨θ, ⟨hθ.1, hθ.2.trans hTpi.le⟩, hu, x, hx, hg⟩

#print axioms unit_add_iff_response
#print axioms response_gain_controls_carrier
#print axioms interval_guard_small_response
#print axioms unit_of_kernel_zero
#print axioms unit_of_gain
#print axioms norm_le_of_quadratic
#print axioms gain_of_unit
#print axioms unit_sub_of_gain
#print axioms compact_units_inverse_bound
#print axioms connected_guard_small_gain
#print axioms interval_guard_small_gain
#print axioms local_delta_norm_of_strat
#print axioms local_delta_norm_linear
#print axioms pencil_unit_of_gain
#print axioms actual_twist_guard_small_gain

end AdalyFormal.Round4.Guarded.PerturbR1
