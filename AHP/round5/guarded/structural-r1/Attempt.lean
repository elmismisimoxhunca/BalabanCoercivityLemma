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

/-! Round 4, decay route. Reused helpers retain their exact definitions. -/
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

namespace AdalyFormal.Round3.Guarded.R2Prove

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

section Algebra
variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Translation invisibility for the genuine quadratic jet kills the full
correction vector, not just its diagonal pairing. -/
theorem correction_kills_of_jet_translation (D : BaseDataS E S F) (hL : D.Laws)
    (x : E) (hjet : ∀ z : E, D.C2 (z + x) = D.C2 z) :
    D.Delta2 hL x = 0 := by
  obtain ⟨hs, hf⟩ := D.Delta2_spec hL
  have hx := hf x
  have hz := hf 0
  have hcx : D.C2 x = D.C2 0 := by simpa only [zero_add] using hjet 0
  rw [hcx] at hx
  have hdiag : ⟪x, D.Delta2 hL x⟫ = 0 := by
    simpa only [inner_zero_left] using hx.trans hz.symm
  apply ext_inner_left ℝ
  intro z
  have hsum := hf (z + x)
  rw [hjet z, ← hf z] at hsum
  have hsym : ⟪x, D.Delta2 hL z⟫ = ⟪z, D.Delta2 hL x⟫ := by
    rw [real_inner_comm, hs]
  simp only [map_add, inner_add_left, inner_add_right, hsym, hdiag] at hsum
  rw [inner_zero_right]
  linarith

end Algebra

section Concrete
variable (P : IngrBParams)

/-- Fields invisible on each positive-level raw-jet input ball. The balls use
rhoT, not all level-zero bonds, and the actual Wop remains in the definition. -/
def jetInputZero : Submodule ℝ ↥(bondSupp P.G) where
  carrier := {x | ∀ (j : Fin (P.k + 1)), 1 ≤ (j : ℕ) →
    ∀ (b : Bond P.Lf), b ∈ bondsLam P.G j →
    ∀ (e : Bond P.Lf), e.1 ∈ AdalyFormal.StatementLaneR8.Ball b.1
      (AdalyFormal.StatementLaneR8.rhoT P.ell j) →
      (Wop P.G P.U P.a (iE P.G x)) e = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j hj b hb e he
    simp [hx j hj b hb e he, hy j hj b hb e he]
  smul_mem' := by
    intro c x hx j hj b hb e he
    simp [hx j hj b hb e he]

/-- Same row proof as frozen C2fullOf_congr_in, but using its precise input
ball instead of enlarging it to all BothIn bonds. No geometry premise is needed. -/
theorem jet_translation_of_jetInputZero
    (x : ↥(bondSupp P.G)) (hx : x ∈ jetInputZero P) (z : ↥(bondSupp P.G)) :
    (dataS selIn selIn P).C2 (z + x) = (dataS selIn selIn P).C2 z := by
  change C2fullOf P.G P.U (Wop P.G P.U P.a (iE P.G (z + x))) =
    C2fullOf P.G P.U (Wop P.G P.U P.a (iE P.G z))
  refine PiLp.ext (fun p => ?_)
  obtain ⟨j, b, hb⟩ := p
  show (((P.ell : ℝ) ^ (j : ℕ))⁻¹) •
      (WithLp.ofLp (C2rawB P.G P.U j (Wop P.G P.U P.a (iE P.G (z + x))))) b =
    (((P.ell : ℝ) ^ (j : ℕ))⁻¹) •
      (WithLp.ofLp (C2rawB P.G P.U j (Wop P.G P.U P.a (iE P.G z)))) b
  congr 1
  rw [C2rawB_eq, C2rawB_eq]
  apply AdalyFormal.StatementLaneR8.suCoordInv_apply_congr
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hj1
  · rw [hj0, C2CompL_zero, C2CompL_zero]
  · apply AdalyFormal.StatementLaneR8.C2CompL_congr_in P.ell P.hell
    intro e he
    have heq : (Wop P.G P.U P.a (iE P.G (z + x))) e =
        (Wop P.G P.U P.a (iE P.G z)) e := by
      simp only [map_add, PiLp.add_apply, hx j hj1 b hb e he, add_zero]
    change fromM2 (((Wop P.G P.U P.a (iE P.G (z + x))) e :
      AdalyFormal.Balaban.SuTwoLogExp.M2)) =
      fromM2 (((Wop P.G P.U P.a (iE P.G z)) e :
      AdalyFormal.Balaban.SuTwoLogExp.M2))
    rw [heq]

theorem correction_kills_jetInputZero
    (x : ↥(bondSupp P.G)) (hx : x ∈ jetInputZero P) :
    (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x = 0 :=
  correction_kills_of_jet_translation _ _ x (jet_translation_of_jetInputZero P x hx)

end Concrete
#print axioms correction_kills_of_jet_translation
#print axioms jetInputZero
#print axioms jet_translation_of_jetInputZero
#print axioms correction_kills_jetInputZero
end AdalyFormal.Round3.Guarded.R2Prove


namespace AdalyFormal.Round4.Guarded.DecayR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round2.Guarded.R2Prove
open AdalyFormal.Round3.Guarded.R2Prove
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

end Algebra

section InversePairing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The inverse symmetry proof used inside frozen R2Algebra.isUnit_Q_inv_Qs. -/
theorem inverse_pairing (T : E →L[ℝ] E) (hT : IsUnit T)
    (hs : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (x y : E) :
    ⟪x, Ring.inverse T y⟫ = ⟪Ring.inverse T x, y⟫ := by
  have hl : ∀ v, T (Ring.inverse T v) = v := fun v =>
    congrArg (fun F : E →L[ℝ] E => F v) (Ring.mul_inverse_cancel T hT)
  have h := hs (Ring.inverse T x) (Ring.inverse T y)
  rw [hl, hl] at h
  exact h

end InversePairing
#print axioms relativeReturn
#print axioms kernel_iff_relative_neg
#print axioms unit_of_relative_norm_lt_one
#print axioms inverse_pairing

/-! Quantitative locality keeps the genuine dressed-jet nullspace. A collar
estimate is a bound for its observed inverse inputs, not finite propagation. -/
section DecayAlgebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Remove exactly the subspace on which the correction vanishes. -/
theorem map_eq_observed (D : E →L[ℝ] E) (N : Submodule ℝ E)
    (hN : ∀ x ∈ N, D x = 0) (x : E) :
    D x = D (Nᗮ.starProjection x) := by
  have hx : x - Nᗮ.starProjection x ∈ N := by
    simpa only [Submodule.orthogonal_orthogonal] using
      (Submodule.sub_starProjection_mem_orthogonal (K := Nᗮ) x)
  exact sub_eq_zero.mp (by simpa only [map_sub] using hN _ hx)

/-- Two observed inputs, not merely one, enter the symmetric correction. -/
theorem pair_eq_observed (D : E →L[ℝ] E) (N : Submodule ℝ E)
    (hN : ∀ x ∈ N, D x = 0)
    (hs : ∀ x y, ⟪D x, y⟫ = ⟪x, D y⟫) (x y : E) :
    ⟪x, D y⟫ = ⟪Nᗮ.starProjection x, D (Nᗮ.starProjection y)⟫ := by
  calc
    ⟪x, D y⟫ = ⟪D x, y⟫ := (hs x y).symm
    _ = ⟪D (Nᗮ.starProjection x), y⟫ := by rw [map_eq_observed D N hN x]
    _ = ⟪Nᗮ.starProjection x, D y⟫ := hs _ _
    _ = _ := by rw [map_eq_observed D N hN y]

omit [FiniteDimensional ℝ E] in
/-- The exact output of a weighted/coercive inverse argument. The weight
fixes boundary sources, and the observation costs exp(-distance). Neither
weighted coercivity nor observation separation is supplied by invertibility. -/
theorem weighted_inverse_observation (Θ B T J : E →L[ℝ] E)
    (hB : IsUnit B) {c d : ℝ} (hc : 0 < c)
    (hcoer : ∀ x, c * ‖T x‖ ^ 2 ≤ ⟪T x, T (B x)⟫)
    (hsource : ∀ y : Θ.range, T y = (y : E))
    (hobs : ∀ x, ‖J x‖ ≤ Real.exp (-d) * ‖T x‖)
    (y : Θ.range) :
    ‖J (Ring.inverse B y)‖ ≤ (Real.exp (-d) / c) * ‖y‖ := by
  let x := Ring.inverse B (y : E)
  have hx : B x = (y : E) :=
    congrArg (fun F : E →L[ℝ] E => F y) (Ring.mul_inverse_cancel B hB)
  have henergy := hcoer x
  rw [hx, hsource y] at henergy
  have hCS := real_inner_le_norm (T x) (y : E)
  change ⟪T x, (y : E)⟫ ≤ ‖T x‖ * ‖y‖ at hCS
  have hbound : c * ‖T x‖ ≤ ‖y‖ := by
    by_cases hz : ‖T x‖ = 0
    · rw [hz, mul_zero]; exact norm_nonneg _
    · have hpos : 0 < ‖T x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have hp : (c * ‖T x‖) * ‖T x‖ ≤ ‖y‖ * ‖T x‖ := by nlinarith
      exact le_of_mul_le_mul_right hp hpos
  calc
    ‖J x‖ ≤ Real.exp (-d) * ‖T x‖ := hobs x
    _ ≤ Real.exp (-d) * (‖y‖ / c) := by
      gcongr
      exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hbound)
    _ = (Real.exp (-d) / c) * ‖y‖ := by ring

/-- Exact two-pass bound. If both observed Green extensions decay once across
the collar, the absolute boundary return decays twice. -/
theorem response_sub_norm_le_two_pass (Θ B D : E →L[ℝ] E)
    (N : Submodule ℝ E) (hB : IsUnit B) (hC : IsUnit (B - D))
    (hΘ : ∀ x y, ⟪Θ x, y⟫ = ⟪x, Θ y⟫)
    (hCs : ∀ x y, ⟪(B - D) x, y⟫ = ⟪x, (B - D) y⟫)
    (hDs : ∀ x y, ⟪D x, y⟫ = ⟪x, D y⟫)
    (hN : ∀ x ∈ N, D x = 0)
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbt : ∀ y : Θ.range, ‖Nᗮ.starProjection (Ring.inverse B y)‖ ≤ b * ‖y‖)
    (hct : ∀ y : Θ.range, ‖Nᗮ.starProjection (Ring.inverse (B - D) y)‖ ≤ c * ‖y‖) :
    ‖response Θ (B - D) - response Θ B‖ ≤ ‖Θ‖ * ‖D‖ * b * c := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  change ‖(response Θ (B - D) y : E) - (response Θ B y : E)‖ ≤ _
  rw [response_sub_apply Θ B D hB hC y]
  let u := Ring.inverse B (y : E)
  let r := Θ (Ring.inverse (B - D) (D u))
  let z : Θ.range := ⟨Θ r, ⟨r, rfl⟩⟩
  have hz : ‖(z : E)‖ ≤ ‖Θ‖ * ‖r‖ := Θ.le_opNorm r
  have hpair : ‖r‖ ^ 2 =
      ⟪Nᗮ.starProjection (Ring.inverse (B - D) z), D (Nᗮ.starProjection u)⟫ := by
    calc
      ‖r‖ ^ 2 = ⟪r, r⟫ := (real_inner_self_eq_norm_sq r).symm
      _ = ⟪Θ r, Ring.inverse (B - D) (D u)⟫ := (hΘ _ _).symm
      _ = ⟪Ring.inverse (B - D) (Θ r), D u⟫ := inverse_pairing _ hC hCs _ _
      _ = _ := pair_eq_observed D N hN hDs _ _
  have he : ‖r‖ ^ 2 ≤ (‖Θ‖ * ‖D‖ * b * c) * ‖y‖ * ‖r‖ := by
    calc
      ‖r‖ ^ 2 ≤ ‖Nᗮ.starProjection (Ring.inverse (B - D) z)‖ *
          ‖D (Nᗮ.starProjection u)‖ := by
        rw [hpair]; exact real_inner_le_norm _ _
      _ ≤ (c * ‖z‖) * (‖D‖ * (b * ‖y‖)) := by
        gcongr
        · exact hct z
        · exact (D.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbt y) (norm_nonneg D))
      _ ≤ (c * (‖Θ‖ * ‖r‖)) * (‖D‖ * (b * ‖y‖)) := by
        gcongr
        exact hz
      _ = (‖Θ‖ * ‖D‖ * b * c) * ‖y‖ * ‖r‖ := by ring
  change ‖r‖ ≤ _
  by_cases hr : r = 0
  · rw [hr, norm_zero]; positivity
  · have hp : ‖r‖ * ‖r‖ ≤ (‖Θ‖ * ‖D‖ * b * c) * ‖y‖ * ‖r‖ := by nlinarith
    exact le_of_mul_le_mul_right hp (norm_pos_iff.mpr hr)

/-- Specialize before substituting the nested concrete carrier, so all
inherited Hilbert-space instances remain explicit to the elaborator. -/
theorem response_isUnit_of_absolute_small (Θ B C : E →L[ℝ] E)
    (hK : IsUnit (response Θ B)) {d : ℝ}
    (hbound : ‖response Θ C - response Θ B‖ ≤ d)
    (hsmall : ‖Ring.inverse (response Θ B)‖ * d < 1) :
    IsUnit (response Θ C) := by
  apply unit_of_relative_norm_lt_one _ _ hK
  apply lt_of_le_of_lt (ContinuousLinearMap.opNorm_comp_le _ _) _
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hbound (norm_nonneg _)) hsmall

end DecayAlgebra

section Concrete
variable (P : IngrBParams)

/-- This is the actual dressed-jet observation, not a raw plaquette mask. -/
noncomputable def jetObservation : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G) :=
  (jetInputZero P)ᗮ.starProjection

theorem boundaryShift_symmetric (x y : ↥(bondSupp P.G)) :
    ⟪boundaryShift P x, y⟫ = ⟪x, boundaryShift P y⟫ := by
  simp only [boundaryShift, sub_apply, inner_sub_left, inner_sub_right,
    (dataS selAll selAll P).Ginv_symm (dataS_laws selAll selAll P),
    (dataS selIn selIn P).Ginv_symm (dataS_laws selIn selIn P)]

theorem localCorrected_symmetric (x y : ↥(bondSupp P.G)) :
    ⟪localCorrected P x, y⟫ = ⟪x, localCorrected P y⟫ := by
  simp only [localCorrected, sub_apply, inner_sub_left, inner_sub_right,
    (dataS selIn selIn P).Ginv_symm (dataS_laws selIn selIn P),
    ((dataS selIn selIn P).Delta2_spec (dataS_laws selIn selIn P)).1]

/-- A new quantitative bound for the real pinned operators. All inverse
propagation assumptions are visible. No locality is inferred for an inverse. -/
theorem actual_return_norm_le_two_pass
    (hW : WellDefAt selIn selIn P) {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbt : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (dataS selIn selIn P).Ginv y)‖ ≤ b * ‖y‖)
    (hct : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖) :
    ‖response (boundaryShift P) (localCorrected P) -
      response (boundaryShift P) (dataS selIn selIn P).Ginv‖ ≤
        ‖boundaryShift P‖ *
          ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * b * c := by
  have hC : IsUnit (localCorrected P) := by
    rw [localCorrected_eq P]; exact hW.2.1
  exact response_sub_norm_le_two_pass _ _ _ (jetInputZero P) hW.1 hC
    (boundaryShift_symmetric P) (localCorrected_symmetric P)
    ((dataS selIn selIn P).Delta2_spec (dataS_laws selIn selIn P)).1
    (correction_kills_jetInputZero P) hb hc hbt hct

/-- The factor from the guarded inverse is indispensable in this route. -/
theorem pencil_isUnit_of_two_pass_decay
    (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbt : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (dataS selIn selIn P).Ginv y)‖ ≤ b * ‖y‖)
    (hct : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖)
    (hsmall : ‖Ring.inverse (response (boundaryShift P) (dataS selIn selIn P).Ginv)‖ *
      (‖boundaryShift P‖ *
        ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * b * c) < 1) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) := by
  apply (pencil_isUnit_iff_response P hW.2.1).mpr
  exact response_isUnit_of_absolute_small _ _ _ ((carrier_isUnit_iff_response P hW.1).mp hu)
    (actual_return_norm_le_two_pass P hW hb hc hbt hct) hsmall

/-- Combes--Thomas-style conditional route with an exponential for each pass.
The numerical gaps cB,cC are localized weighted gaps, not the carrier guard.
The displayed final smallness still requires an inverse-response bound. -/
theorem pencil_isUnit_of_weighted_decay
    (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (TB TC : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G))
    {cB cC dB dC : ℝ} (hcB : 0 < cB) (hcC : 0 < cC)
    (hcoerB : ∀ x, cB * ‖TB x‖ ^ 2 ≤ ⟪TB x, TB ((dataS selIn selIn P).Ginv x)⟫)
    (hcoerC : ∀ x, cC * ‖TC x‖ ^ 2 ≤ ⟪TC x, TC (localCorrected P x)⟫)
    (hsourceB : ∀ y : (boundaryShift P).range, TB y = (y : ↥(bondSupp P.G)))
    (hsourceC : ∀ y : (boundaryShift P).range, TC y = (y : ↥(bondSupp P.G)))
    (hobsB : ∀ x, ‖jetObservation P x‖ ≤ Real.exp (-dB) * ‖TB x‖)
    (hobsC : ∀ x, ‖jetObservation P x‖ ≤ Real.exp (-dC) * ‖TC x‖)
    (hsmall : ‖Ring.inverse (response (boundaryShift P) (dataS selIn selIn P).Ginv)‖ *
      (‖boundaryShift P‖ *
        ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ *
          (Real.exp (-dB) / cB) * (Real.exp (-dC) / cC)) < 1) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) := by
  have hC : IsUnit (localCorrected P) := by
    rw [localCorrected_eq P]; exact hW.2.1
  exact pencil_isUnit_of_two_pass_decay P hW hu (by positivity) (by positivity)
    (weighted_inverse_observation _ _ TB _ hW.1 hcB hcoerB hsourceB hobsB)
    (weighted_inverse_observation _ _ TC _ hC hcC hcoerC hsourceC hobsC) hsmall

/-- If decay holds but the guarded conclusion fails, the inverse boundary
response must amplify enough to cancel both decay factors. -/
theorem guarded_failure_requires_amplification
    (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (hbad : ¬ IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)))
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbt : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (dataS selIn selIn P).Ginv y)‖ ≤ b * ‖y‖)
    (hct : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖) :
    1 ≤ ‖Ring.inverse (response (boundaryShift P) (dataS selIn selIn P).Ginv)‖ *
      (‖boundaryShift P‖ *
        ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * b * c) := by
  by_contra hn
  exact hbad (pencil_isUnit_of_two_pass_decay P hW hu hb hc hbt hct (lt_of_not_ge hn))

end Concrete

/-- This is an explicit remaining obligation, not a replacement for a pin. -/
def CTwoPassSmall : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell)
    (_ : Tower (scaleUp ell k Lu))
    (_ : AdalyFormal.Balaban.CoercUMainDesigned.LinkCfg (scaleUp ell k Lu))
    (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop :=
  fun ell k Lu h S U a Lam =>
    let P := gparams ell k Lu h S U a Lam
    ∃ b c : ℝ, 0 ≤ b ∧ 0 ≤ c ∧
      (∀ y : (boundaryShift P).range,
        ‖jetObservation P (Ring.inverse (dataS selIn selIn P).Ginv y)‖ ≤ b * ‖y‖) ∧
      (∀ y : (boundaryShift P).range,
        ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖) ∧
      ‖Ring.inverse (response (boundaryShift P) (dataS selIn selIn P).Ginv)‖ *
        (‖boundaryShift P‖ *
          ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * b * c) < 1

/-- Conditional implication with every original eventual quantifier intact.
The premise GShape CTwoPassSmall is not proved in this attempt. -/
theorem goalPos2_of_two_pass_decay (h : GShape CTwoPassSmall) : GoalPos2 := by
  apply goalPos2_iff_goalPos1.mpr
  apply AdalyFormal.D1Residual.GShape_imp CTwoPassSmall AdalyFormal.D1Residual.CPen _ h
  intro ell k h0 M R Lu S U a Lam _ _ hW hu ht
  obtain ⟨b, c, hb, hc, hbt, hct, hsmall⟩ := ht
  exact pencil_isUnit_of_two_pass_decay (gparams ell k Lu h0 S U a Lam)
    hW hu hb hc hbt hct hsmall

#print axioms guarded_failure_requires_amplification
#print axioms CTwoPassSmall
#print axioms goalPos2_of_two_pass_decay
#print axioms map_eq_observed
#print axioms pair_eq_observed
#print axioms weighted_inverse_observation
#print axioms response_sub_norm_le_two_pass
#print axioms response_isUnit_of_absolute_small
#print axioms jetObservation
#print axioms boundaryShift_symmetric
#print axioms localCorrected_symmetric
#print axioms actual_return_norm_le_two_pass
#print axioms pencil_isUnit_of_two_pass_decay
#print axioms pencil_isUnit_of_weighted_decay

end AdalyFormal.Round4.Guarded.DecayR1


namespace AdalyFormal.Round4.Guarded.DecayR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round2.Guarded.R2Prove
open AdalyFormal.Round3.Guarded.R2Prove
open AdalyFormal.Round4.Guarded.DecayR1

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The relative return can be evaluated without taking an inverse on W.
The all-carrier inverse is used on the full carrier, not on a compression. -/
theorem relativeReturn_apply (Θ B D : E →L[ℝ] E)
    (hB : IsUnit B) (hC : IsUnit (B - D)) (hA : IsUnit (B + Θ))
    (y : Θ.range) :
    (relativeReturn Θ B (B - D) y : E) =
      Θ (Ring.inverse (B + Θ) (D (Ring.inverse (B - D) y))) := by
  let v := Ring.inverse (B - D) (y : E)
  let u := Ring.inverse (B + Θ) (D v)
  let q : Θ.range := ⟨Θ u, ⟨u, rfl⟩⟩
  have hv : (B - D) v = (y : E) :=
    congrArg (fun T : E →L[ℝ] E => T y) (Ring.mul_inverse_cancel (B - D) hC)
  have hu : (B + Θ) u = D v :=
    congrArg (fun T : E →L[ℝ] E => T (D v)) (Ring.mul_inverse_cancel (B + Θ) hA)
  have hi : ∀ x, Ring.inverse B (B x) = x := fun x =>
    congrArg (fun T : E →L[ℝ] E => T x) (Ring.inverse_mul_cancel B hB)
  have htheta : Θ u = D v - B u := by
    change B u + Θ u = D v at hu
    exact eq_sub_of_add_eq' hu
  have hd : D v = B v - (y : E) := by
    change B v - D v = (y : E) at hv
    calc
      D v = B v - (B v - D v) := by abel
      _ = _ := by rw [hv]
  have hBi : Ring.inverse B (Θ u) = v - Ring.inverse B (y : E) - u := by
    rw [htheta, map_sub, hi, hd, map_sub, hi]
  have hq : response Θ B q = (response Θ (B - D) - response Θ B) y := by
    apply Subtype.ext
    change Θ u + Θ (Ring.inverse B (Θ u)) =
      ((y : E) + Θ v) - ((y : E) + Θ (Ring.inverse B y))
    rw [hBi, map_sub, map_sub]
    abel
  have hK := (unit_add_iff_response Θ B hB).mp hA
  have hr : Ring.inverse (response Θ B) (response Θ B q) = q :=
    congrArg (fun T : Θ.range →L[ℝ] Θ.range => T q)
      (Ring.inverse_mul_cancel (response Θ B) hK)
  have heq : relativeReturn Θ B (B - D) y = q := by
    change Ring.inverse (response Θ B) ((response Θ (B - D) - response Θ B) y) = q
    rw [← hq, hr]
  exact congrArg (fun z : Θ.range => (z : E)) heq

/-- A source-specific bound avoids the crude product of the full inverse
response norm with the absolute return. Only the jet-observed all-carrier
Green response to Theta is required on the first pass. -/
theorem relativeReturn_norm_le_observed (Θ B D : E →L[ℝ] E)
    (N : Submodule ℝ E) (hB : IsUnit B) (hC : IsUnit (B - D))
    (hA : IsUnit (B + Θ))
    (hΘ : ∀ x y, ⟪Θ x, y⟫ = ⟪x, Θ y⟫)
    (hAs : ∀ x y, ⟪(B + Θ) x, y⟫ = ⟪x, (B + Θ) y⟫)
    (hDs : ∀ x y, ⟪D x, y⟫ = ⟪x, D y⟫)
    (hN : ∀ x ∈ N, D x = 0)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hat : ∀ x : E, ‖Nᗮ.starProjection (Ring.inverse (B + Θ) (Θ x))‖ ≤ a * ‖x‖)
    (hct : ∀ y : Θ.range, ‖Nᗮ.starProjection (Ring.inverse (B - D) y)‖ ≤ c * ‖y‖) :
    ‖relativeReturn Θ B (B - D)‖ ≤ a * ‖D‖ * c := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  change ‖(relativeReturn Θ B (B - D) y : E)‖ ≤ _
  rw [relativeReturn_apply Θ B D hB hC hA y]
  let u := Ring.inverse (B - D) (y : E)
  let r := Θ (Ring.inverse (B + Θ) (D u))
  have hpair : ‖r‖ ^ 2 =
      ⟪Nᗮ.starProjection (Ring.inverse (B + Θ) (Θ r)), D (Nᗮ.starProjection u)⟫ := by
    calc
      ‖r‖ ^ 2 = ⟪r, r⟫ := (real_inner_self_eq_norm_sq r).symm
      _ = ⟪Θ r, Ring.inverse (B + Θ) (D u)⟫ := (hΘ _ _).symm
      _ = ⟪Ring.inverse (B + Θ) (Θ r), D u⟫ := inverse_pairing _ hA hAs _ _
      _ = _ := pair_eq_observed D N hN hDs _ _
  have he : ‖r‖ ^ 2 ≤ (a * ‖D‖ * c) * ‖y‖ * ‖r‖ := by
    calc
      ‖r‖ ^ 2 ≤ ‖Nᗮ.starProjection (Ring.inverse (B + Θ) (Θ r))‖ *
          ‖D (Nᗮ.starProjection u)‖ := by
        rw [hpair]; exact real_inner_le_norm _ _
      _ ≤ (a * ‖r‖) * (‖D‖ * (c * ‖y‖)) := by
        gcongr
        · exact hat r
        · exact (D.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hct y) (norm_nonneg D))
      _ = (a * ‖D‖ * c) * ‖y‖ * ‖r‖ := by ring
  change ‖r‖ ≤ _
  by_cases hr : r = 0
  · rw [hr, norm_zero]; positivity
  · have hp : ‖r‖ * ‖r‖ ≤ (a * ‖D‖ * c) * ‖y‖ * ‖r‖ := by nlinarith
    exact le_of_mul_le_mul_right hp (norm_pos_iff.mpr hr)

/-- Specialize the Hilbert-space instances before the concrete nested carrier. -/
theorem response_unit_of_relative_small (Θ B C : E →L[ℝ] E)
    (hK : IsUnit (response Θ B))
    (hsmall : ‖relativeReturn Θ B C‖ < 1) : IsUnit (response Θ C) :=
  unit_of_relative_norm_lt_one _ _ hK hsmall

#print axioms response_unit_of_relative_small
end Algebra
section Concrete
variable (P : IngrBParams)

/-- Genuine correction-sensitive transfer. This need not grow with inverse
norms of modes invisible to the dressed jet. No bound is assumed by its definition. -/
noncomputable def observedGuardTransfer : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G) :=
  (jetObservation P).comp ((Ring.inverse (dataS selAll selAll P).Ginv).comp (boundaryShift P))

/-- Exact inverse-relative return for the unchanged lattice assembly. -/
theorem actual_relative_return_apply (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv) (y : (boundaryShift P).range) :
    (relativeReturn (boundaryShift P) (dataS selIn selIn P).Ginv (localCorrected P) y :
      ↥(bondSupp P.G)) =
      boundaryShift P (Ring.inverse (dataS selAll selAll P).Ginv
        ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
          (Ring.inverse (localCorrected P) y))) := by
  have hC : IsUnit (localCorrected P) := by
    rw [localCorrected_eq P]; exact hW.2.1
  simpa only [localCorrected, ← carrier_eq_local_add_shift P] using
    relativeReturn_apply (boundaryShift P) (dataS selIn selIn P).Ginv
      ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) hW.1 hC
      (by rwa [← carrier_eq_local_add_shift P]) y

/-- Main partial bound: the missing all-carrier control is now restricted to
what the actual nonlinear correction can observe, rather than the entire guard. -/
theorem actual_relative_return_norm_le_observed (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv) {c : ℝ} (hc : 0 ≤ c)
    (hct : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖) :
    ‖relativeReturn (boundaryShift P) (dataS selIn selIn P).Ginv (localCorrected P)‖ ≤
      ‖observedGuardTransfer P‖ *
        ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * c := by
  have hC : IsUnit (localCorrected P) := by
    rw [localCorrected_eq P]; exact hW.2.1
  exact relativeReturn_norm_le_observed (boundaryShift P) (dataS selIn selIn P).Ginv
    ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) (jetInputZero P) hW.1 hC
    (by rwa [← carrier_eq_local_add_shift P]) (boundaryShift_symmetric P)
    (fun x y => by
      rw [← carrier_eq_local_add_shift P]
      exact (dataS selAll selAll P).Ginv_symm (dataS_laws selAll selAll P) x y)
    ((dataS selIn selIn P).Delta2_spec (dataS_laws selIn selIn P)).1
    (correction_kills_jetInputZero P) (norm_nonneg (observedGuardTransfer P)) hc
    (fun x => by
      rw [← carrier_eq_local_add_shift P]
      exact (observedGuardTransfer P).le_opNorm x) hct

/-- A conditional criterion, not a new guard or a change to either pinned goal. -/
theorem pencil_isUnit_of_observed_guard_decay (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv) {c : ℝ} (hc : 0 ≤ c)
    (hct : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖)
    (hsmall : ‖observedGuardTransfer P‖ *
      ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * c < 1) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) := by
  apply (pencil_isUnit_iff_response P hW.2.1).mpr
  exact response_unit_of_relative_small _ _ _ ((carrier_isUnit_iff_response P hW.1).mp hu)
    ((actual_relative_return_norm_le_observed P hW hu hc hct).trans_lt hsmall)

/-- Failure forces amplification in the jet-visible guard transfer, not just
some unrelated small spectral mode of the full response. -/
theorem failure_requires_observed_amplification (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (hbad : ¬ IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)))
    {c : ℝ} (hc : 0 ≤ c)
    (hct : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖) :
    1 ≤ ‖observedGuardTransfer P‖ *
      ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * c := by
  by_contra hn
  exact hbad (pencil_isUnit_of_observed_guard_decay P hW hu hc hct (lt_of_not_ge hn))

end Concrete

/-- A new analytic obligation, kept separate from the unchanged headline. -/
def CObservedGuardSmall : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell)
    (_ : Tower (scaleUp ell k Lu))
    (_ : AdalyFormal.Balaban.CoercUMainDesigned.LinkCfg (scaleUp ell k Lu))
    (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop :=
  fun ell k Lu h S U a Lam =>
    let P := gparams ell k Lu h S U a Lam
    ∃ c : ℝ, 0 ≤ c ∧
      (∀ y : (boundaryShift P).range,
        ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖) ∧
      ‖observedGuardTransfer P‖ *
        ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * c < 1

/-- Conditional only: class-wide correction-sensitive decay would close the
original GoalPos2, with its radius/cap order and all other binders intact. -/
theorem goalPos2_of_observed_guard_decay (h : GShape CObservedGuardSmall) : GoalPos2 := by
  apply goalPos2_iff_goalPos1.mpr
  apply AdalyFormal.D1Residual.GShape_imp CObservedGuardSmall AdalyFormal.D1Residual.CPen _ h
  intro ell k h0 M R Lu S U a Lam _ _ hW hu ht
  obtain ⟨c, hc, hct, hsmall⟩ := ht
  exact pencil_isUnit_of_observed_guard_decay (gparams ell k Lu h0 S U a Lam)
    hW hu hc hct hsmall

#print axioms CObservedGuardSmall
#print axioms goalPos2_of_observed_guard_decay
#print axioms relativeReturn_apply
#print axioms relativeReturn_norm_le_observed
#print axioms observedGuardTransfer
#print axioms actual_relative_return_apply
#print axioms actual_relative_return_norm_le_observed
#print axioms pencil_isUnit_of_observed_guard_decay
#print axioms failure_requires_observed_amplification
end AdalyFormal.Round4.Guarded.DecayR2
