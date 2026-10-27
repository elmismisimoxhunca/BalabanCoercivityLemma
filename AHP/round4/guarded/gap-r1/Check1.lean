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
Round 4, gap route, pass 1. The pin above is unchanged.
The estimates below retain a separate boundary-shift lower-bound premise.
No estimate for that shift is inferred from a localized carrier unit.
-/
namespace AdalyFormal.Round4.Guarded.GapR1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round2.Guarded.R2Prove
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M1 (wnormSq)

/-- The weighted upper bound has no depth-dependent loss. -/
theorem weighted_norm_le {L : PeriodicLatticeExtent} (S : Tower L)
    {ell : ℕ} (hell : 1 ≤ ell) (k : ℕ) (x : BondFnL2 L) :
    wnormSq S ell k x ≤ ‖x‖ ^ 2 := by
  unfold wnormSq
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro b _
  have he : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hp : (1 : ℝ) ≤ (ell : ℝ) ^ bstrat S k b := one_le_pow₀ he
  have hi : ((ell : ℝ) ^ bstrat S k b)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp
  have hi0 : 0 ≤ ((ell : ℝ) ^ bstrat S k b)⁻¹ := by positivity
  have hs : (((ell : ℝ) ^ bstrat S k b)⁻¹) ^ 2 ≤ 1 := by nlinarith
  simpa using mul_le_mul_of_nonneg_right hs (sq_nonneg ‖(WithLp.ofLp x) b‖)

/-- The lower ordinary-norm comparison does retain the depth factor. -/
theorem weighted_norm_pos (P : IngrBParams) (hell : 1 ≤ P.ell)
    (x : ↥(bondSupp P.G)) (hx : x ≠ 0) :
    0 < wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf) := by
  have hl := AdalyFormal.M1IMS.wnormSq_ge P.S hell P.k (x : BondFnL2 P.Lf)
  have he : (0 : ℝ) < P.ell := by exact_mod_cast (show 0 < P.ell by omega)
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hp : 0 < ((P.ell : ℝ) ^ P.k)⁻¹ ^ 2 * ‖x‖ ^ 2 := by positivity
  exact lt_of_lt_of_le hp hl

/-- A genuine localized weighted D-layer estimate implies an ordinary operator
norm estimate, without losing a factor depending on depth. -/
theorem delta2_norm_le_weighted (P : IngrBParams) (hell : 1 ≤ P.ell)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hD : ∀ x : ↥(bondSupp P.G),
      |⟪x, (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x⟫| ≤
        ε * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf)) :
    ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ ≤ ε := by
  apply AdalyFormal.DLayer.opNorm_le_of_symm_form _
    ((dataS selIn selIn P).Delta2_spec (dataS_laws selIn selIn P)).1 hε
  intro x
  exact (hD x).trans (mul_le_mul_of_nonneg_left
    (weighted_norm_le P.S hell P.k (x : BondFnL2 P.Lf)) hε)

/-- The source supplies linear smallness. The raw second jet is bounded in its
input; no quadratic small-background estimate is used. -/
theorem delta2_norm_le_source (P : IngrBParams) (hell : 1 ≤ P.ell)
    (L t K2 CW : ℝ) (hL : 0 ≤ L) (ht : 0 ≤ t) (hK : 0 ≤ K2) (hCW : 0 ≤ CW)
    (hψ : ∀ p, ‖AdalyFormal.DLayer.psiD P p‖ ≤ L * t)
    (hC : ∀ z : BondFnL2 P.Lf, ∑ p, ‖C2fullOf P.G P.U z p‖ ≤
      K2 * wnormSq P.S P.ell P.k z)
    (hW : ∀ x : ↥(bondSupp P.G),
      wnormSq P.S P.ell P.k (Wop P.G P.U P.a (iE P.G x)) ≤
        CW * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf)) :
    ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ ≤
      (2 * L * K2 * CW) * t := by
  apply delta2_norm_le_weighted P hell (by positivity)
  intro x
  have h := AdalyFormal.M1DStrat.delta2_strat P (L * t) K2 CW
    (mul_nonneg hL ht) hK hψ hC hW x
  change |⟪x, P.data.Delta2 P.data_laws x⟫| ≤ _
  convert h using 1 <;> ring

/-- A cap may be chosen before every source satisfying the displayed bound.
The column, jet and Wop hypotheses still have to be supplied on the class. -/
theorem correction_cap (L K2 CW ε : ℝ)
    (hL : 0 ≤ L) (hK : 0 ≤ K2) (hCW : 0 ≤ CW) (hε : 0 < ε) :
    ∃ cap : ℝ, 0 < cap ∧ ∀ (P : IngrBParams), 1 ≤ P.ell →
      ∀ t : ℝ, 0 ≤ t → t ≤ cap →
      (∀ p, ‖AdalyFormal.DLayer.psiD P p‖ ≤ L * t) →
      (∀ z : BondFnL2 P.Lf, ∑ p, ‖C2fullOf P.G P.U z p‖ ≤
        K2 * wnormSq P.S P.ell P.k z) →
      (∀ x : ↥(bondSupp P.G),
        wnormSq P.S P.ell P.k (Wop P.G P.U P.a (iE P.G x)) ≤
          CW * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf)) →
      ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ < ε := by
  let H := 2 * L * K2 * CW
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨ε / (2 * (H + 1)), by positivity, ?_⟩
  intro P hell t ht hcap hψ hC hW
  have hb := delta2_norm_le_source P hell L t K2 CW hL ht hK hCW hψ hC hW
  have hc : (2 * (H + 1)) * t ≤ ε := by
    have h := (le_div_iff₀ (by positivity)).mp hcap
    nlinarith
  have hs : H * t < ε := by nlinarith
  exact hb.trans_lt hs

/-- Exact accounting of the one term not estimated by the localized chain. -/
theorem pencil_weighted_lower (P : IngrBParams) (cw ε β : ℝ)
    (hB : ∀ x : ↥(bondSupp P.G),
      cw * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf) ≤
        ⟪x, (dataS selIn selIn P).Ginv x⟫)
    (hD : ∀ x : ↥(bondSupp P.G),
      |⟪x, (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x⟫| ≤
        ε * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf))
    (hΘ : ∀ x : ↥(bondSupp P.G),
      -(β * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf)) ≤
        ⟪x, boundaryShift P x⟫)
    (x : ↥(bondSupp P.G)) :
    (cw - ε - β) * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf) ≤
      ⟪x, ((dataS selAll selAll P).Ginv -
        (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) x⟫ := by
  have hb := hB x
  have hd := (abs_le.mp (hD x)).2
  have ht := hΘ x
  simp only [boundaryShift, ContinuousLinearMap.sub_apply, inner_sub_right] at ht ⊢
  nlinarith

/-- Sufficient weighted gap criterion on the actual pinned operators. Its
boundary-shift premise is NOT a consequence proved from Total here. -/
theorem pencil_isUnit_of_weighted_boundary_gap (P : IngrBParams) (hell : 1 ≤ P.ell)
    (cw ε β : ℝ) (hgap : ε + β < cw)
    (hB : ∀ x : ↥(bondSupp P.G),
      cw * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf) ≤
        ⟪x, (dataS selIn selIn P).Ginv x⟫)
    (hD : ∀ x : ↥(bondSupp P.G),
      |⟪x, (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x⟫| ≤
        ε * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf))
    (hΘ : ∀ x : ↥(bondSupp P.G),
      -(β * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf)) ≤
        ⟪x, boundaryShift P x⟫) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) := by
  have he : (0 : ℝ) < P.ell := by exact_mod_cast (show 0 < P.ell by omega)
  have hc : 0 < cw - ε - β := by linarith
  apply AdalyFormal.DLayer.coercive_isUnit _
    (show 0 < (cw - ε - β) * ((P.ell : ℝ) ^ P.k)⁻¹ ^ 2 by positivity)
  intro x
  have hl := AdalyFormal.M1IMS.wnormSq_ge P.S hell P.k (x : BondFnL2 P.Lf)
  have hm := mul_le_mul_of_nonneg_left hl hc.le
  have hp := pencil_weighted_lower P cw ε β hB hD hΘ x
  calc
    ((cw - ε - β) * ((P.ell : ℝ) ^ P.k)⁻¹ ^ 2) * ‖x‖ ^ 2 =
        (cw - ε - β) * (((P.ell : ℝ) ^ P.k)⁻¹ ^ 2 * ‖x‖ ^ 2) := by ring
    _ ≤ (cw - ε - β) * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf) := hm
    _ ≤ _ := hp

/-- A corrected singularity, despite a localized weighted gap, must cancel that
gap by a strictly negative energy of the actual boundary shift. -/
theorem pencil_failure_forces_negative_boundary_energy
    (P : IngrBParams) (hell : 1 ≤ P.ell) (cw ε : ℝ) (hgap : ε < cw)
    (hB : ∀ x : ↥(bondSupp P.G),
      cw * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf) ≤
        ⟪x, (dataS selIn selIn P).Ginv x⟫)
    (hD : ∀ x : ↥(bondSupp P.G),
      |⟪x, (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x⟫| ≤
        ε * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf))
    (hbad : ¬ IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))) :
    ∃ x : ↥(bondSupp P.G), x ≠ 0 ∧
      ((dataS selAll selAll P).Ginv -
        (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) x = 0 ∧
      ⟪x, boundaryShift P x⟫ ≤
        -((cw - ε) * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf)) ∧
      ⟪x, boundaryShift P x⟫ < 0 := by
  let T := (dataS selAll selAll P).Ginv -
    (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
  have hn : ¬ Function.Injective T := by
    intro hi
    apply hbad
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hi, (LinearMap.injective_iff_surjective (f := T.toLinearMap)).mp hi⟩
  rw [injective_iff_map_eq_zero] at hn
  push_neg at hn
  obtain ⟨x, hx, hne⟩ := hn
  have hz : ⟪x, (dataS selAll selAll P).Ginv x⟫ -
      ⟪x, (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x⟫ = 0 := by
    have h := congrArg (fun y => ⟪x, y⟫) hx
    simpa only [T, ContinuousLinearMap.sub_apply, inner_sub_right, inner_zero_right] using h
  have hb := hB x
  have hd := (abs_le.mp (hD x)).2
  have ht : ⟪x, boundaryShift P x⟫ ≤
      -((cw - ε) * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf)) := by
    simp only [boundaryShift, ContinuousLinearMap.sub_apply, inner_sub_right]
    nlinarith
  refine ⟨x, hne, hx, ht, ?_⟩
  have hw := weighted_norm_pos P hell x hne
  have hp : 0 < (cw - ε) * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf) :=
    mul_pos (sub_pos.mpr hgap) hw
  linarith

/-- A scalar diagnostic, not a lattice configuration and not a pinned negative
answer. Even B=1 and C≥3/4 do not give a response gap from the carrier guard.
The scalar responses are exactly the displayed 1+Theta/B and 1+Theta/C. -/
theorem scalar_gap_obstruction (cap : ℝ) (hcap : 0 < cap) :
    ∃ (B D Θ : ℝ), B = 1 ∧ 0 < D ∧ |D| < cap ∧ 3 / 4 ≤ B - D ∧
      Θ ≠ 0 ∧ IsUnit B ∧ IsUnit (B - D) ∧ IsUnit (B + Θ) ∧
      ¬ IsUnit (B + Θ - D) ∧
      0 < |1 + Θ / B| ∧ |1 + Θ / B| < cap ∧ 1 + Θ / (B - D) = 0 := by
  let d := min (cap / 2) (1 / 4)
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have hdq : d ≤ 1 / 4 := min_le_right _ _
  have hdc : d < cap := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hc : 0 < 1 - d := by linarith
  refine ⟨1, d, d - 1, rfl, hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [abs_of_pos hd]
  · linarith
  · linarith
  · exact isUnit_one
  · exact isUnit_iff_ne_zero.mpr hc.ne'
  · apply isUnit_iff_ne_zero.mpr
    linarith
  · have hz : (1 : ℝ) + (d - 1) - d = 0 := by ring
    rw [hz]
    exact not_isUnit_zero
  · simpa [abs_of_pos hd] using hd
  · simpa [abs_of_pos hd] using hdc
  · field_simp
    ring

#print axioms weighted_norm_le
#print axioms weighted_norm_pos
#print axioms delta2_norm_le_weighted
#print axioms delta2_norm_le_source
#print axioms correction_cap
#print axioms pencil_weighted_lower
#print axioms pencil_isUnit_of_weighted_boundary_gap
#print axioms pencil_failure_forces_negative_boundary_energy
#print axioms scalar_gap_obstruction

end AdalyFormal.Round4.Guarded.GapR1
