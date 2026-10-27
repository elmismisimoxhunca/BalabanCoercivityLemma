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

/-! An exact two-coordinate diagnostic. These are matrices, not replacements
for any pinned lattice operator and not a negative certificate. -/
namespace AdalyFormal.Round4.Guarded.DecayR2.Diagnostic

noncomputable def bulk (t d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, t; t, 1 + d]
noncomputable def correction (d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, d]
noncomputable def shift (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![t ^ 2 - 1, 0; 0, 0]
noncomputable def greenColumn (t d : ℝ) : Fin 2 → ℝ :=
  ![(1 + d) / (1 + d - t ^ 2), -t / (1 + d - t ^ 2)]
noncomputable def responseCoefficient (t d : ℝ) : ℝ := t ^ 2 * d / (1 + d - t ^ 2)

/-- D and Theta have exactly disjoint coordinate supports. -/
theorem disjoint_support (t d : ℝ) :
    shift t * correction d = 0 ∧ correction d * shift t = 0 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [shift, correction, Matrix.mul_apply, Fin.sum_univ_two]

/-- Both localized operators have a fixed positive Euclidean energy gap,
even while their coupling t and the correction d tend to zero. -/
theorem uniform_local_gaps {t d : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) (hd : 0 ≤ d)
    (x y : ℝ) :
    (1 / 2 : ℝ) * (x ^ 2 + y ^ 2) ≤ x ^ 2 + 2 * t * x * y + (1 + d) * y ^ 2 ∧
    (1 / 2 : ℝ) * (x ^ 2 + y ^ 2) ≤ x ^ 2 + 2 * t * x * y + y ^ 2 := by
  have h1 := mul_nonneg ht (sq_nonneg (x + y))
  have h2 := mul_nonneg (show 0 ≤ (1 / 2 : ℝ) - t by linarith)
    (add_nonneg (sq_nonneg x) (sq_nonneg y))
  have h3 := mul_nonneg hd (sq_nonneg y)
  constructor <;> nlinarith

/-- Localized positivity and exact support separation do not force a
positive all-carrier gap. The uncorrected all-carrier is nevertheless a unit. -/
theorem guarded_separation {t d : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 4) (hd : 0 < d) :
    IsUnit (bulk t d) ∧ IsUnit (bulk t d - correction d) ∧
    IsUnit (bulk t d + shift t) ∧ ¬ IsUnit (bulk t d + shift t - correction d) := by
  have htc : 0 < 1 - t ^ 2 := by nlinarith
  have htb : 0 < 1 + d - t ^ 2 := by linarith
  have hta : 0 < t ^ 2 * d := mul_pos (sq_pos_of_pos ht) hd
  have hB : (bulk t d).det = 1 + d - t ^ 2 := by
    simp [bulk, Matrix.det_fin_two]; ring
  have hC : (bulk t d - correction d).det = 1 - t ^ 2 := by
    simp [bulk, correction, Matrix.det_fin_two]; ring
  have hA : (bulk t d + shift t).det = t ^ 2 * d := by
    simp [bulk, shift, Matrix.det_fin_two]; ring
  have hAC : (bulk t d + shift t - correction d).det = 0 := by
    simp [bulk, shift, correction, Matrix.det_fin_two]; ring
  simp only [Matrix.isUnit_iff_isUnit_det, hB, hC, hA, hAC, isUnit_iff_ne_zero]
  exact ⟨htb.ne', htc.ne', hta.ne', not_not.mpr rfl⟩

/-- These are actual inverse images of the boundary basis vector, not
surrogate decay parameters. Uniqueness follows from the preceding units. -/
theorem green_columns {t d : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) (hd : 0 ≤ d) :
    (bulk t d).mulVec (greenColumn t d) = ![1, 0] ∧
    (bulk t d - correction d).mulVec (greenColumn t 0) = ![1, 0] := by
  have htb : 1 + d - t ^ 2 ≠ 0 := by nlinarith
  have htc : 1 - t ^ 2 ≠ 0 := by nlinarith
  constructor <;> ext i <;> fin_cases i <;>
    simp [bulk, correction, greenColumn, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    field_simp [htb, htc] <;> nlinarith

/-- Their interior coordinates decay linearly with the boundary-to-interior
coupling. t can in particular be chosen exponentially small. -/
theorem inverse_input_decay {t d : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) (hd : 0 ≤ d) :
    |greenColumn t d 1| ≤ 2 * t ∧ |greenColumn t 0 1| ≤ 2 * t := by
  have htb : 0 < 1 + d - t ^ 2 := by nlinarith
  have htc : 0 < 1 - t ^ 2 := by nlinarith
  simp only [greenColumn, Matrix.cons_val_one, Matrix.cons_val_zero, add_zero,
    abs_div, abs_neg, abs_of_nonneg ht, abs_of_pos htb, abs_of_pos htc]
  constructor
  · apply (div_le_iff₀ htb).mpr
    have h := mul_nonneg ht (show 0 ≤ 2 * (1 + d - t ^ 2) - 1 by nlinarith)
    nlinarith
  · apply (div_le_iff₀ htc).mpr
    have h := mul_nonneg ht (show 0 ≤ 2 * (1 - t ^ 2) - 1 by nlinarith)
    nlinarith

/-- K_B is a small nonzero scalar on the first axis while K_C is exactly zero. -/
theorem boundary_responses {t d : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) (hd : 0 ≤ d) :
    (![1, 0] + (shift t).mulVec (greenColumn t d) : Fin 2 → ℝ) =
        ![responseCoefficient t d, 0] ∧
    (![1, 0] + (shift t).mulVec (greenColumn t 0) : Fin 2 → ℝ) = 0 := by
  have htb : 1 + d - t ^ 2 ≠ 0 := by nlinarith
  have htc : 1 - t ^ 2 ≠ 0 := by nlinarith
  constructor <;> ext i <;> fin_cases i <;>
    simp [shift, greenColumn, responseCoefficient, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    field_simp [htb, htc] <;> nlinarith

/-- Arbitrarily small absolute return has inverse-relative size exactly one. -/
theorem relative_not_small {t d : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 4) (hd : 0 < d) :
    0 < responseCoefficient t d ∧ responseCoefficient t d ≤ 2 * t ^ 2 * d ∧
    |(responseCoefficient t d)⁻¹ * (0 - responseCoefficient t d)| = 1 := by
  have hden : 0 < 1 + d - t ^ 2 := by nlinarith
  have hpos : 0 < responseCoefficient t d :=
    div_pos (mul_pos (sq_pos_of_pos ht) hd) hden
  refine ⟨hpos, ?_, ?_⟩
  · apply (div_le_iff₀ hden).mpr
    have h := mul_nonneg (mul_nonneg (sq_nonneg t) hd.le)
      (show 0 ≤ 2 * (1 + d - t ^ 2) - 1 by nlinarith)
    dsimp [responseCoefficient]
    nlinarith
  · rw [zero_sub, mul_neg, inv_mul_cancel₀ hpos.ne', abs_neg, abs_one]

/-- The correction-visible all-carrier transfer grows reciprocally. Its
product with the correction and the exact C inverse input is exactly one. -/
theorem observed_amplification {t d : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 4) (hd : 0 < d) :
    (bulk t d + shift t).mulVec
      ![(t ^ 2 - 1) * (1 + d) / (t ^ 2 * d), (1 - t ^ 2) / (t * d)] =
        (shift t).mulVec ![1, 0] ∧
    ((1 - t ^ 2) / (t * d)) * d * (t / (1 - t ^ 2)) = 1 := by
  have htc : 1 - t ^ 2 ≠ 0 := by nlinarith
  constructor
  · ext i; fin_cases i <;>
      simp [bulk, shift, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      field_simp [ht.ne', hd.ne'] <;> ring
  · field_simp [ht.ne', hd.ne', htc]

/-- Any prescribed positive correction cap and positive transmission bound
permit the diagnostic separation. This is not the lattice cofinal quantifier. -/
theorem arbitrarily_small_separated_model (cap transmission : ℝ)
    (hcap : 0 < cap) (htrans : 0 < transmission) :
    ∃ t d : ℝ, 0 < t ∧ t ≤ 1 / 4 ∧ t < transmission ∧
      0 < d ∧ d ≤ 1 / 4 ∧ d < cap ∧
      shift t * correction d = 0 ∧ correction d * shift t = 0 ∧
      IsUnit (bulk t d) ∧ IsUnit (bulk t d - correction d) ∧
      IsUnit (bulk t d + shift t) ∧ ¬ IsUnit (bulk t d + shift t - correction d) ∧
      |greenColumn t d 1| ≤ 2 * t ∧ |greenColumn t 0 1| ≤ 2 * t ∧
      |(responseCoefficient t d)⁻¹ * (0 - responseCoefficient t d)| = 1 := by
  let t := min (transmission / 2) (1 / 4)
  let d := min (cap / 2) (1 / 4)
  have ht : 0 < t := lt_min (half_pos htrans) (by norm_num)
  have hd : 0 < d := lt_min (half_pos hcap) (by norm_num)
  have ht' : t ≤ 1 / 4 := min_le_right _ _
  have hd' : d ≤ 1 / 4 := min_le_right _ _
  have hsep := guarded_separation ht ht' hd
  have hdis := disjoint_support t d
  have hdec := inverse_input_decay ht.le ht' hd.le
  exact ⟨t, d, ht, ht', (min_le_left _ _).trans_lt (half_lt_self htrans),
    hd, hd', (min_le_left _ _).trans_lt (half_lt_self hcap), hdis.1, hdis.2,
    hsep.1, hsep.2.1, hsep.2.2.1, hsep.2.2.2, hdec.1, hdec.2,
    (relative_not_small ht ht' hd).2.2⟩

#print axioms bulk
#print axioms correction
#print axioms shift
#print axioms greenColumn
#print axioms responseCoefficient
#print axioms disjoint_support
#print axioms uniform_local_gaps
#print axioms guarded_separation
#print axioms green_columns
#print axioms inverse_input_decay
#print axioms boundary_responses
#print axioms relative_not_small
#print axioms observed_amplification
#print axioms arbitrarily_small_separated_model
end AdalyFormal.Round4.Guarded.DecayR2.Diagnostic
