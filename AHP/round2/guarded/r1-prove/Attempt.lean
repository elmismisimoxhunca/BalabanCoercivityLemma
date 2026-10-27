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
Positive attempt: reuse the frozen agreement on V0 and the finite-dimensional
injectivity argument from GdGen4.unit_transfer. These results do not prove either
pinned positive goal. No class, operator, selector or target above is changed.
-/
namespace AdalyFormal.Round2.Guarded.R1Prove

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- Finite-dimensional endomorphism criterion, as used by frozen unit_transfer. -/
theorem unit_of_kernel_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (h : ∀ x, T x = 0 → x = 0) : IsUnit T := by
  have hinj : Function.Injective T := (injective_iff_map_eq_zero T).mpr h
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, (LinearMap.injective_iff_surjective
      (f := (show E →ₗ[ℝ] E from T))).mp hinj⟩

section Pointwise
variable (P : IngrBParams) {M R : ℕ}

/-- The actual pencil agrees with the localized corrected operator on V0.
This needs no literal unit premise, and no flatness. -/
theorem pencil_eq_local_on_V
    (hS : Admissible P.ell M R P.k P.S) (hell0 : 0 < P.ell)
    (hroom : 17 * P.ell ≤ R * M) (x : ↥(bondSupp P.G)) (hx : x ∈ V0 P.G) :
    ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) x =
        G1invS selIn selIn P x := by
  have hloc : G1invS selIn selIn P = (dataS selIn selIn P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) :=
    (dataS selIn selIn P).G1inv_unique
      (AdalyFormal.D1Literal.G1invS_spec selIn selIn P)
      ((dataS selIn selIn P).isG1inv_sub (dataS_laws selIn selIn P))
  have hA : (dataS selAll selAll P).Ginv x = (dataS selIn selIn P).Ginv x :=
    Ginv_eq_on_V P hS hell0 hroom selAll selAll selIn selIn
      (fun _ _ => Set.subset_univ _) (fun _ _ => Set.Subset.refl _) hx
  rw [hloc]
  exact congrArg (fun y => y - (dataS selIn selIn P).Delta2
    (dataS_laws selIn selIn P) x) hA

/-- A corrected null vector with zero level-zero trace is zero. -/
theorem pencil_kernel_in_V_zero
    (hS : Admissible P.ell M R P.k P.S) (hell0 : 0 < P.ell)
    (hroom : 17 * P.ell ≤ R * M)
    (hloc : IsUnit (G1invS selIn selIn P))
    (x : ↥(bondSupp P.G)) (hx : x ∈ V0 P.G)
    (hk : ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) x = 0) : x = 0 := by
  have hzero : G1invS selIn selIn P x = 0 := by
    rw [← pencil_eq_local_on_V P hS hell0 hroom x hx]
    exact hk
  exact (injective_iff_map_eq_zero (G1invS selIn selIn P)).mp
    (ContinuousLinearMap.isUnit_iff_bijective.mp hloc).1 x hzero

/-- This is the exact missing kernel-location premise, not a proof of it. -/
theorem pencil_isUnit_of_kernel_mem_V
    (hS : Admissible P.ell M R P.k P.S) (hell0 : 0 < P.ell)
    (hroom : 17 * P.ell ≤ R * M)
    (hloc : IsUnit (G1invS selIn selIn P))
    (hker : ∀ x, ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) x = 0 → x ∈ V0 P.G) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) := by
  apply unit_of_kernel_zero
  intro x hx
  exact pencil_kernel_in_V_zero P hS hell0 hroom hloc x (hker x hx) hx

/-- On the literal guard domain, corrected null vectors are fixed vectors of
actual inverse times actual localized correction. No positivity is required. -/
theorem pencil_kernel_iff_feedback_fixed
    (hu : IsUnit (dataS selAll selAll P).Ginv) (x : ↥(bondSupp P.G)) :
    ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) x = 0 ↔
    ((Ring.inverse (dataS selAll selAll P).Ginv).comp
      ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))) x = x := by
  let A := (dataS selAll selAll P).Ginv
  let D := (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
  change (A - D) x = 0 ↔ (Ring.inverse A).comp D x = x
  constructor
  · intro hx
    have heq : A x = D x := sub_eq_zero.mp hx
    change Ring.inverse A (D x) = x
    rw [← heq]
    exact congrArg (fun T : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G) => T x)
      (Ring.inverse_mul_cancel A hu)
  · intro hx
    have heq : A (Ring.inverse A (D x)) = D x :=
      congrArg (fun T : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G) => T (D x))
        (Ring.mul_inverse_cancel A hu)
    change Ring.inverse A (D x) = x at hx
    rw [hx] at heq
    exact sub_eq_zero.mpr heq

/-- Sufficient margin using the inverse-relative correction. Unlike the old
positive-coercivity margin, it also applies to indefinite literal units. -/
theorem pencil_isUnit_of_feedback_norm_lt_one
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (hnorm : ‖(Ring.inverse (dataS selAll selAll P).Ginv).comp
      ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))‖ < 1) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) := by
  apply unit_of_kernel_zero
  intro x hx
  have hfix := (pencil_kernel_iff_feedback_fixed P hu x).mp hx
  have hbound := ((Ring.inverse (dataS selAll selAll P).Ginv).comp
    ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))).le_opNorm x
  rw [hfix] at hbound
  by_contra hne
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hne
  have hlt := mul_lt_mul_of_pos_right hnorm hpos
  rw [one_mul] at hlt
  exact (not_lt_of_ge hbound) hlt

/-- Every genuine unit/singular separation has a nonzero level-zero coordinate,
a nonzero correction action, and inverse-relative correction norm at least one.
This excludes no such separation without an additional source-specific bound. -/
theorem guarded_kernel_obstruction
    (hS : Admissible P.ell M R P.k P.S) (hell0 : 0 < P.ell)
    (hroom : 17 * P.ell ≤ R * M)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (hloc : IsUnit (G1invS selIn selIn P))
    (hbad : ¬ IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))) :
    (∃ x : ↥(bondSupp P.G), x ≠ 0 ∧
      ((dataS selAll selAll P).Ginv -
        (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) x = 0 ∧
      (∃ b : Bond P.Lf, b ∈ bondsLam P.G 0 ∧ (WithLp.ofLp (iE P.G x)) b ≠ 0) ∧
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x ≠ 0) ∧
    1 ≤ ‖(Ring.inverse (dataS selAll selAll P).Ginv).comp
      ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))‖ := by
  have hex : ∃ x : ↥(bondSupp P.G),
      ((dataS selAll selAll P).Ginv -
        (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) x = 0 ∧ x ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hbad (unit_of_kernel_zero _ hn)
  obtain ⟨x, hk, hne⟩ := hex
  have htrace : ∃ b : Bond P.Lf, b ∈ bondsLam P.G 0 ∧
      (WithLp.ofLp (iE P.G x)) b ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hne (pencil_kernel_in_V_zero P hS hell0 hroom hloc x hn hk)
  have hD : (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x ≠ 0 := by
    intro hzero
    have hA : (dataS selAll selAll P).Ginv x = 0 := by
      have heq := sub_eq_zero.mp hk
      exact heq.trans hzero
    exact hne ((injective_iff_map_eq_zero (dataS selAll selAll P).Ginv).mp
      (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1 x hA)
  refine ⟨⟨x, hne, hk, htrace, hD⟩, ?_⟩
  by_contra hn
  exact hbad (pencil_isUnit_of_feedback_norm_lt_one P hu (lt_of_not_ge hn))

end Pointwise

/-- Boundary-trace condition for the unchanged concrete pencil. -/
def CBoundary : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell)
    (_ : Tower (scaleUp ell k Lu)) (_ : LinkCfg (scaleUp ell k Lu))
    (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop :=
  fun ell k Lu h S U a Lam =>
    let P := gparams ell k Lu h S U a Lam
    ∀ x, ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) x = 0 → x ∈ V0 P.G

/-- Exact equivalence, with all pinned eventual/class/test-field quantifiers.
The boundary condition is NOT proved by this declaration. -/
theorem goalPos1_iff_boundary_kernel : GoalPos1 ↔ GShape CBoundary := by
  constructor
  · intro hp
    exact AdalyFormal.D1Residual.GShape_imp AdalyFormal.D1Residual.CPen CBoundary
      (fun ell k h0 M R Lu S U a Lam _ _ _ _ hc x hx => by
        have hz : x = 0 := (injective_iff_map_eq_zero _).mp
          (ContinuousLinearMap.isUnit_iff_bijective.mp hc).1 x hx
        rw [hz]
        exact (V0 _).zero_mem) hp
  · intro hb
    exact AdalyFormal.D1Residual.GShape_imp CBoundary AdalyFormal.D1Residual.CPen
      (fun ell k h0 M R Lu S U a Lam hS hr hW _ hc =>
        pencil_isUnit_of_kernel_mem_V (gparams ell k Lu h0 S U a Lam) hS h0 hr hW.2.1 hc) hb

/-- Reduction of the original pinned positive headline, not its proof. -/
theorem goalPos2_iff_boundary_kernel : GoalPos2 ↔ GShape CBoundary :=
  goalPos2_iff_goalPos1.trans goalPos1_iff_boundary_kernel

/-- A sufficient quantitative conclusion in the same unmodified GShape prefix. -/
def CFeedbackSmall : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell)
    (_ : Tower (scaleUp ell k Lu)) (_ : LinkCfg (scaleUp ell k Lu))
    (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop :=
  fun ell k Lu h S U a Lam =>
    let P := gparams ell k Lu h S U a Lam
    ‖(Ring.inverse (dataS selAll selAll P).Ginv).comp
      ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))‖ < 1

/-- A conditional positive route. The displayed hypothesis is not discharged. -/
theorem goalPos2_of_feedback_smallness (h : GShape CFeedbackSmall) : GoalPos2 := by
  apply goalPos2_iff_goalPos1.mpr
  exact AdalyFormal.D1Residual.GShape_imp CFeedbackSmall AdalyFormal.D1Residual.CPen
    (fun ell k h0 M R Lu S U a Lam _ _ _ hu hn =>
      pencil_isUnit_of_feedback_norm_lt_one (gparams ell k Lu h0 S U a Lam) hu hn) h

#print axioms CFeedbackSmall
#print axioms goalPos2_of_feedback_smallness
#print axioms unit_of_kernel_zero
#print axioms pencil_eq_local_on_V
#print axioms pencil_kernel_in_V_zero
#print axioms pencil_isUnit_of_kernel_mem_V
#print axioms pencil_kernel_iff_feedback_fixed
#print axioms pencil_isUnit_of_feedback_norm_lt_one
#print axioms guarded_kernel_obstruction
#print axioms CBoundary
#print axioms goalPos1_iff_boundary_kernel
#print axioms goalPos2_iff_boundary_kernel

-- Frozen helpers directly used above: their transitive closures are checked too.
#print axioms AdalyFormal.D1Guarded.Ginv_eq_on_V
#print axioms AdalyFormal.D1Literal.G1invS_spec
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.G1inv_unique
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.isG1inv_sub
#print axioms AdalyFormal.D1Residual.GShape_imp
#print axioms AdalyFormal.D1Residual.P428Target8SG_iff_pencilT

#print axioms AdalyFormal.D1Guarded.V0
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

end AdalyFormal.Round2.Guarded.R1Prove
