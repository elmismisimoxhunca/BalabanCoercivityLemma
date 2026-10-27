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
Second positive attempt. The boundary response below is constructed from the
actual difference of selectors, not from a substitute lattice or a compression
of the literal inverse. All results following the pin are partial reductions.
-/
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

/-- Finite-dimensional endomorphism criterion, as used by frozen unit_transfer. -/
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

/-- The exact response on the range of the perturbation. -/
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

/-- This is an actual restriction to an invariant range, not an inverse of a
compression of B. -/
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

/-- A sufficient exact no-return condition, allowing a nonzero D. It is not
asserted that the concrete class satisfies this condition. -/
theorem unit_corrected_of_no_return (Θ B D : E →L[ℝ] E)
    (hB : IsUnit B) (hC : IsUnit (B - D)) (hM : IsUnit (B + Θ))
    (hret : ∀ y : Θ.range, Θ (Ring.inverse (B - D) (D (Ring.inverse B y))) = 0) :
    IsUnit (B - D + Θ) := by
  have heq : response Θ (B - D) = response Θ B := by
    ext y
    exact sub_eq_zero.mp ((response_sub_apply Θ B D hB hC y).trans (hret y))
  apply (unit_add_iff_response Θ (B - D) hC).mpr
  rw [heq]
  exact (unit_add_iff_response Θ B hB).mp hM

/-- Kernel witness on the response space, with its inherited Hilbert structure. -/
theorem exists_response_kernel (Θ B : E →L[ℝ] E)
    (hbad : ¬ IsUnit (response Θ B)) :
    ∃ y : Θ.range, response Θ B y = 0 ∧ y ≠ 0 := by
  by_contra hn
  push Not at hn
  exact hbad (unit_of_kernel_zero (response Θ B) hn)

/-- Unit responses cannot annihilate a nonzero boundary mode. -/
theorem response_apply_ne_zero (Θ B : E →L[ℝ] E)
    (hu : IsUnit (response Θ B)) (y : Θ.range) (hy : y ≠ 0) :
    response Θ B y ≠ 0 := by
  intro hz
  exact hy ((injective_iff_map_eq_zero (response Θ B)).mp
    (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1 y hz)

end Algebra

section Concrete
variable (P : IngrBParams)

/-- Exact selector difference of the pinned assemblies. -/
noncomputable def boundaryShift : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G) :=
  (dataS selAll selAll P).Ginv - (dataS selIn selIn P).Ginv

/-- Exact corrected localized operator. -/
noncomputable def localCorrected : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G) :=
  (dataS selIn selIn P).Ginv -
    (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)

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

/-- Geometry inherited from the frozen agreement theorem. -/
theorem boundaryShift_kills_V {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hell0 : 0 < P.ell)
    (hroom : 17 * P.ell ≤ R * M) (x : ↥(bondSupp P.G)) (hx : x ∈ V0 P.G) :
    boundaryShift P x = 0 := by
  exact sub_eq_zero.mpr (Ginv_eq_on_V P hS hell0 hroom selAll selAll selIn selIn
    (fun _ _ => Set.subset_univ _) (fun _ _ => Set.Subset.refl _) hx)

/-- Symmetry makes the reduction a genuine level-zero boundary reduction:
the whole shift range is orthogonal to fields with zero level-zero trace. -/
theorem boundaryShift_range_le_orthogonal {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hell0 : 0 < P.ell)
    (hroom : 17 * P.ell ≤ R * M) : (boundaryShift P).range ≤ (V0 P.G)ᗮ := by
  rintro y ⟨x, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  intro v hv
  change ⟪v, boundaryShift P x⟫ = 0
  have hsym : ⟪boundaryShift P v, x⟫ = ⟪v, boundaryShift P x⟫ := by
    simp only [boundaryShift, sub_apply, inner_sub_left,
      inner_sub_right,
      (dataS selAll selAll P).Ginv_symm (dataS_laws selAll selAll P),
      (dataS selIn selIn P).Ginv_symm (dataS_laws selIn selIn P)]
  rw [← hsym, boundaryShift_kills_V P hS hell0 hroom v hv, inner_zero_left]

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

/-- Non-flat sufficient condition with the actual localized correction. -/
theorem pencil_isUnit_of_no_boundary_return
    (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (hret : ∀ y : (boundaryShift P).range,
      boundaryShift P (Ring.inverse (localCorrected P)
        ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
          (Ring.inverse (dataS selIn selIn P).Ginv y))) = 0) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) := by
  rw [pencil_eq_local_add_shift P]
  apply unit_corrected_of_no_return _ _ _ hW.1
  · change IsUnit (localCorrected P)
    rw [localCorrected_eq P]
    exact hW.2.1
  · change IsUnit ((dataS selIn selIn P).Ginv + boundaryShift P)
    rw [← carrier_eq_local_add_shift P]
    exact hu
  · exact hret

/-- Any guarded failure has a nonzero boundary mode and a nonzero return
through the actual correction. The return uses only localized inverses. -/
theorem guarded_failure_forces_boundary_return
    (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (hbad : ¬ IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))) :
    ∃ y : (boundaryShift P).range, y ≠ 0 ∧
      response (boundaryShift P) (localCorrected P) y = 0 ∧
      boundaryShift P (Ring.inverse (localCorrected P)
        ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
          (Ring.inverse (dataS selIn selIn P).Ginv y))) ≠ 0 := by
  have hC : IsUnit (localCorrected P) := by
    rw [localCorrected_eq P]
    exact hW.2.1
  have hK : IsUnit (response (boundaryShift P) (dataS selIn selIn P).Ginv) :=
    (carrier_isUnit_iff_response P hW.1).mp hu
  obtain ⟨y, hy, hne⟩ := exists_response_kernel (boundaryShift P) (localCorrected P)
    (fun hK' => hbad ((pencil_isUnit_iff_response P hW.2.1).mpr hK'))
  refine ⟨y, hne, hy, ?_⟩
  intro hzero
  have hdiff := response_sub_apply (boundaryShift P) (dataS selIn selIn P).Ginv
    ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) hW.1 hC y
  change (response (boundaryShift P) (localCorrected P) y : ↥(bondSupp P.G)) -
    (response (boundaryShift P) (dataS selIn selIn P).Ginv y : ↥(bondSupp P.G)) =
      boundaryShift P (Ring.inverse (localCorrected P)
        ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
          (Ring.inverse (dataS selIn selIn P).Ginv y))) at hdiff
  rw [hzero] at hdiff
  have heq : response (boundaryShift P) (localCorrected P) y =
      response (boundaryShift P) (dataS selIn selIn P).Ginv y :=
    Subtype.ext (sub_eq_zero.mp hdiff)
  have hkzero : response (boundaryShift P) (dataS selIn selIn P).Ginv y = 0 :=
    heq.symm.trans hy
  exact response_apply_ne_zero (boundaryShift P) (dataS selIn selIn P).Ginv
    hK y hne hkzero

end Concrete

/-- Conclusion only: the prefix is the unchanged pinned GShape. -/
def CBoundaryResponse : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell)
    (_ : Tower (scaleUp ell k Lu)) (_ : LinkCfg (scaleUp ell k Lu))
    (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop :=
  fun ell k Lu h S U a Lam =>
    let P := gparams ell k Lu h S U a Lam
    IsUnit (response (boundaryShift P) (localCorrected P))

/-- Exact eventual reduction, not a proof of either side. -/
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

/-- A sufficient exact condition, not an asserted property of the class. -/
def CNoBoundaryReturn : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell)
    (_ : Tower (scaleUp ell k Lu)) (_ : LinkCfg (scaleUp ell k Lu))
    (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop :=
  fun ell k Lu h S U a Lam =>
    let P := gparams ell k Lu h S U a Lam
    ∀ y : (boundaryShift P).range,
      boundaryShift P (Ring.inverse (localCorrected P)
        ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
          (Ring.inverse (dataS selIn selIn P).Ginv y))) = 0

/-- Conditional positive route; the no-return premise remains open. -/
theorem goalPos2_of_no_boundary_return (h : GShape CNoBoundaryReturn) : GoalPos2 := by
  apply goalPos2_iff_goalPos1.mpr
  exact AdalyFormal.D1Residual.GShape_imp CNoBoundaryReturn AdalyFormal.D1Residual.CPen
    (fun ell k h0 M R Lu S U a Lam _ _ hW hu hn =>
      pencil_isUnit_of_no_boundary_return (gparams ell k Lu h0 S U a Lam) hW hu hn) h

#print axioms unit_of_kernel_zero
#print axioms response
#print axioms response_apply
#print axioms unit_add_iff_response
#print axioms inverse_sub_apply
#print axioms response_sub_apply
#print axioms unit_corrected_of_no_return
#print axioms exists_response_kernel
#print axioms response_apply_ne_zero
#print axioms boundaryShift
#print axioms localCorrected
#print axioms localCorrected_eq
#print axioms carrier_eq_local_add_shift
#print axioms pencil_eq_local_add_shift
#print axioms boundaryShift_kills_V
#print axioms boundaryShift_range_le_orthogonal
#print axioms carrier_isUnit_iff_response
#print axioms pencil_isUnit_iff_response
#print axioms pencil_isUnit_of_no_boundary_return
#print axioms guarded_failure_forces_boundary_return
#print axioms CNoBoundaryReturn
#print axioms goalPos2_of_no_boundary_return
#print axioms CBoundaryResponse
#print axioms goalPos1_iff_boundary_response
#print axioms goalPos2_iff_boundary_response

-- Frozen proof roots directly reused in the concrete reduction.
#print axioms AdalyFormal.D1Guarded.Ginv_eq_on_V
#print axioms AdalyFormal.D1Literal.G1invS_spec
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.G1inv_unique
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.isG1inv_sub
#print axioms AdalyFormal.IngredientFamilyR2.BaseDataS.Ginv_symm
#print axioms AdalyFormal.D1Residual.GShape_imp
#print axioms AdalyFormal.D1Residual.P428Target8SG_iff_pencilT
#print axioms AdalyFormal.D1Guarded.WellDefAt
#print axioms AdalyFormal.D1Guarded.V0

-- Copied operative definitions receive individual dependency records too.
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

end AdalyFormal.Round2.Guarded.R2Prove
