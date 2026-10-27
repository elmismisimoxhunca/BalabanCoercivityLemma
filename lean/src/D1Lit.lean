import ZT5A

/-!
# D1Lit -- the LITERAL (all-plaquette) variants of the r8 headline `P428Target8`  (lane d1_literal_20261018)

The r8 headline localises `Δ` (3.10) and `J` (3.11) to `plaqIn Ω₀`.  The print sums over all plaquettes / bonds of `T_η`.
Here a *plaquette selector* `sD sJ : PlaqSel` (a function of the tower geometry) is threaded through the operators `Δ` and `J` ONLY;
every other ingredient is the r8 one, unchanged.  `selIn` is the r8 reading, `selAll` the literal reading.
`target8S selIn selIn = P428Target8` is `rfl` (`pin_target8`): the generalisation changes nothing at the r8 selector.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- a choice of plaquette set, as a function of the tower geometry. -/
abbrev PlaqSel : Type := ∀ (L : PeriodicLatticeExtent), TowerGeom L → Set (PeriodicLatticePlaquette L)

/-- the r8 reading: plaquettes with all four boundary bonds having both endpoints in `Ω₀`. -/
def selIn : PlaqSel := fun _ G => plaqIn G.Om0
/-- the literal reading: every plaquette of the torus (`Σ_{p ⊂ T_η}`). -/
def selAll : PlaqSel := fun _ _ => Set.univ

variable (sD sJ : PlaqSel)

/-- `Δ` of (3.10) with the plaquette set chosen by `sD`. -/
noncomputable def DeltaS {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  AdalyFormal.StatementLaneR6.deltaKLocCLM U (sD L G)

/-- `Δ_π = W* Δ W` with the chosen `Δ`. -/
noncomputable def DpiFullS {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (a : ℝ) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  (ContinuousLinearMap.adjoint (Wop G U a)).comp ((DeltaS sD G U).comp (Wop G U a))

theorem DpiFullS_symm {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (a : ℝ) (x y : BondFnL2 L) :
    ⟪DpiFullS sD G U a x, y⟫ = ⟪x, DpiFullS sD G U a y⟫ := by
  simp only [DpiFullS, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  exact AdalyFormal.StatementLaneR6.deltaKLocCLM_symm U _ _ _

section Ops
variable (P : IngrBParams)

/-- `J` of (3.11) with the plaquette set chosen by `sJ`. -/
noncomputable def JfS : BondFnL2 (scaleUp P.ell P.k P.Lu) :=
  WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1 (sJ _ P.G) P.U b))

/-- the base data (3.122)-(3.128) with `Δ`, `J` chosen by `sD`, `sJ`. -/
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

theorem G1invS_spec : (dataS sD sJ P).IsG1inv (G1invS sD sJ P) :=
  Classical.choose_spec ((dataS sD sJ P).exists_G1inv (dataS_laws sD sJ P))

noncomputable def H1inS : BondFnL2 P.Lu →L[ℝ] BondFnL2 (scaleUp P.ell P.k P.Lu) :=
  (iE P.G).comp (((dataS sD sJ P).H1 (G1invS sD sJ P)).comp (ContinuousLinearMap.adjoint P.tau))

end Ops

namespace GenS
variable (P : IngrBParams)

noncomputable def NmatS : FSp P.G →L[ℝ] FSp P.G :=
  ((dataS sD sJ P).Q.comp ((dataS sD sJ P).G1 (G1invS sD sJ P))).comp (dataS sD sJ P).Qs

noncomputable def firstTermS (B : BondFnL2 P.Lu) : ℝ :=
  P.eta * ⟪ContinuousLinearMap.adjoint P.tau B, Ring.inverse (NmatS sD sJ P) (ContinuousLinearMap.adjoint P.tau B)⟫

/-- (3.156) with `Δ`, `J` chosen by `sD`, `sJ`. -/
noncomputable def genFormS (B : BondFnL2 P.Lu) : ℝ :=
  firstTermS sD sJ P B - P.a * ⟪B, B⟫ - 2 * ⟪H1inS sD sJ P (P.D2in B), JfS sJ P⟫
end GenS

def InstIneqS (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) : Prop :=
  ∀ (Bt : Bond Lu → SuTwo), OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
    γ₀ * bondEnergy Bt ≤
      GenS.genFormS sD sJ (gparams ell k Lu hell S U a Lam)
        (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt))

def CoercG8AtS (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneqS sD sJ ell k hell a Lu γ₀ S Lam U

def P428Core8AtS (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) (c : ℕ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtS sD sJ ell M R k hell a Lu c α₀ γ₀

def P428Core8S (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop := P428Core8AtS sD sJ ell M R hell a 12

def P428Genuine8S (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ P428Core8S sD sJ ell M R hell a

/-- the headline with selectors `sD`, `sJ`. -/
def P428Target8S : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8S sD sJ ell (ell ^ m) R (by omega) a

/-- LIT-ALL: `Δ` and `J` both summed over all plaquettes of the torus. -/
def P428Target8Literal : Prop := P428Target8S selAll selAll
/-- LIT-Δ: only `Δ` literal. -/
def P428Target8LiteralDelta : Prop := P428Target8S selAll selIn

/-- PIN: at the r8 selector the generalised headline IS the frozen `P428Target8` (definitional). -/
theorem pin_target8 : P428Target8S selIn selIn = P428Target8 := rfl
theorem pin_target8_iff : P428Target8S selIn selIn ↔ P428Target8 := Iff.rfl

/-- PIN: the generalised form at the r8 selector equals `genForm` pointwise. -/
theorem pin_genForm (P : IngrBParams) (B : BondFnL2 P.Lu) : GenS.genFormS selIn selIn P B = GenP.genForm P B := rfl

/-- PIN: `selAll` is the whole plaquette set; `selIn` is `plaqIn Ω₀`. -/
theorem selAll_eq (L : PeriodicLatticeExtent) (G : TowerGeom L) : selAll L G = Set.univ := rfl
theorem selIn_eq (L : PeriodicLatticeExtent) (G : TowerGeom L) : selIn L G = plaqIn G.Om0 := rfl
/-- the literal `Δ` is the r5 operator `deltaKCLMNormalized` (sum over ALL plaquettes). -/
theorem DeltaS_selAll_eq {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) :
    DeltaS selAll G U = AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized U := by
  unfold DeltaS selAll
  exact AdalyFormal.StatementLaneR6.deltaKLocCLM_univ U

#print axioms pin_target8
#print axioms pin_genForm
#print axioms DeltaS_selAll_eq

end AdalyFormal.D1Literal
