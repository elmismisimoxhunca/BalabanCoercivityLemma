import D1Final

/-!
# D2Lit -- the OTHER literal sandwich: `Δ` (3.10) summed over all plaquettes, then Dirichlet-compressed by a BOND mask `χ_B` (`Δ ↦ χ_B Δ χ_B`) before `Δ_π = W* Δ W`.
`B = touching bonds` (CMP96 p.224 convention) gives back exactly the operator of `D1Lit` (`dataM_touch`: because `W` maps `E₀` into `E₀`);
`B = bonds with BOTH endpoints in Ω₀` is r6's reading "χ_both Δ χ_both" (undecided in statement_audit_r6_opus).  `B = everything` is `D1Lit` with the identity mask (`dataM_univ`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

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

variable {L : PeriodicLatticeExtent}

open Classical in
/-- multiplication by the indicator of a set of bonds. -/
noncomputable def bondMask (B : Set (Bond L)) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => WithLp.toLp 2 (fun b => if b ∈ B then (WithLp.ofLp A) b else 0)
      map_add' := fun A A' => by ext b; simp only [PiLp.add_apply]; split_ifs <;> simp
      map_smul' := fun c A => by ext b; simp only [PiLp.smul_apply]; split_ifs <;> simp }

open Classical in
theorem bondMask_apply (B : Set (Bond L)) (A : BondFnL2 L) (b : Bond L) :
    (bondMask B A) b = if b ∈ B then A b else 0 := rfl

theorem bondMask_symm (B : Set (Bond L)) (A A' : BondFnL2 L) :
    ⟪bondMask B A, A'⟫ = ⟪A, bondMask B A'⟫ := by
  simp only [PiLp.inner_apply, bondMask_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs <;> simp

theorem bondMask_eq_self (B : Set (Bond L)) (A : BondFnL2 L) (h : ∀ b, b ∉ B → A b = 0) : bondMask B A = A := by
  refine PiLp.ext (fun b => ?_)
  rw [bondMask_apply]; split_ifs with hb
  · rfl
  · exact (h b hb).symm

theorem bondMask_univ (A : BondFnL2 L) : bondMask (Set.univ : Set (Bond L)) A = A :=
  bondMask_eq_self _ _ (fun b hb => absurd (Set.mem_univ b) hb)

/-- a choice of bond set, as a function of the tower geometry. -/
abbrev BondSel : Type := ∀ (L : PeriodicLatticeExtent), TowerGeom L → Set (Bond L)

/-- bonds with at least one endpoint in `Ω₀` (CMP96 p.224). -/
def touchSel : BondSel := fun _ G => bondsOm0 G
/-- bonds with BOTH endpoints in `Ω₀`. -/
def bothSel : BondSel := fun _ G => {b | BothIn G.Om0 b}
/-- all bonds (identity mask). -/
def allSel : BondSel := fun _ _ => Set.univ

variable (sD sJ : PlaqSel) (bs : BondSel)

/-- `χ_B Δ χ_B`. -/
noncomputable def DeltaM (G : TowerGeom L) (U : Cfg L) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  (bondMask (bs L G)).comp ((DeltaS sD G U).comp (bondMask (bs L G)))

noncomputable def DpiFullM (G : TowerGeom L) (U : Cfg L) (a : ℝ) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  (ContinuousLinearMap.adjoint (Wop G U a)).comp ((DeltaM sD bs G U).comp (Wop G U a))

theorem DeltaM_symm (G : TowerGeom L) (U : Cfg L) (x y : BondFnL2 L) :
    ⟪DeltaM sD bs G U x, y⟫ = ⟪x, DeltaM sD bs G U y⟫ := by
  simp only [DeltaM, DeltaS, ContinuousLinearMap.comp_apply]
  rw [bondMask_symm, AdalyFormal.StatementLaneR6.deltaKLocCLM_symm, bondMask_symm]

theorem DpiFullM_symm (G : TowerGeom L) (U : Cfg L) (a : ℝ) (x y : BondFnL2 L) :
    ⟪DpiFullM sD bs G U a x, y⟫ = ⟪x, DpiFullM sD bs G U a y⟫ := by
  simp only [DpiFullM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  exact DeltaM_symm sD bs G U _ _

section Ops
variable (P : IngrBParams)

noncomputable def dataM : BaseDataS ↥(bondSupp P.G) (SiteL2 (scaleUp P.ell P.k P.Lu)) (FSp P.G) :=
  { baseData P.G P.U P.a P.sector (JfS sJ P) with
    Dpi := (pE P.G).comp ((DpiFullM sD bs P.G P.U P.a).comp (iE P.G)) }

theorem dataM_laws : (dataM sD sJ bs P).Laws := by
  refine ⟨fun x y => ?_, P.data_laws.C2_quad⟩
  show ⟪((pE P.G).comp ((DpiFullM sD bs P.G P.U P.a).comp (iE P.G))) x, y⟫ = ⟪x, ((pE P.G).comp ((DpiFullM sD bs P.G P.U P.a).comp (iE P.G))) y⟫
  simp only [ContinuousLinearMap.comp_apply]
  rw [pE_inner_left, pE_inner_right]
  exact DpiFullM_symm sD bs P.G P.U P.a _ _

noncomputable def G1invM : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G) :=
  Classical.choose ((dataM sD sJ bs P).exists_G1inv (dataM_laws sD sJ bs P))

theorem G1invM_spec : (dataM sD sJ bs P).IsG1inv (G1invM sD sJ bs P) :=
  Classical.choose_spec ((dataM sD sJ bs P).exists_G1inv (dataM_laws sD sJ bs P))

noncomputable def H1inM : BondFnL2 P.Lu →L[ℝ] BondFnL2 (scaleUp P.ell P.k P.Lu) :=
  (iE P.G).comp (((dataM sD sJ bs P).H1 (G1invM sD sJ bs P)).comp (ContinuousLinearMap.adjoint P.tau))

end Ops

namespace GenM
variable (P : IngrBParams)

noncomputable def NmatM : FSp P.G →L[ℝ] FSp P.G :=
  ((dataM sD sJ bs P).Q.comp ((dataM sD sJ bs P).G1 (G1invM sD sJ bs P))).comp (dataM sD sJ bs P).Qs

noncomputable def firstTermM (B : BondFnL2 P.Lu) : ℝ :=
  P.eta * ⟪ContinuousLinearMap.adjoint P.tau B, Ring.inverse (NmatM sD sJ bs P) (ContinuousLinearMap.adjoint P.tau B)⟫

noncomputable def genFormM (B : BondFnL2 P.Lu) : ℝ :=
  firstTermM sD sJ bs P B - P.a * ⟪B, B⟫ - 2 * ⟪H1inM sD sJ bs P (P.D2in B), JfS sJ P⟫
end GenM

def InstIneqM (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) : Prop :=
  ∀ (Bt : Bond Lu → SuTwo), OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
    γ₀ * bondEnergy Bt ≤
      GenM.genFormM sD sJ bs (gparams ell k Lu hell S U a Lam)
        (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt))

def CoercG8AtM (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneqM sD sJ bs ell k hell a Lu γ₀ S Lam U

def P428Core8AtM (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) (c : ℕ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtM sD sJ bs ell M R k hell a Lu c α₀ γ₀

def P428Core8M (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop := P428Core8AtM sD sJ bs ell M R hell a 12

def P428Genuine8M (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ P428Core8M sD sJ bs ell M R hell a

/-- the headline with `Δ` plaquette set `sD`, bond mask `bs`, `J` plaquette set `sJ`. -/
def P428Target8M : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8M sD sJ bs ell (ell ^ m) R (by omega) a

/-- all-plaquette `Δ` compressed to bonds with BOTH endpoints in `Ω₀` (r6's `χ_both Δ χ_both`); `J` over all plaquettes. -/
def P428Target8LiteralBoth : Prop := P428Target8M selAll selAll bothSel
/-- all-plaquette `Δ` compressed to TOUCHING bonds. -/
def P428Target8LiteralTouch : Prop := P428Target8M selAll selAll touchSel

/-! ### pins -/

theorem DeltaM_univ (G : TowerGeom L) (U : Cfg L) : DeltaM sD allSel G U = DeltaS sD G U := by
  ext1 A
  simp only [DeltaM, allSel, ContinuousLinearMap.comp_apply, bondMask_univ]

theorem DpiFullM_univ (G : TowerGeom L) (U : Cfg L) (a : ℝ) : DpiFullM sD allSel G U a = DpiFullS sD G U a := by
  unfold DpiFullM DpiFullS; rw [DeltaM_univ]

/-- PIN: with the identity mask the masked data IS the unmasked data. -/
theorem dataM_univ (P : IngrBParams) : dataM sD sJ allSel P = dataS sD sJ P := by
  simp only [dataM, dataS, DpiFullM_univ]

/-- `W` maps `E₀` (touching-bond fields) into `E₀`. -/
theorem Wop_mem_bondSupp (G : TowerGeom L) (U : Cfg L) (a : ℝ) (A : BondFnL2 L) (hA : A ∈ bondSupp G) :
    Wop G U a A ∈ bondSupp G := by
  intro b hb
  have hb1 : b.1 ∉ G.Om0 := fun h => hb (Or.inl h)
  have hb2 : periodicLatticeShift b.1 b.2 ∉ G.Om0 := fun h => hb (Or.inr h)
  unfold Wop
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
  show (WithLp.ofLp A) b - (WithLp.ofLp (gradL2 U _)) b = 0
  rw [gradL2_apply]
  unfold AdalyFormal.Balaban.CovariantOperators.gradValueCovariant
  rw [Gp_supp G U a _ _ hb2, Gp_supp G U a _ _ hb1, hA b hb]
  simp

theorem Dpi_touch_eq (P : IngrBParams) :
    (pE P.G).comp ((DpiFullM sD touchSel P.G P.U P.a).comp (iE P.G)) =
      (pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G)) := by
  ext1 x
  refine ext_inner_left ℝ (fun y => ?_)
  simp only [ContinuousLinearMap.comp_apply]
  rw [pE_inner_right, pE_inner_right]
  unfold DpiFullM DpiFullS DeltaM
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  have hx := Wop_mem_bondSupp P.G P.U P.a (iE P.G x) x.2
  have hy := Wop_mem_bondSupp P.G P.U P.a (iE P.G y) y.2
  have e1 : bondMask (touchSel (scaleUp P.ell P.k P.Lu) P.G) (Wop P.G P.U P.a (iE P.G x)) = Wop P.G P.U P.a (iE P.G x) :=
    bondMask_eq_self _ _ (fun b hb => hx b hb)
  have e2 : bondMask (touchSel (scaleUp P.ell P.k P.Lu) P.G) (Wop P.G P.U P.a (iE P.G y)) = Wop P.G P.U P.a (iE P.G y) :=
    bondMask_eq_self _ _ (fun b hb => hy b hb)
  rw [← bondMask_symm, e2, e1]

/-- PIN (the exact relation, F3): compressing `Δ` to TOUCHING bonds inside `Δ_π = W*ΔW` changes nothing on `E₀`, because `W E₀ ⊆ E₀`. -/
theorem dataM_touch (P : IngrBParams) : dataM sD sJ touchSel P = dataS sD sJ P := by
  simp only [dataM, dataS, Dpi_touch_eq]

#print axioms dataM_univ
#print axioms dataM_touch

end AdalyFormal.D1Literal
