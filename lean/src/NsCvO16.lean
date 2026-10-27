import NsCvO15

/-!
# CvO16 -- the raw one-step averaging of a Cartan background perturbed by a sigma_3 field (lane omega)

Let `V0 = cartanOf φ` (Cartan background) and `V1 = cartanOf θ` (sigma_3 perturbation, `θ : Edge → ℝ`).  Everything is abelian:
`rawStep s ell V0 V1 c = cartan (Rσ s ell θ c)` with `Rσ θ c = -S(θ; c₋) + Ā(θ; c) + S(θ; c₊)` LINEAR in `θ` and independent of `φ`,
provided no `su2Log` wraps: `|loopAngG (θ+φ)| < π` at every loop of every block, `|pathAngG θ Γ| < π`, `|Rσ θ| < π`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2 (rProd_eq sBlock rawStep rawStep_simp)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf coarsePathHolonomy_cons coarsePathHolonomy_nil coarsePathEndpoint_cons)

variable {L : PeriodicLatticeExtent}

/-- the Cartan configuration of angles `θ`. -/
noncomputable def cartanOf (θ : PeriodicLatticeEdge L → ℝ) : PeriodicLinkConfiguration SU2 L := fun e => cartan (θ e)

/-- angle along a stride-`s` path. -/
noncomputable def pathAngG (s : ℕ) (θ : PeriodicLatticeEdge L → ℝ) : PeriodicLatticeSite L → List (Fin 3) → ℝ
  | _, [] => 0
  | y, μ :: rest => θ (y, μ) + pathAngG s θ (coarseShift y s μ) rest

theorem hol_cartanOf (s : ℕ) (θ : PeriodicLatticeEdge L → ℝ) (p : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite L, coarsePathHolonomy s (cartanOf θ) y p = cartan (pathAngG s θ y p) := by
  induction p with
  | nil => intro y; rw [coarsePathHolonomy_nil]; exact cartan_zero.symm
  | cons μ rest ih =>
    intro y
    rw [coarsePathHolonomy_cons, ih]
    simp only [pathAngG, cartanOf, cartan_mul]

theorem pathAngG_append (s : ℕ) (θ : PeriodicLatticeEdge L → ℝ) (p q : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite L, pathAngG s θ y (p ++ q) = pathAngG s θ y p + pathAngG s θ (coarsePathEndpoint s y p) q := by
  induction p with
  | nil => intro y; simp [pathAngG, coarsePathEndpoint]
  | cons μ rest ih =>
    intro y
    simp only [List.cons_append, pathAngG, coarsePathEndpoint_cons, ih]
    ring

theorem pathAngG_add (s : ℕ) (θ θ' : PeriodicLatticeEdge L → ℝ) (p : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite L, pathAngG s (θ + θ') y p = pathAngG s θ y p + pathAngG s θ' y p := by
  induction p with
  | nil => intro y; simp [pathAngG]
  | cons μ rest ih => intro y; simp only [pathAngG, Pi.add_apply, ih]; ring

theorem pathAngG_smul (s : ℕ) (r : ℝ) (θ : PeriodicLatticeEdge L → ℝ) (p : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite L, pathAngG s (r • θ) y p = r * pathAngG s θ y p := by
  induction p with
  | nil => intro y; simp [pathAngG]
  | cons μ rest ih => intro y; simp only [pathAngG, Pi.smul_apply, smul_eq_mul, ih]; ring

theorem pathAngG_zero (s : ℕ) (p : List (Fin 3)) : ∀ y : PeriodicLatticeSite L, pathAngG s (0 : PeriodicLatticeEdge L → ℝ) y p = 0 := by
  induction p with
  | nil => intro y; simp [pathAngG]
  | cons μ rest ih => intro y; simp [pathAngG, ih]

/-- the loop angle `W_x = V(Γ_{c,x}) V(c)⁻¹` of `cartanOf θ`. -/
noncomputable def loopAngG (s ell : ℕ) (θ : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L) (μ : Fin 3)
    (x : PeriodicLatticeSite L) : ℝ :=
  pathAngG s θ y (coarseGammaPath s y x) + pathAngG s θ x (List.replicate ell μ)
    - pathAngG s θ (cPlusS s ell (y, μ)) (coarseGammaPath s y x) - pathAngG s θ y (List.replicate ell μ)

theorem loopVar_cartanOf (s ell : ℕ) (θ : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L) (μ : Fin 3)
    (x : PeriodicLatticeSite L) : loopVar s ell (cartanOf θ) (y, μ) x = cartan (loopAngG s ell θ y μ x) := by
  unfold loopVar gammaVarStrided coarseBondVar loopAngG
  simp only []
  rw [hol_cartanOf, hol_cartanOf, hol_cartanOf, hol_cartanOf, cartan_comb']

theorem loopAngG_add (s ell : ℕ) (θ θ' : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L) (μ : Fin 3) (x : PeriodicLatticeSite L) :
    loopAngG s ell (θ + θ') y μ x = loopAngG s ell θ y μ x + loopAngG s ell θ' y μ x := by
  unfold loopAngG; rw [pathAngG_add, pathAngG_add, pathAngG_add, pathAngG_add]; ring

theorem loopAngG_zero (s ell : ℕ) (y : PeriodicLatticeSite L) (μ : Fin 3) (x : PeriodicLatticeSite L) :
    loopAngG s ell (0 : PeriodicLatticeEdge L → ℝ) y μ x = 0 := by
  unfold loopAngG; simp only [pathAngG_zero]; ring

/-- the Cartan angle of the (43)-block average. -/
noncomputable def blockAngG (s ell : ℕ) (θ : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L) (μ : Fin 3) : ℝ :=
  (((ell : ℝ) ^ 3)⁻¹ * ∑ x ∈ stepBlockOf y s ell, loopAngG s ell θ y μ x) + pathAngG s θ y (List.replicate ell μ)

theorem blockAngG_add (s ell : ℕ) (θ θ' : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L) (μ : Fin 3) :
    blockAngG s ell (θ + θ') y μ = blockAngG s ell θ y μ + blockAngG s ell θ' y μ := by
  unfold blockAngG
  simp only [loopAngG_add, Finset.sum_add_distrib, pathAngG_add]; ring

theorem sbg_cartanOf (s ell : ℕ) (θ : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L) (μ : Fin 3)
    (h : ∀ x ∈ stepBlockOf y s ell, |loopAngG s ell θ y μ x| < Real.pi) :
    stridedBlockedGauge su2LogExp s ell (cartanOf θ) (y, μ) = cartan (blockAngG s ell θ y μ) := by
  have hcb : coarseBondVar s ell (cartanOf θ) (y, μ) = cartan (pathAngG s θ y (List.replicate ell μ)) := by
    unfold coarseBondVar; exact hol_cartanOf s θ _ y
  exact blocked_cartan s ell (cartanOf θ) (y, μ) (fun x => loopAngG s ell θ y μ x) _
    (fun x hx => ⟨loopVar_cartanOf s ell θ y μ x, h x hx⟩) hcb

/-- the angle of `S(y) = Σ_x ell^{-3} log (R V1)(Γ_{y,x})`. -/
noncomputable def sAngG (s ell : ℕ) (θ : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L) : ℝ :=
  ((ell : ℝ) ^ 3)⁻¹ * ∑ x ∈ stepBlockOf y s ell, pathAngG s θ y (coarseGammaPath s y x)

theorem sAngG_add (s ell : ℕ) (θ θ' : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L) :
    sAngG s ell (θ + θ') y = sAngG s ell θ y + sAngG s ell θ' y := by
  unfold sAngG; simp only [pathAngG_add, Finset.sum_add_distrib]; ring

theorem cartanOf_mul (φ θ : PeriodicLatticeEdge L → ℝ) :
    (fun b => cartanOf θ b * cartanOf φ b) = cartanOf (θ + φ) := by
  funext b; simp only [cartanOf, cartan_mul, Pi.add_apply]

theorem sBlock_cartanOf (s ell : ℕ) (φ θ : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L)
    (h : ∀ x ∈ stepBlockOf y s ell, |pathAngG s θ y (coarseGammaPath s y x)| < Real.pi) :
    sBlock s ell (cartanOf φ) (cartanOf θ) y = dg (sAngG s ell θ y) := by
  unfold sBlock sAngG
  have h1 : ∀ x ∈ stepBlockOf y s ell, ((ell : ℚ) ^ 3)⁻¹ • su2Log (AdalyFormal.IngredientFamilyR2.rProd s (cartanOf φ) (cartanOf θ) y (coarseGammaPath s y x))
      = dg ((((ell : ℝ) ^ 3)⁻¹) * pathAngG s θ y (coarseGammaPath s y x)) := by
    intro x hx
    rw [rProd_eq, cartanOf_mul, hol_cartanOf, hol_cartanOf, cartan_inv, cartan_mul, pathAngG_add]
    have : pathAngG s θ y (coarseGammaPath s y x) + pathAngG s φ y (coarseGammaPath s y x) + -pathAngG s φ y (coarseGammaPath s y x)
        = pathAngG s θ y (coarseGammaPath s y x) := by ring
    rw [this, su2Log_cartan _ (h x hx), dg_qsmul]
    push_cast; rfl
  rw [Finset.sum_congr rfl h1, ← dg_sum, ← Finset.mul_sum]

/-- the linear map `Rσ` -/
noncomputable def Rsig (s ell : ℕ) (θ : PeriodicLatticeEdge L → ℝ) (c : PeriodicLatticeEdge L) : ℝ :=
  - sAngG s ell θ c.1 + blockAngG s ell θ c.1 c.2 + sAngG s ell θ (cPlusS s ell c)

theorem Rsig_add (s ell : ℕ) (θ θ' : PeriodicLatticeEdge L → ℝ) :
    Rsig s ell (θ + θ') = Rsig s ell θ + Rsig s ell θ' := by
  funext c; simp only [Rsig, sAngG_add, blockAngG_add, Pi.add_apply]; ring

/-- **the abelian raw step**. -/
theorem rawStep_cartanOf (s ell : ℕ) (φ θ : PeriodicLatticeEdge L → ℝ) (c : PeriodicLatticeEdge L)
    (hloop : ∀ x ∈ stepBlockOf c.1 s ell, |loopAngG s ell φ c.1 c.2 x| < Real.pi)
    (hloop' : ∀ x ∈ stepBlockOf c.1 s ell, |loopAngG s ell (θ + φ) c.1 c.2 x| < Real.pi)
    (hS1 : ∀ x ∈ stepBlockOf c.1 s ell, |pathAngG s θ c.1 (coarseGammaPath s c.1 x)| < Real.pi)
    (hS2 : ∀ x ∈ stepBlockOf (cPlusS s ell c) s ell, |pathAngG s θ (cPlusS s ell c) (coarseGammaPath s (cPlusS s ell c) x)| < Real.pi) :
    rawStep s ell (cartanOf φ) (cartanOf θ) c = cartan (Rsig s ell θ c) := by
  rw [rawStep_simp, cartanOf_mul, sBlock_cartanOf s ell φ θ c.1 hS1, sBlock_cartanOf s ell φ θ _ hS2]
  obtain ⟨y, μ⟩ := c
  rw [sbg_cartanOf s ell (θ + φ) y μ hloop', sbg_cartanOf s ell φ y μ hloop]
  rw [show -(dg (sAngG s ell θ (y, μ).1)) = dg (-(sAngG s ell θ (y, μ).1)) by
    ext i j; fin_cases i <;> fin_cases j <;> simp [dg]]
  rw [su2Exp_dg, su2Exp_dg, cartan_inv, cartan_mul, cartan_mul, cartan_mul, blockAngG_add]
  unfold Rsig
  congr 1; simp only []; ring

#print axioms hol_cartanOf
#print axioms loopVar_cartanOf
#print axioms sbg_cartanOf
#print axioms sBlock_cartanOf
#print axioms rawStep_cartanOf

end AdalyFormal.CoverOmega
