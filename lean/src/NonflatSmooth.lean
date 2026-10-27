import LoopWords

/-!
Actual modifiedAverage smoothness, not a polynomial surrogate. In particular
all directions vary simultaneously in the native fine field. This is the
multivariate input needed for a derivative-of-remainder estimate, beyond SI1.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
attribute [local instance 20000] AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo
  AdalyFormal.Balaban.SuTwoInner.instInnerProductSpaceSuTwo
namespace HConstruction.SmallNFSmooth
open HConstruction.Predicate HConstruction.LocalLog
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
  (SU2 M2 su2Exp su2Log coe_mul coe_inv coe_one su2Log_antiHermitian
   su2Log_traceless su2Exp_coe_of_antiHerm_traceless)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf witnessL)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathHolonomy_trivialU)
open AdalyFormal.Balaban.UbarTowerCov (coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarSU2_trivialU)
open AdalySI1.ModifiedAverageDeriv
open AdalySI1.RawUbarDerivNoLoop (ubarBracket ubarSU2_eq_exp_bracket_mul_bondVar
  ubarBracket_conjTranspose ubarBracket_trace)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L : PeriodicLatticeExtent} {x : E}

noncomputable local instance : NormedAddCommGroup (Fine L) :=
  @Pi.normedAddCommGroup _ (fun _ : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 1 => SuTwo)
    inferInstance (fun _ => AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo)
noncomputable local instance : SeminormedAddCommGroup (Fine L) :=
  (inferInstance : NormedAddCommGroup (Fine L)).toSeminormedAddCommGroup
noncomputable local instance : NormedSpace ℝ (Fine L) :=
  @Pi.normedSpace ℝ _ _ (fun _ : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 1 => SuTwo)
    inferInstance (fun _ => AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo.toSeminormedAddCommGroup)
    (fun _ => AdalyFormal.Balaban.SuTwoInner.instInnerProductSpaceSuTwo.toNormedSpace)

private theorem smooth_mul {V W : E → SU2}
    (hV : ContDiffAt ℝ ⊤ (fun t => ((V t : SU2) : M2)) x)
    (hW : ContDiffAt ℝ ⊤ (fun t => ((W t : SU2) : M2)) x) :
    ContDiffAt ℝ ⊤ (fun t => ((V t * W t : SU2) : M2)) x := by
  simpa only [coe_mul] using hV.mul hW

private theorem smooth_inv {V : E → SU2}
    (hV : ContDiffAt ℝ ⊤ (fun t => ((V t : SU2) : M2)) x) :
    ContDiffAt ℝ ⊤ (fun t => (((V t)⁻¹ : SU2) : M2)) x := by
  have h := AdalySI1.L7.conjTransposeCLM.contDiff.contDiffAt.comp x hV
  change ContDiffAt ℝ ⊤ (fun t => (((V t : SU2) : M2))ᴴ) x at h
  simpa only [coe_inv] using h

private theorem smooth_conj {V W : E → SU2}
    (hV : ContDiffAt ℝ ⊤ (fun t => ((V t : SU2) : M2)) x)
    (hW : ContDiffAt ℝ ⊤ (fun t => ((W t : SU2) : M2)) x) :
    ContDiffAt ℝ ⊤ (fun t => ((groupConj (V t) (W t) : SU2) : M2)) x :=
  smooth_mul (smooth_mul hV hW) (smooth_inv hV)

private theorem smooth_exp {F : E → M2}
    (hF : ContDiffAt ℝ ⊤ F x)
    (hmem : ∀ t, (F t)ᴴ = -(F t) ∧ Matrix.trace (F t) = 0) :
    ContDiffAt ℝ ⊤ (fun t => ((su2Exp (F t) : SU2) : M2)) x := by
  have h := ((NormedSpace.exp_analytic (𝕂 := ℝ) (𝔸 := M2) (F x)).contDiffAt).comp x hF
  have heq : (fun t => ((su2Exp (F t) : SU2) : M2)) = fun t => NormedSpace.exp (F t) := by
    funext t
    exact su2Exp_coe_of_antiHerm_traceless (hmem t).1 (hmem t).2
  rw [heq]
  exact h

/-- Every finite ordered holonomy is smooth in all of its bond entries. -/
theorem smooth_coarsePath {V : E → PeriodicLinkConfiguration SU2 L}
    (hV : ∀ e, ContDiffAt ℝ ⊤ (fun t => ((V t e : SU2) : M2)) x)
    (s : ℕ) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    ContDiffAt ℝ ⊤ (fun t => ((coarsePathHolonomy s (V t) y p : SU2) : M2)) x := by
  induction p generalizing y with
  | nil => exact contDiffAt_const
  | cons mu p ih => exact smooth_mul (hV (y, mu)) (ih _)

private theorem smooth_loop {V : E → PeriodicLinkConfiguration SU2 L}
    (hV : ∀ e, ContDiffAt ℝ ⊤ (fun t => ((V t e : SU2) : M2)) x)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (y : PeriodicLatticeSite L) :
    ContDiffAt ℝ ⊤ (fun t => ((loopVar 1 ell (V t) c y : SU2) : M2)) x := by
  unfold loopVar gammaVarStrided coarseBondVar
  exact smooth_mul (smooth_mul (smooth_mul (smooth_coarsePath hV _ _ _)
    (smooth_coarsePath hV _ _ _)) (smooth_inv (smooth_coarsePath hV _ _ _)))
    (smooth_inv (smooth_coarsePath hV _ _ _))
/-- Background-specific loop guards, explicitly including noncentral loops. -/
theorem smooth_ubar_at_guard {V : E → PeriodicLinkConfiguration SU2 L}
    (hV : ∀ e, ContDiffAt ℝ ⊤ (fun t => ((V t e : SU2) : M2)) x)
    (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hg : ∀ y ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 1 ell,
      HConstruction.SmallNF.LogGuard (loopVar 1 ell (V x) c y)) :
    ContDiffAt ℝ ⊤ (fun t => ((ubarSU2 1 ell (V t) c : SU2) : M2)) x := by
  have hlog : ∀ y ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 1 ell,
      ContDiffAt ℝ ⊤ (fun t => su2Log (loopVar 1 ell (V t) c y)) x := by
    intro y hy
    exact HConstruction.SmallNF.log_smooth_guard (smooth_loop hV ell c y) (hg y hy)
  have hbr : ContDiffAt ℝ ⊤ (fun t => ubarBracket (V t) ell c) x := by
    unfold ubarBracket
    exact ContDiffAt.sum (fun y hy => (hlog y hy).const_smul _)
  have hex := smooth_exp hbr (fun t => ⟨ubarBracket_conjTranspose _ _ _, ubarBracket_trace _ _ _⟩)
  have hb := smooth_coarsePath hV 1 c.1 (List.replicate ell c.2)
  have heq : (fun t => ((ubarSU2 1 ell (V t) c : SU2) : M2)) =
      fun t => ((su2Exp (ubarBracket (V t) ell c) * coarseBondVar 1 ell (V t) c : SU2) : M2) := by
    funext t; rw [ubarSU2_eq_exp_bracket_mul_bondVar]
  rw [heq]
  exact smooth_mul hex hb

/-- Smoothness of the literal signed-path fold, with varying accumulated product. -/
private theorem smooth_rZero_fold (V0 : PeriodicLinkConfiguration SU2 L)
    {V : E → PeriodicLinkConfiguration SU2 L}
    (hV : ∀ e, ContDiffAt ℝ ⊤ (fun t => ((V t e : SU2) : M2)) x)
    (p : List (Fin 3 × Bool)) :
    ∀ (base : PeriodicLatticeSite L) (g : SU2) (prod : E → SU2),
      ContDiffAt ℝ ⊤ (fun t => ((prod t : SU2) : M2)) x →
      ContDiffAt ℝ ⊤ (fun t => ((
        (p.foldl (rZeroPathStep V0 (V t)) (base, g, prod t)).2.2 : SU2) : M2)) x := by
  induction p with
  | nil => intro base g prod hp; exact hp
  | cons step rest ih =>
    intro base g prod hp
    let next := periodicLatticeStep base step
    let bond : E → SU2 := fun t => if step.2 then V t (base, step.1)
      else groupConj (V0 (next, step.1))⁻¹ (V t (next, step.1))⁻¹
    have hb : ContDiffAt ℝ ⊤ (fun t => ((bond t : SU2) : M2)) x := by
      dsimp [bond]
      cases hs : step.2
      · exact smooth_conj contDiffAt_const (smooth_inv (hV _))
      · exact hV _
    have hnew := smooth_mul hp (smooth_conj (V := fun _ => g) contDiffAt_const hb)
    exact ih next (g * (if step.2 then V0 (base, step.1) else (V0 (next, step.1))⁻¹))
      (fun t => prod t * groupConj g (bond t)) hnew

private theorem smooth_rZero (V0 : PeriodicLinkConfiguration SU2 L)
    {V : E → PeriodicLinkConfiguration SU2 L}
    (hV : ∀ e, ContDiffAt ℝ ⊤ (fun t => ((V t e : SU2) : M2)) x)
    (base : PeriodicLatticeSite L) (p : List (Fin 3 × Bool)) :
    ContDiffAt ℝ ⊤ (fun t => ((rZeroPath V0 (V t) base p : SU2) : M2)) x :=
  smooth_rZero_fold V0 hV p base 1 (fun _ => 1) contDiffAt_const

/-- Both endpoint averages remain the actual nonlinear signed-path averages. -/
theorem smooth_endpoint_at_trivial (V0 : PeriodicLinkConfiguration SU2 L)
    {V : E → PeriodicLinkConfiguration SU2 L}
    (hV : ∀ e, ContDiffAt ℝ ⊤ (fun t => ((V t e : SU2) : M2)) x)
    (h0 : V x = trivialU L) (ell : ℕ) (y : PeriodicLatticeSite L) :
    ContDiffAt ℝ ⊤ (fun t => ((endpointAvg V0 (V t) ell y : SU2) : M2)) x := by
  have hlog : ∀ z, ContDiffAt ℝ ⊤
      (fun t => su2Log (rZeroPath V0 (V t) y (AdalyFormal.Balaban.Q1Real.GammaPath y z))) x := by
    intro z
    exact contDiffAt_log_at_one (smooth_rZero V0 hV y _)
      (by rw [h0, rZeroPath_trivialU_right])
  apply smooth_exp
  · exact ContDiffAt.sum (fun z hz => (hlog z).const_smul _)
  · intro t
    exact ⟨AdalySI1.RawUbarDerivNoLoop.sum_qsmul_su2Log_conjTranspose _ _ _,
      AdalySI1.RawUbarDerivNoLoop.sum_qsmul_su2Log_trace _ _ _⟩

/-- Actual normalized bond chart, with all fine coordinates varying at once. -/
noncomputable def bondExp (ell : ℕ) (A : Fine L) : PeriodicLinkConfiguration SU2 L :=
  fun e => su2Exp ((ell : ℝ)⁻¹ • AdalySI1.Multiscale.M2.unitBondDir A e)

@[simp] theorem bondExp_zero (ell : ℕ) : bondExp (L := L) ell 0 = trivialU L := by
  funext e
  simp [bondExp, AdalySI1.Multiscale.M2.unitBondDir, trivialU]

theorem smooth_bondExp (ell : ℕ) (e : PeriodicLatticeEdge L) :
    ContDiffAt ℝ ⊤ (fun A : Fine L => ((bondExp ell A e : SU2) : M2)) 0 := by
  let ev : Fine L →ₗ[ℝ] M2 := (suTwo.subtype).comp
    (LinearMap.proj (⟨e.1, AdalyFormal.Balaban.StridedAveraging.mem_coarseLattice_one e.1⟩, e.2))
  have he : ContDiffAt ℝ ⊤ (fun A : Fine L => AdalySI1.Multiscale.M2.unitBondDir A e) 0 :=
    ev.toContinuousLinearMap.contDiff.contDiffAt
  apply smooth_exp (he.const_smul _)
  intro A
  exact ⟨by simp [AdalySI1.Multiscale.M2.unitBondDir, Matrix.conjTranspose_smul,
      (A (⟨e.1, AdalyFormal.Balaban.StridedAveraging.mem_coarseLattice_one e.1⟩, e.2)).2.1],
    by simp [AdalySI1.Multiscale.M2.unitBondDir, Matrix.trace_smul,
      (A (⟨e.1, AdalyFormal.Balaban.StridedAveraging.mem_coarseLattice_one e.1⟩, e.2)).2.2]⟩
/-- C-infinity of the actual U-dependent map, not a polynomial replacement. -/
theorem actualQ_contDiffAt_guard (U : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (c : AdalyFormal.Balaban.LatticeOperators.CoarseBond L (1*ell))
    (hg : ∀ y ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf c.1.1 1 ell,
      HConstruction.SmallNF.LogGuard (loopVar 1 ell U (c.1.1,c.2) y)) :
    ContDiffAt ℝ ⊤ (fun A : Fine L => actualQ U ell A c) 0 := by
  have hV := smooth_bondExp (L := L) ell
  have hraw : ContDiffAt ℝ ⊤ (fun A : Fine L =>
      ((ubarSU2 1 ell (configMul (bondExp ell A) U) (c.1.1,c.2) : SU2) : M2)) 0 := by
    apply smooth_ubar_at_guard
    · intro e; exact smooth_mul (hV e) contDiffAt_const
    · rw [bondExp_zero,configMul_trivialU_left]; exact hg
  have hmod : ContDiffAt ℝ ⊤ (fun A : Fine L =>
      ((modifiedAverage U ell (bondExp ell A) (c.1.1,c.2) : SU2) : M2)) 0 := by
    exact smooth_mul
      (smooth_mul (smooth_inv (smooth_endpoint_at_trivial _ hV (bondExp_zero ell) ell c.1.1))
        (smooth_mul hraw contDiffAt_const))
      (smooth_conj contDiffAt_const (smooth_endpoint_at_trivial _ hV (bondExp_zero ell) ell _))
  apply contDiffAt_log_at_one hmod
  rw [bondExp_zero,modifiedAverage_trivialU]

theorem chosen_actualQ_smooth
    (c : AdalyFormal.Balaban.LatticeOperators.CoarseBond witnessL (1*2)) :
    ContDiffAt ℝ ⊤ (fun A : Fine witnessL => actualQ HConstruction.SmallNF.chosenU 2 A c) 0 :=
  actualQ_contDiffAt_guard _ _ _ (HConstruction.SmallNF.chosen_loop_guard c)
end HConstruction.SmallNFSmooth
