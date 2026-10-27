import DrEquiv

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## F. Jets of the raw averaging along a smooth family of backgrounds

The frozen `SG` calculus (`R2Raw3`, `R2RawX`) is stated over an arbitrary normed parameter space.
Taking the parameter space `ℝ × X` (curvature, coordinate field), the frozen proof of `SG_rawStep`
goes through with the background varying smoothly: the raw one-step averaging is jointly smooth in
(curvature, field) at `(0, 0)` whenever the background at curvature `0` is regular.  Its first and
second field derivatives at the zero field (the printed jets `QlinStepL`, `D2StepL`) are therefore
continuous in the curvature at `0` (`ContDiffAt.fderiv`). -/
section Jets

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS coarseBondVar gammaVarStrided loopVar)

variable {L : PeriodicLatticeExtent}

theorem tendsto_clm_of_apply' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : Type*} {l : Filter α} {f : α → E →L[ℝ] F} {f₀ : E →L[ℝ] F}
    (h : ∀ x, Tendsto (fun a => f a x) l (𝓝 (f₀ x))) : Tendsto f l (𝓝 f₀) := by
  let b := Module.finBasis ℝ E
  let c : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have e : ∀ g : E →L[ℝ] F, g = ∑ i, (c i).smulRight (g (b i)) := by
    intro g
    ext x
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, c,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul]
  rw [e f₀]
  have hf : f = fun a => ∑ i, (c i).smulRight (f a (b i)) := funext fun a => e (f a)
  rw [hf]
  refine tendsto_finsetSum _ (fun i _ => ?_)
  exact ((ContinuousLinearMap.smulRightL ℝ E F (c i)).continuous.tendsto _).comp (h (b i))

section Fam
variable (V : ℝ → PeriodicLinkConfiguration SU2 L)
  (hV : ∀ b, ContDiffAt ℝ ⊤ (fun ε => ((V ε b : SU2) : M2)) 0)

include hV in
theorem SG_V0 (b : PeriodicLatticeEdge L) : SG (fun q : ℝ × XS L => V q.1 b) := by
  show ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => ((V q.1 b : SU2) : M2)) 0
  exact ContDiffAt.comp (g := fun ε : ℝ => ((V ε b : SU2) : M2)) (f := fun q : ℝ × XS L => q.1)
    (0 : ℝ × XS L) (hV b) contDiffAt_fst

theorem SG_V1 (b : PeriodicLatticeEdge L) : SG (fun q : ℝ × XS L => expCfgX q.2 b) := by
  have h : ContDiffAt ℝ ⊤ (fun a : XS L => ((expCfgX a b : SU2) : M2)) 0 := SG_expCfgX b
  show ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => ((expCfgX q.2 b : SU2) : M2)) 0
  exact ContDiffAt.comp (g := fun a : XS L => ((expCfgX a b : SU2) : M2)) (f := fun q : ℝ × XS L => q.2)
    (0 : ℝ × XS L) h contDiffAt_snd

include hV in
theorem SG_prod (b : PeriodicLatticeEdge L) :
    SG (fun q : ℝ × XS L => expCfgX q.2 b * V q.1 b) :=
  (SG_V1 b).mul (SG_V0 V hV b)

theorem SG_loopVar_fam (s ell : ℕ) (W : ℝ × XS L → PeriodicLinkConfiguration SU2 L)
    (hW : ∀ b, SG (fun q => W q b)) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    SG (fun q => loopVar s ell (W q) c x) := by
  unfold loopVar gammaVarStrided coarseBondVar
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) => SG.hol s W hW p y
  exact (((h _ _).mul (h _ _)).mul (h _ _).inv).mul (h _ _).inv

theorem SG_sbg_fam (s ell : ℕ) (W : ℝ × XS L → PeriodicLinkConfiguration SU2 L)
    (hW : ∀ b, SG (fun q => W q b)) (c : PeriodicLatticeEdge L)
    (hreg : ∀ x ∈ stepBlockOf c.1 s ell, ((loopVar s ell (W 0) c x : SU2) : M2) ∈ LogReg) :
    SG (fun q => stridedBlockedGauge su2LogExp s ell (W q) c) := by
  unfold stridedBlockedGauge
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) => SG.hol s W hW p y
  refine SG.mul ?_ (by unfold coarseBondVar; exact h _ _)
  have := SG_su2Exp_sum_log (E := ℝ × XS L) (stepBlockOf c.1 s ell) (((ell : ℚ) ^ 3)⁻¹)
    (fun x q => loopVar s ell (W q) c x) (fun x _ => SG_loopVar_fam s ell W hW c x)
    (fun x hx => hreg x hx)
  simpa [su2LogExp_log, su2LogExp_exp] using this

include hV in
theorem SG_rProd_fam (s : ℕ) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    SG (fun q : ℝ × XS L => rProd s (V q.1) (expCfgX q.2) y p) := by
  have h1 := SG.hol (E := ℝ × XS L) s (fun q => fun b => expCfgX q.2 b * V q.1 b)
    (fun b => SG_prod V hV b) p y
  have h2 := SG.hol (E := ℝ × XS L) s (fun q => V q.1) (fun b => SG_V0 V hV b) p y
  have e : (fun q : ℝ × XS L => rProd s (V q.1) (expCfgX q.2) y p)
      = fun q => coarsePathHolonomy s (fun b => expCfgX q.2 b * V q.1 b) y p *
          (coarsePathHolonomy s (V q.1) y p)⁻¹ := by
    funext q
    exact rProd_eq s (V q.1) (expCfgX q.2) y p
  rw [e]
  exact SG.mul_inv h1 h2

include hV in
theorem SG_su2Exp_sBlock_fam (s ell : ℕ) (y : PeriodicLatticeSite L) :
    SG (fun q : ℝ × XS L => su2Exp (sBlock s ell (V q.1) (expCfgX q.2) y)) := by
  unfold sBlock
  exact SG_su2Exp_sum_log (E := ℝ × XS L) (stepBlockOf y s ell) (((ell : ℚ) ^ 3)⁻¹)
    (fun x q => rProd s (V q.1) (expCfgX q.2) y (coarseGammaPath s y x))
    (fun x _ => SG_rProd_fam V hV s y _)
    (fun x _ => by
      show ((rProd s (V 0) (expCfgX (0 : XS L)) y _ : SU2) : M2) ∈ LogReg
      rw [rProd_expCfgX_zero]; exact one_mem_LogReg)

include hV in
theorem SG_su2Exp_neg_sBlock_fam (s ell : ℕ) (y : PeriodicLatticeSite L) :
    SG (fun q : ℝ × XS L => su2Exp (-(sBlock s ell (V q.1) (expCfgX q.2) y))) := by
  have := SG_su2Exp_sum_log (E := ℝ × XS L) (stepBlockOf y s ell) (-((ell : ℚ) ^ 3)⁻¹)
    (fun x q => rProd s (V q.1) (expCfgX q.2) y (coarseGammaPath s y x))
    (fun x _ => SG_rProd_fam V hV s y _)
    (fun x _ => by
      show ((rProd s (V 0) (expCfgX (0 : XS L)) y _ : SU2) : M2) ∈ LogReg
      rw [rProd_expCfgX_zero]; exact one_mem_LogReg)
  unfold sBlock
  simpa [neg_smul, Finset.sum_neg_distrib] using this

include hV in
/-- The raw one-step averaging is jointly smooth in (curvature, field) at `(0, 0)`. -/
theorem SG_rawStep_fam (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    SG (fun q : ℝ × XS L => rawStep s ell (V q.1) (expCfgX q.2) c) := by
  have e : (fun q : ℝ × XS L => rawStep s ell (V q.1) (expCfgX q.2) c)
      = fun q => su2Exp (-(sBlock s ell (V q.1) (expCfgX q.2) c.1))
        * stridedBlockedGauge su2LogExp s ell (fun b => expCfgX q.2 b * V q.1 b) c
        * su2Exp (sBlock s ell (V q.1) (expCfgX q.2) (cPlusS s ell c))
        * (stridedBlockedGauge su2LogExp s ell (V q.1) c)⁻¹ := by
    funext q; exact rawStep_simp s ell (V q.1) (expCfgX q.2) c
  unfold SG; rw [e]
  have h1 := SG_su2Exp_neg_sBlock_fam V hV s ell c.1
  have h2 : SG (fun q : ℝ × XS L =>
      stridedBlockedGauge su2LogExp s ell (fun b => expCfgX q.2 b * V q.1 b) c) := by
    refine SG_sbg_fam s ell (fun q => fun b => expCfgX q.2 b * V q.1 b) (fun b => SG_prod V hV b) c ?_
    intro x hx
    have e0 : (fun b => expCfgX (0 : XS L) b * V 0 b) = V 0 := by
      funext b; rw [expCfgX_zero]; exact one_mul _
    show ((loopVar s ell (fun b => expCfgX ((0 : ℝ × XS L).2) b * V ((0 : ℝ × XS L).1) b) c x : SU2) : M2)
      ∈ LogReg
    rw [show ((0 : ℝ × XS L).2) = (0 : XS L) from rfl, show ((0 : ℝ × XS L).1) = (0 : ℝ) from rfl, e0]
    exact hreg c x hx
  have h3 := SG_su2Exp_sBlock_fam V hV s ell (cPlusS s ell c)
  have h4 : SG (fun q : ℝ × XS L => (stridedBlockedGauge su2LogExp s ell (V q.1) c)⁻¹) := by
    refine SG.inv (SG_sbg_fam s ell (fun q => V q.1) (fun b => SG_V0 V hV b) c ?_)
    intro x hx
    exact hreg c x hx
  exact (((h1.mul h2).mul h3).mul h4)

include hV in
theorem contDiffAt_qStep_fam (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => qStepX s ell (V q.1) q.2 c) 0 := by
  have h1 : ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => su2Log (rawStep s ell (V q.1) (expCfgX q.2) c)) 0 :=
    AdalyFormal.Balaban.SmoothLog.su2Log_comp_contDiffAt
      (G := fun q : ℝ × XS L => rawStep s ell (V q.1) (expCfgX q.2) c)
      (SG_rawStep_fam V hV s ell hreg c) (rawStep_expCfgX_zero s ell (V 0) c)
  exact fromM2L.contDiff.contDiffAt.comp (0 : ℝ × XS L) h1

include hV in
/-- First jet: continuity in the curvature of the field derivative at the zero field. -/
theorem continuousAt_fderiv_qStep (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    ContinuousAt (fun ε => fderiv ℝ (qStepComp s ell (V ε) c) 0) 0 := by
  have h := contDiffAt_qStep_fam V hV s ell hreg c
  have h2 : ContDiffAt ℝ 0 (fun ε : ℝ => fderiv ℝ (fun a : XS L => qStepX s ell (V ε) a c)
      ((fun _ : ℝ => (0 : XS L)) ε)) 0 :=
    ContDiffAt.fderiv (f := fun (ε : ℝ) (a : XS L) => qStepX s ell (V ε) a c)
      (g := fun _ : ℝ => (0 : XS L)) h contDiffAt_const (by simp)
  exact h2.continuousAt

include hV in
/-- Second jet: continuity in the curvature of the second field derivative at the zero field. -/
theorem continuousAt_fderiv2_qStep (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    ContinuousAt (fun ε => fderiv ℝ (fderiv ℝ (qStepComp s ell (V ε) c)) 0) 0 := by
  have h := contDiffAt_qStep_fam V hV s ell hreg c
  have hl : ContDiffAt ℝ ⊤ (fun z : (ℝ × XS L) × XS L => ((z.1.1, z.2) : ℝ × XS L))
      ((0 : ℝ × XS L), (0 : XS L)) :=
    (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hΦ' : ContDiffAt ℝ ⊤ ((fun q : ℝ × XS L => qStepX s ell (V q.1) q.2 c) ∘
      (fun z : (ℝ × XS L) × XS L => ((z.1.1, z.2) : ℝ × XS L))) ((0 : ℝ × XS L), (0 : XS L)) :=
    ContDiffAt.comp (g := fun q : ℝ × XS L => qStepX s ell (V q.1) q.2 c)
      (f := fun z : (ℝ × XS L) × XS L => ((z.1.1, z.2) : ℝ × XS L)) ((0 : ℝ × XS L), (0 : XS L)) h hl
  have hΦ : ContDiffAt ℝ ⊤ (Function.uncurry fun (x : ℝ × XS L) (b : XS L) =>
      qStepX s ell (V x.1) b c) ((0 : ℝ × XS L), (fun x : ℝ × XS L => x.2) 0) := hΦ'
  have hΨ : ContDiffAt ℝ ⊤ (fun x : ℝ × XS L =>
      fderiv ℝ (fun b : XS L => qStepX s ell (V x.1) b c) x.2) 0 :=
    ContDiffAt.fderiv (f := fun (x : ℝ × XS L) (b : XS L) => qStepX s ell (V x.1) b c)
      (g := fun x : ℝ × XS L => x.2) hΦ contDiffAt_snd (by simp)
  have h2 : ContDiffAt ℝ 0 (fun ε : ℝ => fderiv ℝ (fun a : XS L =>
      fderiv ℝ (fun b : XS L => qStepX s ell (V ε) b c) a) ((fun _ : ℝ => (0 : XS L)) ε)) 0 :=
    ContDiffAt.fderiv (f := fun (ε : ℝ) (a : XS L) =>
        fderiv ℝ (fun b : XS L => qStepX s ell (V ε) b c) a)
      (g := fun _ : ℝ => (0 : XS L)) hΨ contDiffAt_const (by simp)
  exact h2.continuousAt

end Fam

end Jets

end AdalyFormal.Round9.Guarded.AnalyticR2
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_fderiv2_qStep
