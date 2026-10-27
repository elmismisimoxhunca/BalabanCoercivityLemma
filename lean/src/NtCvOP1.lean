import NsCvO9
import NtCvOS12

/-!
# CvOP1 -- the (43)-averaging chain with a PARAMETER: joint analyticity in `(t, A)` (lane omega/near2/struct)

`ContDiffAt ℝ ⊤` is analyticity (`⊤ : WithTop ℕ∞` is `ω`; `contDiffAt_omega_iff_analyticAt`).
`SGat e0 G`: `e ↦ (G e : M₂)` is analytic at `e0`.  This repeats `R2RawX`/`CvO9` with an arbitrary base point `e0` of an arbitrary
parameter space `E` and a background family `V : E → Cfg`, a perturbation `B : E → XS L` with `B e0 = 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.CoverOmega (LogReg2 RegBg2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L : PeriodicLatticeExtent}

/-- `G : E → SU(2)` has analytic coercion at `e0`. -/
def SGat (e0 : E) (G : E → SU2) : Prop := ContDiffAt ℝ ⊤ (fun e => ((G e : SU2) : M2)) e0

theorem SGat.const (e0 : E) (g : SU2) : SGat e0 (fun _ : E => g) := contDiffAt_const

theorem SGat.mul {e0 : E} {G H : E → SU2} (hG : SGat e0 G) (hH : SGat e0 H) : SGat e0 (fun e => G e * H e) :=
  ContDiffAt.mul hG hH

theorem SGat.inv {e0 : E} {G : E → SU2} (hG : SGat e0 G) : SGat e0 (fun e => (G e)⁻¹) := by
  have h : (fun e => (((G e)⁻¹ : SU2) : M2)) = fun e => conjTR ((G e : SU2) : M2) := by
    funext e; rfl
  unfold SGat; rw [h]
  exact conjTR.contDiff.contDiffAt.comp e0 hG

theorem SGat.mul_inv {e0 : E} {G H : E → SU2} (hG : SGat e0 G) (hH : SGat e0 H) : SGat e0 (fun e => G e * (H e)⁻¹) :=
  hG.mul hH.inv

theorem SGat.hol (e0 : E) (s : ℕ) (V : E → PeriodicLinkConfiguration SU2 L)
    (hV : ∀ b, SGat e0 (fun e => V e b)) (p : List (Fin 3)) :
    ∀ y, SGat e0 (fun e => coarsePathHolonomy s (V e) y p) := by
  induction p with
  | nil => intro y; exact SGat.const e0 1
  | cons μ rest ih =>
      intro y
      exact (hV (y, μ)).mul (ih _)

theorem SGat_su2Exp {e0 : E} {S : E → M2} (hS : ContDiffAt ℝ ⊤ S e0) (hah : ∀ e, (S e)ᴴ = -S e)
    (htr : ∀ e, Matrix.trace (S e) = 0) : SGat e0 (fun e => su2Exp (S e)) := by
  have h : (fun e => ((su2Exp (S e) : SU2) : M2)) = fun e => NormedSpace.exp (S e) := by
    funext e; exact AdalyFormal.Balaban.SmoothLog.su2Exp_coe_of_mem_suTwo (hah e) (htr e)
  unfold SGat; rw [h]
  exact (NormedSpace.exp_analytic (S e0)).contDiffAt.comp e0 hS

theorem su2Log_comp_at {e0 : E} (G : E → SU2) (hG : SGat e0 G) (hG0 : ((G e0 : SU2) : M2) ∈ LogReg2) :
    ContDiffAt ℝ ⊤ (fun e => su2Log (G e)) e0 := by
  obtain ⟨F, hF, hev⟩ := hG0
  have hc : ContDiffAt ℝ ⊤ (fun e => F (G e : M2)) e0 := hF.comp e0 hG
  have hev' : (fun e => su2Log (G e)) =ᶠ[𝓝 e0] fun e => F (G e : M2) := by
    have ht : Tendsto (fun e => (G e : M2)) (𝓝 e0) (𝓝 ((G e0 : SU2) : M2)) := hG.continuousAt.tendsto
    filter_upwards [ht.eventually hev] with e hA
    exact hA (G e).2
  exact hc.congr_of_eventuallyEq hev'

theorem SGat_su2Exp_sum_log {e0 : E} {ι : Type*} (s : Finset ι) (q : ℚ) (G : ι → E → SU2)
    (hG : ∀ i ∈ s, SGat e0 (G i)) (hreg : ∀ i ∈ s, (((G i e0 : SU2)) : M2) ∈ LogReg2) :
    SGat e0 (fun e => su2Exp (∑ i ∈ s, q • su2Log (G i e))) := by
  refine SGat_su2Exp ?_ (fun e => (sum_qsmul_su2Log_mem s q (fun i => G i e)).1)
    (fun e => (sum_qsmul_su2Log_mem s q (fun i => G i e)).2)
  refine ContDiffAt.sum (fun i hi => ?_)
  simp only [qsmul_real]
  exact (su2Log_comp_at (G i) (hG i hi) (hreg i hi)).const_smul _

/-! ### the perturbation family -/

theorem SGat_expCfg {e0 : E} (B : E → XS L) (hB : ContDiffAt ℝ ⊤ B e0) (b : PeriodicLatticeEdge L) :
    SGat e0 (fun e => expCfgX (B e) b) := by
  have hS : ContDiffAt ℝ ⊤ (fun e => toM2L (B e b)) e0 :=
    toM2L.contDiff.contDiffAt.comp e0 ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) b).contDiff.contDiffAt.comp e0 hB)
  exact SGat_su2Exp (S := fun e => toM2L (B e b)) hS (fun e => (toM2_mem (B e b)).1) (fun e => (toM2_mem (B e b)).2)

theorem SGat_pc {e0 : E} (V : E → PeriodicLinkConfiguration SU2 L) (B : E → XS L)
    (hV : ∀ b, SGat e0 (fun e => V e b)) (hB : ContDiffAt ℝ ⊤ B e0) (b : PeriodicLatticeEdge L) :
    SGat e0 (fun e => prodCfgX (V e) (B e) b) :=
  (SGat_expCfg B hB b).mul (hV b)

theorem SGat_loopVar {e0 : E} (s ell : ℕ) (V : E → PeriodicLinkConfiguration SU2 L) (B : E → XS L)
    (hV : ∀ b, SGat e0 (fun e => V e b)) (hB : ContDiffAt ℝ ⊤ B e0) (c : PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) :
    SGat e0 (fun e => loopVar s ell (prodCfgX (V e) (B e)) c x) := by
  unfold loopVar gammaVarStrided coarseBondVar
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) =>
    SGat.hol e0 s (fun e => prodCfgX (V e) (B e)) (fun b => SGat_pc V B hV hB b) p y
  exact (((h _ _).mul (h _ _)).mul (h _ _).inv).mul (h _ _).inv

theorem SGat_avg_prod {e0 : E} (s ell : ℕ) (V : E → PeriodicLinkConfiguration SU2 L) (B : E → XS L)
    (hV : ∀ b, SGat e0 (fun e => V e b)) (hB : ContDiffAt ℝ ⊤ B e0) (hB0 : B e0 = 0)
    (hreg : RegBg2 s ell (V e0)) (c : PeriodicLatticeEdge L) :
    SGat e0 (fun e => stridedBlockedGauge su2LogExp s ell (prodCfgX (V e) (B e)) c) := by
  unfold stridedBlockedGauge
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) =>
    SGat.hol e0 s (fun e => prodCfgX (V e) (B e)) (fun b => SGat_pc V B hV hB b) p y
  refine SGat.mul ?_ (by unfold coarseBondVar; exact h _ _)
  have := SGat_su2Exp_sum_log (e0 := e0) (stepBlockOf c.1 s ell) (((ell : ℚ) ^ 3)⁻¹)
    (fun x e => loopVar s ell (prodCfgX (V e) (B e)) c x) (fun x _ => SGat_loopVar s ell V B hV hB c x)
    (fun x hx => by rw [hB0, prodCfgX_zero]; exact hreg c x hx)
  simpa [su2LogExp_log, su2LogExp_exp] using this

theorem SGat_avg_plain {e0 : E} (s ell : ℕ) (V : E → PeriodicLinkConfiguration SU2 L)
    (hV : ∀ b, SGat e0 (fun e => V e b)) (hreg : RegBg2 s ell (V e0)) (c : PeriodicLatticeEdge L) :
    SGat e0 (fun e => stridedBlockedGauge su2LogExp s ell (V e) c) := by
  have := SGat_avg_prod (e0 := e0) s ell V (fun _ => (0 : XS L)) hV contDiffAt_const rfl hreg c
  simpa [prodCfgX_zero] using this

theorem SGat_rProd {e0 : E} (s : ℕ) (V : E → PeriodicLinkConfiguration SU2 L) (B : E → XS L)
    (hV : ∀ b, SGat e0 (fun e => V e b)) (hB : ContDiffAt ℝ ⊤ B e0) (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) :
    SGat e0 (fun e => rProd s (V e) (expCfgX (B e)) y p) := by
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) =>
    SGat.hol e0 s (fun e => prodCfgX (V e) (B e)) (fun b => SGat_pc V B hV hB b) p y
  have h0 := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) =>
    SGat.hol e0 s V hV p y
  have : (fun e => rProd s (V e) (expCfgX (B e)) y p)
      = fun e => coarsePathHolonomy s (prodCfgX (V e) (B e)) y p * (coarsePathHolonomy s (V e) y p)⁻¹ := by
    funext e; exact rProd_eq s (V e) (expCfgX (B e)) y p
  rw [this]
  exact SGat.mul_inv (h p y) (h0 p y)

theorem SGat_su2Exp_sBlock {e0 : E} (s ell : ℕ) (V : E → PeriodicLinkConfiguration SU2 L) (B : E → XS L)
    (hV : ∀ b, SGat e0 (fun e => V e b)) (hB : ContDiffAt ℝ ⊤ B e0) (hB0 : B e0 = 0)
    (y : PeriodicLatticeSite L) :
    SGat e0 (fun e => su2Exp (sBlock s ell (V e) (expCfgX (B e)) y)) := by
  unfold sBlock
  exact SGat_su2Exp_sum_log (e0 := e0) (stepBlockOf y s ell) (((ell : ℚ) ^ 3)⁻¹)
    (fun x e => rProd s (V e) (expCfgX (B e)) y (coarseGammaPath s y x))
    (fun x _ => SGat_rProd s V B hV hB y _)
    (fun x _ => by
      show ((rProd s (V e0) (expCfgX (B e0)) y _ : SU2) : M2) ∈ LogReg2
      rw [hB0, rProd_expCfgX_zero]
      exact AdalyFormal.CoverOmega.LogReg_subset one_mem_LogReg)

theorem SGat_su2Exp_neg_sBlock {e0 : E} (s ell : ℕ) (V : E → PeriodicLinkConfiguration SU2 L) (B : E → XS L)
    (hV : ∀ b, SGat e0 (fun e => V e b)) (hB : ContDiffAt ℝ ⊤ B e0) (hB0 : B e0 = 0)
    (y : PeriodicLatticeSite L) :
    SGat e0 (fun e => su2Exp (-(sBlock s ell (V e) (expCfgX (B e)) y))) := by
  have := SGat_su2Exp_sum_log (e0 := e0) (stepBlockOf y s ell) (-((ell : ℚ) ^ 3)⁻¹)
    (fun x e => rProd s (V e) (expCfgX (B e)) y (coarseGammaPath s y x))
    (fun x _ => SGat_rProd s V B hV hB y _)
    (fun x _ => by
      show ((rProd s (V e0) (expCfgX (B e0)) y _ : SU2) : M2) ∈ LogReg2
      rw [hB0, rProd_expCfgX_zero]
      exact AdalyFormal.CoverOmega.LogReg_subset one_mem_LogReg)
  unfold sBlock
  simpa [neg_smul, Finset.sum_neg_distrib] using this

/-- **the raw one-step averaging is jointly analytic in the parameter and the perturbation.** -/
theorem SGat_rawStep {e0 : E} (s ell : ℕ) (V : E → PeriodicLinkConfiguration SU2 L) (B : E → XS L)
    (hV : ∀ b, SGat e0 (fun e => V e b)) (hB : ContDiffAt ℝ ⊤ B e0) (hB0 : B e0 = 0)
    (hreg : RegBg2 s ell (V e0)) (c : PeriodicLatticeEdge L) :
    SGat e0 (fun e => rawStep s ell (V e) (expCfgX (B e)) c) := by
  have e : (fun e => rawStep s ell (V e) (expCfgX (B e)) c)
      = fun e => su2Exp (-(sBlock s ell (V e) (expCfgX (B e)) c.1))
        * stridedBlockedGauge su2LogExp s ell (prodCfgX (V e) (B e)) c
        * su2Exp (sBlock s ell (V e) (expCfgX (B e)) (cPlusS s ell c))
        * (stridedBlockedGauge su2LogExp s ell (V e) c)⁻¹ := by
    funext e; exact rawStep_simp s ell (V e) (expCfgX (B e)) c
  unfold SGat at *; rw [e]
  have h1 := SGat_su2Exp_neg_sBlock s ell V B hV hB hB0 c.1
  have h2 := SGat_avg_prod s ell V B hV hB hB0 hreg c
  have h3 := SGat_su2Exp_sBlock s ell V B hV hB hB0 (cPlusS s ell c)
  have h4 := (SGat_avg_plain s ell V hV hreg c).inv
  exact ((h1.mul h2).mul h3).mul h4

/-- joint analyticity of the coordinate one-step map. -/
theorem qStepX_param {e0 : E} (s ell : ℕ) (V : E → PeriodicLinkConfiguration SU2 L) (B : E → XS L)
    (hV : ∀ b, SGat e0 (fun e => V e b)) (hB : ContDiffAt ℝ ⊤ B e0) (hB0 : B e0 = 0)
    (hreg : RegBg2 s ell (V e0)) (c : PeriodicLatticeEdge L) :
    ContDiffAt ℝ ⊤ (fun e => qStepX s ell (V e) (B e) c) e0 := by
  have h1 : ContDiffAt ℝ ⊤ (fun e => su2Log (rawStep s ell (V e) (expCfgX (B e)) c)) e0 :=
    su2Log_comp_at (G := fun e => rawStep s ell (V e) (expCfgX (B e)) c)
      (SGat_rawStep s ell V B hV hB hB0 hreg c)
      (by
        show ((rawStep s ell (V e0) (expCfgX (B e0)) c : SU2) : M2) ∈ LogReg2
        rw [hB0, expCfgX_zero]
        rw [rawStep_one_right]
        exact AdalyFormal.CoverOmega.LogReg_subset one_mem_LogReg)
  exact fromM2L.contDiff.contDiffAt.comp e0 h1

end AdalyFormal.CoverOmega.Struct
