import R2RawX
import CvO4

/-!
# CvO9 -- smoothness of `su2Log` away from `-1`, and the regular-background chain with `RegBg2` (lane omega)

`LogReg2`: `g ∈ M₂(ℂ)` near which `su2Log` agrees with SOME analytic function.  It contains `LogReg` (a neighbourhood of `1`) and EVERY
`g ∈ SU(2)` with `g ≠ -1` (closed form `κ(arccos(Re tr g / 2)) (g - gᴴ)/2`, `κ(θ) = θ/sin θ`, analytic on `|Re tr g/2| < 1`).
`RegBg2` replaces `RegBg` (all loop holonomies in `LogReg`) by "all loop holonomies in `LogReg2`", and the chain
`SG_avg_prod → SG_rawStep → qStepX_contDiffAt → qCompX_contDiffAt → QlinCompX_succ / C2CompX_succ` of `R2RawX` is repeated verbatim.
This removes the "background near the identity" restriction of the tree's smoothness machinery (lane cover_jacobi NOTES, finding of round 10).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2

/-- real part of half the trace -/
noncomputable def a0F (g : M2) : ℝ := (Matrix.trace g).re / 2

theorem a0F_contDiff : ContDiff ℝ ⊤ a0F := by
  have h : a0F = fun g : M2 => (Matrix.trace g).re / 2 := rfl
  let T : M2 →ₗ[ℝ] ℝ :=
    { toFun := fun g => (Matrix.trace g).re / 2
      map_add' := fun g h => by simp [Matrix.trace_add]; ring
      map_smul' := fun r g => by simp [Matrix.trace_smul]; ring }
  have hT : (T : M2 → ℝ) = a0F := rfl
  rw [← hT]
  exact (LinearMap.toContinuousLinearMap T).contDiff

/-- `g ↦ gᴴ` as a continuous real-linear map. -/
noncomputable def conjTL : M2 →L[ℝ] M2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => gᴴ
      map_add' := fun g h => Matrix.conjTranspose_add g h
      map_smul' := fun r g => by
        ext i j; simp [Matrix.conjTranspose_apply] }

/-- the closed form of `su2Log` -/
noncomputable def logF (g : M2) : M2 :=
  (((Real.arccos (a0F g) / Real.sqrt (1 - a0F g ^ 2) : ℝ) : ℂ) / 2) • (g - gᴴ)

theorem logF_contDiffAt (g0 : M2) (h : |a0F g0| < 1) : ContDiffAt ℝ ⊤ logF g0 := by
  have h1 : a0F g0 ≠ -1 := by intro e; rw [e] at h; simp at h
  have h2 : a0F g0 ≠ 1 := by intro e; rw [e] at h; simp at h
  have hpos : 0 < 1 - a0F g0 ^ 2 := by
    have := abs_lt.mp h; nlinarith [this.1, this.2]
  have ha : ContDiffAt ℝ ⊤ a0F g0 := a0F_contDiff.contDiffAt
  have harc : ContDiffAt ℝ ⊤ (fun g => Real.arccos (a0F g)) g0 :=
    (Real.contDiffAt_arccos h1 h2).comp g0 ha
  have hsq : ContDiffAt ℝ ⊤ (fun g => Real.sqrt (1 - a0F g ^ 2)) g0 := by
    have hin : ContDiffAt ℝ ⊤ (fun g => 1 - a0F g ^ 2) g0 := contDiffAt_const.sub (ha.pow 2)
    exact (Real.contDiffAt_sqrt hpos.ne').comp g0 hin
  have hdiv : ContDiffAt ℝ ⊤ (fun g => Real.arccos (a0F g) / Real.sqrt (1 - a0F g ^ 2)) g0 :=
    harc.div hsq (Real.sqrt_pos.mpr hpos).ne'
  have hc : ContDiffAt ℝ ⊤ (fun g => (((Real.arccos (a0F g) / Real.sqrt (1 - a0F g ^ 2) : ℝ) : ℂ) / 2)) g0 :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp g0 hdiv).div_const 2
  have hm : ContDiffAt ℝ ⊤ (fun g : M2 => g - gᴴ) g0 := contDiffAt_id.sub conjTL.contDiff.contDiffAt
  exact hc.smul hm

theorem su2Log_eq_logF (g : SU2) : su2Log g = logF (g : M2) := by
  unfold su2Log su2Kappa su2Angle logF a0F
  rw [Real.sin_arccos]

/-- points where `su2Log` is locally some analytic function. -/
def LogReg2 : Set M2 :=
  {g | ∃ F : M2 → M2, ContDiffAt ℝ ⊤ F g ∧ ∀ᶠ g' in 𝓝 g, ∀ h : g' ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, su2Log ⟨g', h⟩ = F g'}

theorem LogReg_subset : LogReg ⊆ LogReg2 := fun _ hg => ⟨_, hg.1, hg.2⟩

/-- every `g ∈ SU(2)`, `g ≠ -1` has `su2Log` locally analytic. -/
theorem mem_LogReg2_of_ne_negOne (g : SU2) (hg : g ≠ su2NegOne) : (g : M2) ∈ LogReg2 := by
  by_cases h1 : g = 1
  · subst h1
    exact LogReg_subset one_mem_LogReg
  · have hs := sin_su2Angle_ne_zero g h1 hg
    have hlt : |a0F (g : M2)| < 1 := by
      have : su2Angle g = Real.arccos (a0F (g : M2)) := rfl
      rw [this, Real.sin_arccos] at hs
      have hp : 0 < 1 - a0F (g : M2) ^ 2 := Real.sqrt_ne_zero'.mp hs
      exact (sq_lt_one_iff_abs_lt_one _).mp (by linarith)
    exact ⟨logF, logF_contDiffAt _ hlt, Filter.Eventually.of_forall (fun g' h' => su2Log_eq_logF ⟨g', h'⟩)⟩


open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.SmoothLog (su2Log_comp_contDiffAt fderiv_fderiv_comp)

variable {L : PeriodicLatticeExtent}

/-- `su2Log ∘ G` is smooth at `0` whenever `G` is smooth at `0` with `G 0` in `LogReg2`. -/
theorem su2Log_comp_contDiffAt_reg2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → SU2) {n : WithTop ℕ∞} (hn : n ≤ ⊤)
    (hG : ContDiffAt ℝ n (fun A => (G A : M2)) 0) (hG0 : ((G 0 : SU2) : M2) ∈ LogReg2) :
    ContDiffAt ℝ n (fun A => su2Log (G A)) 0 := by
  obtain ⟨F, hF, hev⟩ := hG0
  have hL : ContDiffAt ℝ n F ((G 0 : SU2) : M2) := hF.of_le hn
  have hc : ContDiffAt ℝ n (fun A => F (G A : M2)) 0 := hL.comp (0 : E) hG
  have hev' : (fun A => su2Log (G A)) =ᶠ[𝓝 0] fun A => F (G A : M2) := by
    have ht : Tendsto (fun A => (G A : M2)) (𝓝 0) (𝓝 ((G 0 : SU2) : M2)) := hG.continuousAt.tendsto
    filter_upwards [ht.eventually hev] with A hA
    exact hA (G A).2
  exact hc.congr_of_eventuallyEq hev'

/-- A background is REGULAR2 when every loop holonomy of the (43)-average lies in `LogReg2`. -/
def RegBg2 (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) : Prop :=
  ∀ (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L), x ∈ stepBlockOf c.1 s ell →
    ((loopVar s ell V0 c x : SU2) : M2) ∈ LogReg2

/-- `RegBg2` holds as soon as no loop holonomy is `-1`. -/
theorem regBg2_of_ne_negOne (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L)
    (h : ∀ (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L), x ∈ stepBlockOf c.1 s ell → loopVar s ell V0 c x ≠ su2NegOne) :
    RegBg2 s ell V0 := fun c x hx => mem_LogReg2_of_ne_negOne _ (h c x hx)

theorem RegBg2_of_RegBg {s ell : ℕ} {V0 : PeriodicLinkConfiguration SU2 L} (h : RegBg s ell V0) : RegBg2 s ell V0 :=
  fun c x hx => LogReg_subset (h c x hx)

/-- `A ↦ su2Exp (Σ_x q • su2Log (G_x A))` is analytic at `0` when each `G_x` is analytic at `0`
with `G_x 0` in `LogReg`. -/
theorem SG_su2Exp_sum_log2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (s : Finset ι) (q : ℚ) (G : ι → E → SU2) (hG : ∀ i ∈ s, SG (G i))
    (hreg : ∀ i ∈ s, (((G i 0 : SU2)) : M2) ∈ LogReg2) :
    SG (fun A => su2Exp (∑ i ∈ s, q • su2Log (G i A))) := by
  refine SG_su2Exp ?_ (fun A => (sum_qsmul_su2Log_mem s q (fun i => G i A)).1)
    (fun A => (sum_qsmul_su2Log_mem s q (fun i => G i A)).2)
  refine ContDiffAt.sum (fun i hi => ?_)
  simp only [qsmul_real]
  exact (su2Log_comp_contDiffAt_reg2 (G i) le_rfl (hG i hi) (hreg i hi)).const_smul _



/-- the (43)-average of `V₁V₀` is analytic at `A = 0` on a regular background. -/
theorem SG_avg_prod2 (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (hreg : RegBg2 s ell V0)
    (c : PeriodicLatticeEdge L) :
    SG (fun A : XS L => stridedBlockedGauge su2LogExp s ell (prodCfgX V0 A) c) := by
  unfold stridedBlockedGauge
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) =>
    SG.hol (E := XS L) s (fun A => prodCfgX V0 A) (fun b => SG_prodCfgX V0 b) p y
  refine SG.mul ?_ (by unfold coarseBondVar; exact h _ _)
  have := SG_su2Exp_sum_log2 (E := XS L) (stepBlockOf c.1 s ell) (((ell : ℚ) ^ 3)⁻¹)
    (fun x A => loopVar s ell (prodCfgX V0 A) c x) (fun x _ => SG_loopVar s ell V0 c x)
    (fun x hx => by rw [prodCfgX_zero]; exact hreg c x hx)
  simpa [su2LogExp_log, su2LogExp_exp] using this


/-- THE RAW ONE-STEP AVERAGING IS ANALYTIC AT `A = 0` ON A REGULAR BACKGROUND. -/
theorem SG_rawStep2 (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (hreg : RegBg2 s ell V0)
    (c : PeriodicLatticeEdge L) :
    SG (fun A : XS L => rawStep s ell V0 (expCfgX A) c) := by
  have e : (fun A : XS L => rawStep s ell V0 (expCfgX A) c)
      = fun A => su2Exp (-(sBlock s ell V0 (expCfgX A) c.1))
        * stridedBlockedGauge su2LogExp s ell (prodCfgX V0 A) c
        * su2Exp (sBlock s ell V0 (expCfgX A) (cPlusS s ell c))
        * (stridedBlockedGauge su2LogExp s ell V0 c)⁻¹ := by
    funext A; exact rawStep_simp s ell V0 (expCfgX A) c
  unfold SG; rw [e]
  have h1 := SG_su2Exp_neg_sBlock s ell V0 c.1
  have h2 := SG_avg_prod2 s ell V0 hreg c
  have h3 := SG_su2Exp_sBlock s ell V0 (cPlusS s ell c)
  have h4 := SG_avg_const_inv s ell V0 c
  exact (((h1.mul h2).mul h3).mul h4)


theorem qStepX_contDiffAt2 (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L)
    (hreg : RegBg2 s ell V0) : ContDiffAt ℝ ⊤ (qStepX s ell V0) 0 := by
  refine contDiffAt_pi.mpr (fun c => ?_)
  have h1 : ContDiffAt ℝ ⊤ (fun a : XS L => su2Log (rawStep s ell V0 (expCfgX a) c)) 0 :=
    su2Log_comp_contDiffAt (G := fun a : XS L => rawStep s ell V0 (expCfgX a) c)
      (SG_rawStep2 s ell V0 hreg c) (rawStep_expCfgX_zero s ell V0 c)
  exact fromM2L.contDiff.contDiffAt.comp (0 : XS L) h1


/-- regularity of the background tower up to level `J` (the smallness hypothesis of p.428). -/
def RegTower2 (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ) : Prop :=
  ∀ j, j < J → RegBg2 (ell ^ j) ell (bg j)

theorem qCompX_contDiffAt2 (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower2 ell bg J) : ∀ j, j ≤ J → ContDiffAt ℝ ⊤ (qCompX ell bg j) 0 := by
  intro j
  induction j with
  | zero => intro _; exact contDiffAt_id
  | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := qStepX_contDiffAt2 (ell ^ j) ell (bg j) (hreg j (by omega))
      have h2' : ContDiffAt ℝ ⊤ (qStepX (ell ^ j) ell (bg j)) (qCompX ell bg j 0) := by
        rw [qCompX_zero]; exact h2
      exact h2'.comp (0 : XS L) h1


/-- CHAIN RULE: `Q_{j+1} = Q(Ū^j) Q_j`, i.e. the printed composite (3.15). -/
theorem QlinCompX_succ2 (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower2 ell bg J) (j : ℕ) (hj : j < J) :
    QlinCompX ell bg (j + 1) = (QlinStepX (ell ^ j) ell (bg j)).comp (QlinCompX ell bg j) := by
  have h1 := qCompX_contDiffAt2 ell bg J hreg j hj.le
  have h2 := qStepX_contDiffAt2 (ell ^ j) ell (bg j) (hreg j hj)
  have h2' : ContDiffAt ℝ ⊤ (qStepX (ell ^ j) ell (bg j)) (qCompX ell bg j 0) := by
    rw [qCompX_zero]; exact h2
  have hd1 : DifferentiableAt ℝ (qCompX ell bg j) 0 := h1.differentiableAt (by simp)
  have hd2 : DifferentiableAt ℝ (qStepX (ell ^ j) ell (bg j)) (qCompX ell bg j 0) :=
    h2'.differentiableAt (by simp)
  unfold QlinCompX QlinStepX
  show fderiv ℝ (qStepX (ell ^ j) ell (bg j) ∘ qCompX ell bg j) 0 = _
  rw [fderiv_comp (0 : XS L) hd2 hd1, qCompX_zero]

/-- SECOND-ORDER CHAIN RULE: `C_{j+1}(a) = Q(Ū^j) C_j(a) + C(Ū^j, Q_j a)`. -/
theorem C2CompX_succ2 (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower2 ell bg J) (j : ℕ) (hj : j < J) (a : XS L) :
    C2CompX ell bg (j + 1) a
      = QlinStepX (ell ^ j) ell (bg j) (C2CompX ell bg j a)
        + C2StepX (ell ^ j) ell (bg j) (QlinCompX ell bg j a) := by
  have h1 := qCompX_contDiffAt2 ell bg J hreg j hj.le
  have h2 := qStepX_contDiffAt2 (ell ^ j) ell (bg j) (hreg j hj)
  have h2' : ContDiffAt ℝ ⊤ (qStepX (ell ^ j) ell (bg j)) (qCompX ell bg j 0) := by
    rw [qCompX_zero]; exact h2
  have hc := fderiv_fderiv_comp (qStepX (ell ^ j) ell (bg j)) (qCompX ell bg j) (0 : XS L)
    (h2'.of_le (by simp)) (h1.of_le (by simp)) a a
  unfold C2CompX C2StepX QlinCompX QlinStepX
  show (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (qStepX (ell ^ j) ell (bg j) ∘ qCompX ell bg j)) 0 a a = _
  rw [hc, qCompX_zero]
  simp only [map_smul, smul_add]
  abel


#print axioms su2Log_comp_contDiffAt_reg2
#print axioms regBg2_of_ne_negOne
#print axioms SG_su2Exp_sum_log2
#print axioms SG_avg_prod2
#print axioms SG_rawStep2
#print axioms qStepX_contDiffAt2
#print axioms qCompX_contDiffAt2
#print axioms QlinCompX_succ2
#print axioms C2CompX_succ2

end AdalyFormal.CoverOmega
