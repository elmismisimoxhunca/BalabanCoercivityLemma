import ZLocJet

/-!
# CJ1 -- PER-ROW analyticity of the one-step averaging component

`R2RawX.qStepX_contDiffAt` needs `RegBg` at EVERY bond of the torus.  The component `c` alone
(`ZLocJet.qStepComp s ell V₀ c`) only reads the block loops `loopVar s ell V₀ c x`, `x ∈ B_s(c₋)`.
`RegRow s ell V₀ c` says those loops lie in `LogReg`; under it the component is analytic at `0`
(`qStepComp_contDiffAt_of_row`).  The proofs are the R2RawX proofs with the hypothesis restricted to the row.

Also: the universal chart radius `r0` (`ball 1 r0 ⊆ LogReg`), as in `nonflat_jet_20261009/NJ13bReg`
(re-proved here to keep the import cone small).
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.ClassJets

open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.SmoothLog (su2Log_comp_contDiffAt)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq)

variable {L : PeriodicLatticeExtent}

/-- the block loops of the row `c` lie in `LogReg`. -/
def RegRow (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L) : Prop :=
  ∀ x ∈ stepBlockOf c.1 s ell, ((loopVar s ell V0 c x : SU2) : M2) ∈ LogReg

/-- `RegBg` is `RegRow` at every row. -/
theorem regBg_iff_rows (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) :
    RegBg s ell V0 ↔ ∀ c, RegRow s ell V0 c := Iff.rfl

theorem SG_avg_prod_row (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L)
    (hreg : RegRow s ell V0 c) :
    SG (fun A : XS L => stridedBlockedGauge su2LogExp s ell (prodCfgX V0 A) c) := by
  unfold stridedBlockedGauge
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) =>
    SG.hol (E := XS L) s (fun A => prodCfgX V0 A) (fun b => SG_prodCfgX V0 b) p y
  refine SG.mul ?_ (by unfold coarseBondVar; exact h _ _)
  have := SG_su2Exp_sum_log (E := XS L) (stepBlockOf c.1 s ell) (((ell : ℚ) ^ 3)⁻¹)
    (fun x A => loopVar s ell (prodCfgX V0 A) c x) (fun x _ => SG_loopVar s ell V0 c x)
    (fun x hx => by rw [prodCfgX_zero]; exact hreg x hx)
  simpa [su2LogExp_log, su2LogExp_exp] using this

theorem SG_rawStep_row (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L)
    (hreg : RegRow s ell V0 c) :
    SG (fun A : XS L => rawStep s ell V0 (expCfgX A) c) := by
  have e : (fun A : XS L => rawStep s ell V0 (expCfgX A) c)
      = fun A => su2Exp (-(sBlock s ell V0 (expCfgX A) c.1))
        * stridedBlockedGauge su2LogExp s ell (prodCfgX V0 A) c
        * su2Exp (sBlock s ell V0 (expCfgX A) (cPlusS s ell c))
        * (stridedBlockedGauge su2LogExp s ell V0 c)⁻¹ := by
    funext A; exact rawStep_simp s ell V0 (expCfgX A) c
  unfold SG; rw [e]
  have h1 := SG_su2Exp_neg_sBlock s ell V0 c.1
  have h2 := SG_avg_prod_row s ell V0 c hreg
  have h3 := SG_su2Exp_sBlock s ell V0 (cPlusS s ell c)
  have h4 := SG_avg_const_inv s ell V0 c
  exact (((h1.mul h2).mul h3).mul h4)

/-- **PER-ROW ANALYTICITY.**  If the block loops of row `c` lie in `LogReg`, the component `c` of the one-step
averaging is `C^∞` at `0`. -/
theorem qStepComp_contDiffAt_of_row (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L)
    (hreg : RegRow s ell V0 c) : ContDiffAt ℝ ⊤ (qStepComp s ell V0 c) 0 := by
  have h1 : ContDiffAt ℝ ⊤ (fun a : XS L => su2Log (rawStep s ell V0 (expCfgX a) c)) 0 :=
    su2Log_comp_contDiffAt (G := fun a : XS L => rawStep s ell V0 (expCfgX a) c)
      (SG_rawStep_row s ell V0 c hreg) (rawStep_expCfgX_zero s ell V0 c)
  exact fromM2L.contDiff.contDiffAt.comp (0 : XS L) h1

/-- the row is differentiable at `0`, hence its `QlinStepL` row is a genuine derivative. -/
theorem qStepComp_hasFDerivAt_of_row (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L)
    (hreg : RegRow s ell V0 c) :
    HasFDerivAt (qStepComp s ell V0 c) (fderiv ℝ (qStepComp s ell V0 c) 0) 0 :=
  ((qStepComp_contDiffAt_of_row s ell V0 c hreg).differentiableAt (by simp)).hasFDerivAt

/-! ## the chart radius -/

theorem norm_frob_eq (M : Matrix (Fin 2) (Fin 2) ℂ) : ‖M‖ = frobNorm M := by
  rw [Matrix.frobenius_norm_def]
  unfold frobNorm frobSq
  simp only [Fin.sum_univ_two]
  rw [Real.sqrt_eq_rpow]
  congr 1
  have h : ∀ z : ℂ, ‖z‖ ^ (2 : ℝ) = Complex.normSq z := fun z => by
    rw [Real.rpow_two]; exact Complex.sq_norm z
  simp only [h]
  ring

theorem exists_r0 : ∃ r : ℝ, 0 < r ∧ ∀ g : M2, frobNorm (g - 1) < r → g ∈ LogReg := by
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp LogReg_mem_nhds_one
  refine ⟨r, hr, fun g hg => hb ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, norm_frob_eq]
  exact hg

/-- a radius of the analytic-log chart at `1` (non-explicit, positive). -/
noncomputable def r0 : ℝ := Classical.choose exists_r0

theorem r0_pos : 0 < r0 := (Classical.choose_spec exists_r0).1

theorem mem_LogReg_of_frob_lt {g : M2} (h : frobNorm (g - 1) < r0) : g ∈ LogReg :=
  (Classical.choose_spec exists_r0).2 g h

#print axioms qStepComp_contDiffAt_of_row
#print axioms qStepComp_hasFDerivAt_of_row
#print axioms mem_LogReg_of_frob_lt

end AdalyFormal.ClassJets
