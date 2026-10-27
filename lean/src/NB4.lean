import NB1
import NB2
import NB3
/-!
# NB4 -- linearisation of ONE blocked link (piece N4a)

If every bond `b` read by the blocking of `c` carries `W b = exp (A b)` with `A b ∈ 𝔰𝔲(2)`,
`‖A b‖_F ≤ k` and `8·ell·k ≤ 1/(8π)`, then

  `exp (log Ū_c) = Ū_c`  and  `‖log Ū_c − blkM s ell A c‖_F ≤ 200 π ell² k²`     (`log_ubar_lin`)

where `Ū_c = ubarSU2 s ell W c` and `blkM` is the linear (Lie-algebra) blocking of NB2.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarSU2_eq_blockedLink)
open AdalyFormal.Balaban.BlockingLinkEstimate (blockExponent)
open AdalyFormal.Balaban.Bch2 (IsSu2)

variable {L : PeriodicLatticeExtent}

theorem hol_eq_prod (s : ℕ) (W : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), (∀ b ∈ pathBonds s y p, W b = su2Exp (A b)) →
      coarsePathHolonomy s W y p = (((pathBonds s y p).map A).map su2Exp).prod := by
  intro p
  induction p with
  | nil => intro y _; rfl
  | cons μ rest ih =>
      intro y h
      show W (y, μ) * coarsePathHolonomy s W (coarseShift y s μ) rest = _
      rw [h _ (List.mem_cons_self ..), ih _ (fun b hb => h b (List.mem_cons_of_mem _ hb))]
      rfl

theorem sum_pathBonds (s : ℕ) (A : PeriodicLatticeEdge L → M2) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), ((pathBonds s y p).map A).sum = pathM s A y p := by
  intro p
  induction p with
  | nil => intro y; rfl
  | cons μ rest ih => intro y; simp only [pathBonds, List.map_cons, List.sum_cons, ih]; rfl

/-- Inverse of an exponential product. -/
theorem inv_prod_exp (l : List M2) (h : ∀ a ∈ l, IsSu2 a) :
    ((l.map su2Exp).prod)⁻¹ = (((l.map (fun a => -a)).reverse).map su2Exp).prod := by
  rw [List.prod_inv_reverse, List.map_map, List.map_reverse, List.map_map]
  congr 2
  refine List.map_congr_left (fun a ha => ?_)
  exact (su2Exp_neg_eq_inv (h a ha)).symm

theorem normsum_neg_rev (l : List M2) :
    (((l.map (fun a => -a)).reverse).map frobNorm).sum = (l.map frobNorm).sum := by
  rw [List.map_reverse, List.sum_reverse, List.map_map]
  congr 1
  refine List.map_congr_left (fun a _ => ?_)
  simp [Function.comp, AdalyFormal.Balaban.RegularityGap.frobNorm_neg]

theorem sum_neg_rev (l : List M2) : ((l.map (fun a => -a)).reverse).sum = -l.sum := by
  rw [List.sum_reverse]
  induction l with
  | nil => simp
  | cons a r ih => simp only [List.map_cons, List.sum_cons, ih]; abel

theorem normsum_le (l : List M2) (k : ℝ) (h : ∀ a ∈ l, frobNorm a ≤ k) :
    (l.map frobNorm).sum ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a r ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := h a (List.mem_cons_self ..)
      have := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
      push_cast; linarith

theorem length_pathBonds (s : ℕ) : ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L),
    (pathBonds s y p).length = p.length := by
  intro p; induction p with
  | nil => intro y; rfl
  | cons μ r ih => intro y; simp [pathBonds, ih]

theorem real_csmul (r : ℝ) (X : M2) : ((r : ℂ) • X) = r • X := by
  ext i j; simp [Matrix.smul_apply, Complex.real_smul]

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.hol_eq_prod
#print axioms AdalyFormal.CurvBlock.inv_prod_exp
