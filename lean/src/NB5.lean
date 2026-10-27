import NB4
/-!
# NB5 -- linearisation of ONE blocked link (piece N4a)

If every bond `b` read by the blocking of `c` carries `W b = exp (A b)` with `A b ∈ 𝔰𝔲(2)`,
`‖A b‖_F ≤ k` and `8·ell·k ≤ 1/(8π)`, then `exp (log Ū_c) = Ū_c` and
`‖log Ū_c − blkM s ell A c‖_F ≤ 200 π ell² k²`  (`log_ubar_lin`), `Ū_c = ubarSU2 s ell W c`.

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

/-- Exponent list of a strided path. -/
def pl (s : ℕ) (A : PeriodicLatticeEdge L → M2) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    List M2 := (pathBonds s y p).map A

/-- Exponent list of the inverse path. -/
def plInv (s : ℕ) (A : PeriodicLatticeEdge L → M2) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    List M2 := ((pl s A y p).map (fun a => -a)).reverse

/-- Good bonds: chart with bound `k`. -/
def Chart (W : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2) (k : ℝ)
    (b : PeriodicLatticeEdge L) : Prop :=
  W b = su2Exp (A b) ∧ IsSu2 (A b) ∧ frobNorm (A b) ≤ k

theorem pl_facts (s : ℕ) (W : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2)
    (k : ℝ) (y : PeriodicLatticeSite L) (p : List (Fin 3))
    (h : ∀ b ∈ pathBonds s y p, Chart W A k b) :
    coarsePathHolonomy s W y p = ((pl s A y p).map su2Exp).prod ∧
    (coarsePathHolonomy s W y p)⁻¹ = ((plInv s A y p).map su2Exp).prod ∧
    (pl s A y p).sum = pathM s A y p ∧ (plInv s A y p).sum = -pathM s A y p ∧
    (∀ a ∈ pl s A y p, IsSu2 a) ∧ (∀ a ∈ plInv s A y p, IsSu2 a) ∧
    ((pl s A y p).map frobNorm).sum ≤ p.length * k ∧
    ((plInv s A y p).map frobNorm).sum ≤ p.length * k := by
  have hhol := hol_eq_prod s W A p y (fun b hb => (h b hb).1)
  have hsu : ∀ a ∈ pl s A y p, IsSu2 a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact (h b hb).2.1
  have hnorm : ((pl s A y p).map frobNorm).sum ≤ p.length * k := by
    have := normsum_le (pl s A y p) k (by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact (h b hb).2.2)
    rwa [pl, List.length_map, length_pathBonds] at this
  refine ⟨hhol, ?_, sum_pathBonds s A p y, ?_, hsu, ?_, hnorm, ?_⟩
  · rw [hhol]; exact inv_prod_exp _ hsu
  · unfold plInv; rw [sum_neg_rev, pl, sum_pathBonds]
  · intro a ha
    unfold plInv at ha
    rw [List.mem_reverse] at ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    exact (hsu a' ha').neg
  · unfold plInv; rw [normsum_neg_rev]; exact hnorm

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.pl_facts
