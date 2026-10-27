import R7Fork.DM7d

/-!
# DM7e -- `Q*` is injective on `frakB` for EVERY admissible tower at flat `U` (equivalently `Q : E_0 -> L^2(frakB)` is onto).
Triangular argument: the private bond `d_j(b)` is read by its own row (positive coefficient), by no other row of level `j`
and by no row of a lower level; so testing `Q*f = 0` against `X (x) delta_{d(beta_0)}` at a top-level `beta_0` with `f(beta_0) != 0` gives `c |f(beta_0)|^2 = 0`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower Admissible)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ReparamCDisjoint (ReadsBond droppedBondLast droppedBondLast_reads_self)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.QOne (pathSite)

/-- the single-bond field `X (x) delta_d` -/
noncomputable def spike {L : PeriodicLatticeExtent} (d : Bond L) (X : SuTwo) : Bond L → SuTwo :=
  fun e => if e = d then X else 0

theorem lcr_spike_zero {L : PeriodicLatticeExtent} {n : ℕ} (c : CoarseBond L n) (d : Bond L) (X : SuTwo)
    (h : ¬ ReadsBond n c d) : lineCoarseRestrictSuTwo n (spike d X) c = 0 := by
  unfold lineCoarseRestrictSuTwo
  rw [Finset.sum_eq_zero, smul_zero]
  intro x hx
  refine Finset.sum_eq_zero (fun i hi => ?_)
  unfold spike
  rw [if_neg]
  intro hd
  exact h ⟨x, hx, i, hi, hd⟩

theorem lcr_spike_self {L : PeriodicLatticeExtent} {n : ℕ} (hn : 0 < n) (c : CoarseBond L n) (X : SuTwo) :
    ∃ r : ℝ, 0 < r ∧ lineCoarseRestrictSuTwo n (spike (droppedBondLast n c) X) c = r • X := by
  classical
  set d := droppedBondLast n c with hd
  set cnt : ℝ := ∑ x ∈ blockOf c.1.1 n, ∑ i ∈ Finset.range n,
    (if (pathSite x c.2 i, c.2) = d then (1 : ℝ) else 0) with hcnt
  have hcnt1 : 1 ≤ cnt := by
    have hself : ReadsBond n c d := droppedBondLast_reads_self hn c
    obtain ⟨x0, hx0, i0, hi0, hE⟩ := hself
    have h1 : (if (pathSite x0 c.2 i0, c.2) = d then (1 : ℝ) else 0) = 1 := by rw [if_pos hE]
    have h2 : (1 : ℝ) ≤ ∑ i ∈ Finset.range n, (if (pathSite x0 c.2 i, c.2) = d then (1 : ℝ) else 0) := by
      calc (1 : ℝ) = (if (pathSite x0 c.2 i0, c.2) = d then (1 : ℝ) else 0) := h1.symm
        _ ≤ _ := Finset.single_le_sum (f := fun i => (if (pathSite x0 c.2 i, c.2) = d then (1 : ℝ) else 0))
            (fun i _ => by split_ifs <;> norm_num) hi0
    calc (1 : ℝ) ≤ ∑ i ∈ Finset.range n, (if (pathSite x0 c.2 i, c.2) = d then (1 : ℝ) else 0) := h2
      _ ≤ cnt := Finset.single_le_sum
          (f := fun x => ∑ i ∈ Finset.range n, (if (pathSite x c.2 i, c.2) = d then (1 : ℝ) else 0))
          (fun x _ => Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)) hx0
  refine ⟨(1 / (n : ℝ) ^ 4) * cnt, by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity, ?_⟩
  unfold lineCoarseRestrictSuTwo
  have hsum : (∑ x ∈ blockOf c.1.1 n, ∑ i ∈ Finset.range n, spike d X (pathSite x c.2 i, c.2)) = cnt • X := by
    rw [hcnt, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold spike
    split_ifs <;> simp
  rw [hsum, smul_smul]

#print axioms lcr_spike_self

end AdalyFormal.DirichletMono
