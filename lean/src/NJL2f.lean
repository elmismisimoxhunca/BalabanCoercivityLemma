import NJL2e
import NJ6Delta

/-!
# NJL2f -- (volume-free L2, step 5) the pointwise bound of `Δ_c` by the four absolute path sums, and `(Σ_path f)² ≤ |path| Σ_path f²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open AdalyFormal.Balaban.QOne (pathSite)
open OneStep124
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem list_sq_sum_le (l : List ℝ) : l.sum ^ 2 ≤ l.length * (l.map (fun x => x ^ 2)).sum := by
  induction l with
  | nil => simp
  | cons x rest ih =>
      simp only [List.sum_cons, List.length_cons, List.map_cons, Nat.cast_add, Nat.cast_one]
      set S := rest.sum with hS
      set T := (rest.map (fun x => x ^ 2)).sum with hT
      set n : ℝ := (rest.length : ℝ) with hn
      have hT0 : 0 ≤ T := List.sum_nonneg (fun y hy => by
        obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy; exact sq_nonneg z)
      have hn0 : 0 ≤ n := Nat.cast_nonneg _
      rcases hn0.eq_or_lt with h0 | hpos
      · rw [← h0] at ih ⊢
        have : S = 0 := by nlinarith [sq_nonneg S]
        rw [this]; nlinarith
      · have key : n * ((n + 1) * (x ^ 2 + T) - (x + S) ^ 2) ≥ 0 := by
          nlinarith [sq_nonneg (n * x - S), ih]
        have : (n + 1) * (x ^ 2 + T) - (x + S) ^ 2 ≥ 0 := by
          by_contra hneg
          push Not at hneg
          nlinarith [mul_pos hpos (neg_pos.mpr (sub_neg.mpr (by linarith : (x + S) ^ 2 > (n + 1) * (x ^ 2 + T) )))]
        nlinarith

/-- `(Σ_path f)² ≤ |path| · Σ_path f²`. -/
theorem pathSum_sq_le (f : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    (pathSum f y p) ^ 2 ≤ p.length * pathSum (fun e => f e ^ 2) y p := by
  unfold pathSum
  have := list_sq_sum_le ((bondsOf y p).map f)
  rw [List.length_map, bondsOf_length, List.map_map] at this
  simpa [Function.comp_def, List.map_map] using this

#print axioms list_sq_sum_le
#print axioms pathSum_sq_le

end AdalyFormal.NonflatJet
