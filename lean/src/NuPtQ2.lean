import NuPtQ1

/-!
# PtQ2 -- single-bond test fields and the coefficient of `lineCoarseRestrictSuTwo` (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmegaTwo
open AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)

section single
variable {L : PeriodicLatticeExtent}

theorem pathSite_ne (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) (i : ℕ) : pathSite x μ i ν = x ν := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pathSite_succ, shift_val_ne _ _ _ h, ih]

theorem pathSite_self_val (x : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) :
    ((pathSite x μ i) μ).val = ((x μ).val + i) % (L μ + 1) := by
  induction i with
  | zero => simp [pathSite_zero, Nat.mod_eq_of_lt (x μ).isLt]
  | succ i ih =>
    rw [pathSite_succ, shift_val_self, ih, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, ← add_assoc]

/-- the field supported on one bond. -/
noncomputable def dB (β : Bond L) (v : SuTwo) : BondFnL2 L :=
  WithLp.toLp 2 (fun b => if b = β then v else 0)

theorem dB_apply (β : Bond L) (v : SuTwo) (b : Bond L) : (WithLp.ofLp (dB β v)) b = if b = β then v else 0 := rfl

/-- number of hits of the line sum of the row `(Y,μ)` at length `n` on the bond `β`. -/
noncomputable def hits (Y : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) (β : Bond L) : ℕ :=
  (((blockOf Y n) ×ˢ (range n)).filter (fun q => (pathSite q.1 μ q.2, μ) = β)).card

theorem lcr_single (Y : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) (hc : Y ∈ CoarseLattice L n)
    (β : Bond L) (v : SuTwo) :
    lineCoarseRestrictSuTwo n (WithLp.ofLp (dB β v)) ⟨⟨Y, hc⟩, μ⟩ = ((1 / (n : ℝ) ^ 4) * (hits Y μ n β : ℝ)) • v := by
  unfold lineCoarseRestrictSuTwo hits
  classical
  have : ∑ x ∈ blockOf Y n, ∑ i ∈ range n, (WithLp.ofLp (dB β v)) (pathSite x μ i, μ)
      = ∑ q ∈ (blockOf Y n) ×ˢ (range n), (if (pathSite q.1 μ q.2, μ) = β then v else 0) := by
    rw [Finset.sum_product]
    rfl
  show (1 / (n : ℝ) ^ 4) • ∑ x ∈ blockOf Y n, ∑ i ∈ range n, (WithLp.ofLp (dB β v)) (pathSite x μ i, μ) = _
  rw [this, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]

theorem hits_pos (Y : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) (hn : 0 < n) :
    0 < hits Y μ n (pathSite Y μ (n - 1), μ) := by
  unfold hits
  apply Finset.card_pos.mpr
  refine ⟨(Y, n - 1), ?_⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  refine ⟨⟨?_, by omega⟩, by simp⟩
  rw [mem_blockOf]
  intro ν
  exact ⟨le_rfl, by omega⟩

theorem hit_extract (Y' : PeriodicLatticeSite L) (μ' μ : Fin 3) (n n' : ℕ) (Y : PeriodicLatticeSite L)
    (hit : 0 < hits Y' μ' n' (pathSite Y μ (n - 1), μ)) :
    μ' = μ ∧ ∃ y : PeriodicLatticeSite L, (∀ ν, (Y' ν).val ≤ (y ν).val ∧ (y ν).val < (Y' ν).val + n') ∧
      ∃ i, i < n' ∧ (∀ ν, ν ≠ μ → (y ν).val = (Y ν).val) ∧
        ((y μ).val + i) % (L μ + 1) = ((Y μ).val + (n - 1)) % (L μ + 1) := by
  unfold hits at hit
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hit
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
  obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hq
  have hμ : μ' = μ := congrArg Prod.snd hq3
  subst hμ
  have hs : pathSite q.1 μ' q.2 = pathSite Y μ' (n - 1) := congrArg Prod.fst hq3
  refine ⟨rfl, q.1, (mem_blockOf.mp hq1), q.2, hq2, ?_, ?_⟩
  · intro ν hν
    have := congrArg (fun z => z ν) hs
    simp only [pathSite_ne _ _ _ hν] at this
    rw [this]
  · have := congrArg (fun z => (z μ').val) hs
    simp only [pathSite_self_val] at this
    exact this

end single

end AdalyFormal.CoverOmegaTwo
