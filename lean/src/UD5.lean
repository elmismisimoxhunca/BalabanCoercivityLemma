import UD4

/-!
# UD5 -- supports: `InBox` is within 3, a partition cell has `pdist`-diameter `≤ 6 Mc`, `embY` scales `pdist` by `ℓ^k` (lane m2_unitcharts_20261014)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2UnitCharts

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.IngredientFamilyR2 (embY embY_val)
open AdalyFormal.M2Unit (psi1 prevC hpart Kc PartOK Kc_mul)
open AdalyFormal.FlatEllGeneral (InBox)

theorem pcd_next (N a : ℕ) (ha : a < N) : pcd N a ((a + 1) % N) ≤ 1 := by
  by_cases h : a + 1 < N
  · rw [Nat.mod_eq_of_lt h]; unfold pcd; split_ifs <;> omega
  · have : a + 1 = N := by omega
    rw [this, Nat.mod_self]; unfold pcd; split_ifs <;> omega

theorem inBox_pdist {Lu : PeriodicLatticeExtent} {z c : PeriodicLatticeSite Lu} (h : InBox z c) : pdist z c ≤ 3 := by
  unfold pdist
  have : ∀ ρ : Fin 3, pcd (Lu ρ + 1) (z ρ).val (c ρ).val ≤ 1 := by
    intro ρ
    rcases h ρ with h1 | h1
    · rw [h1]; unfold pcd; split_ifs <;> omega
    · rw [h1]
      have hv : ((z ρ + 1 : Fin (Lu ρ + 1)) : ℕ) = ((z ρ).val + 1) % (Lu ρ + 1) := by
        rw [Fin.val_add]
        by_cases h0 : Lu ρ = 0
        · have : (z ρ).val = 0 := by have := (z ρ).isLt; omega
          simp [h0, this]
        · rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < Lu ρ + 1)]
      rw [hv]
      exact pcd_next _ _ (z ρ).isLt
  calc ∑ ρ : Fin 3, pcd (Lu ρ + 1) (z ρ).val (c ρ).val ≤ ∑ _ρ : Fin 3, 1 := Finset.sum_le_sum (fun ρ _ => this ρ)
    _ = 3 := by simp

theorem psi1_supp {M K : ℕ} (m : Fin K) (t : ℕ) (h : psi1 M K m t ≠ 0) :
    m.val = t / M ∨ m.val = (t / M + K - 1) % K := by
  unfold psi1 at h
  split_ifs at h with h1 h2
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd rfl h

theorem prev_val {K a : ℕ} (ha : a < K) :
    (a = 0 ∧ (a + K - 1) % K = K - 1) ∨ (a ≠ 0 ∧ (a + K - 1) % K = a - 1) := by
  by_cases h : a = 0
  · left; subst h; refine ⟨rfl, ?_⟩; simp only [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
  · right; refine ⟨h, ?_⟩
    have : (a + K - 1) % K = (a + K - 1 - K) % K := Nat.mod_eq_sub_mod (by omega)
    rw [this, Nat.mod_eq_of_lt (by omega)]; omega

theorem psi1_pcd {M K : ℕ} (hM : 0 < M) (hK : 2 ≤ K) (m : Fin K) {t t' : ℕ} (ht : t < K * M) (ht' : t' < K * M)
    (h : psi1 M K m t ≠ 0) (h' : psi1 M K m t' ≠ 0) : pcd (K * M) t t' ≤ 2 * M := by
  have ha : t / M < K := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact ht)
  have ha' : t' / M < K := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact ht')
  have e1 := Nat.mod_add_div t M
  have e2 := Nat.mod_add_div t' M
  have l1 := Nat.mod_lt t hM
  have l2 := Nat.mod_lt t' hM
  have hm := m.isLt
  have pv := prev_val ha
  have pv' := prev_val ha'
  have c1 := psi1_supp m t h
  have c2 := psi1_supp m t' h'
  generalize t / M = a at *
  generalize t' / M = a' at *
  rw [mul_comm K M]
  have f1 : a' = a + 1 → M * a' = M * a + M := fun h => by subst h; ring
  have f2 : a = a' + 1 → M * a = M * a' + M := fun h => by subst h; ring
  have f3 : a = K - 1 → M * a + M = M * K := fun h => by
    subst h; obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩; simp [Nat.mul_succ]
  have f4 : a' = K - 1 → M * a' + M = M * K := fun h => by
    subst h; obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩; simp [Nat.mul_succ]
  have f5 : a = 0 → M * a = 0 := fun h => by subst h; simp
  have f6 : a' = 0 → M * a' = 0 := fun h => by subst h; simp
  have f7 : a' = a → M * a' = M * a := fun h => by subst h; rfl
  unfold pcd
  split_ifs <;> omega


theorem hpart_pdist {Lu : PeriodicLatticeExtent} {Mc : ℕ} (hP : PartOK Lu Mc) (m : (μ : Fin 3) → Fin (Kc Lu Mc μ))
    {x x' : PeriodicLatticeSite Lu} (h : hpart Mc m x ≠ 0) (h' : hpart Mc m x' ≠ 0) : pdist x x' ≤ 6 * Mc := by
  unfold hpart at h h'
  have hh := Finset.prod_ne_zero_iff.mp h
  have hh' := Finset.prod_ne_zero_iff.mp h'
  unfold pdist
  have : ∀ μ : Fin 3, pcd (Lu μ + 1) (x μ).val (x' μ).val ≤ 2 * Mc := by
    intro μ
    have hK := Kc_mul hP μ
    have hlt : (x μ).val < Kc Lu Mc μ * Mc := by rw [hK]; exact (x μ).isLt
    have hlt' : (x' μ).val < Kc Lu Mc μ * Mc := by rw [hK]; exact (x' μ).isLt
    have := psi1_pcd hP.1 (AdalyFormal.M2Unit.Kc_two hP μ) (m μ) hlt hlt' (hh μ (Finset.mem_univ μ)) (hh' μ (Finset.mem_univ μ))
    rwa [hK] at this
  calc ∑ μ : Fin 3, pcd (Lu μ + 1) (x μ).val (x' μ).val ≤ ∑ _μ : Fin 3, 2 * Mc := Finset.sum_le_sum (fun μ _ => this μ)
    _ = 6 * Mc := by simp; ring

theorem pdist_embY {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (a b : PeriodicLatticeSite Lu) :
    pdist (embY ell k Lu hell a) (embY ell k Lu hell b) = ell ^ k * pdist a b := by
  unfold pdist
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [embY_val, embY_val, scaleUp_succ ell k Lu hell σ]
  exact pcd_mul (Lu σ + 1) (ell ^ k) _ _ (pow_pos hell k)

end AdalyFormal.M2UnitCharts
