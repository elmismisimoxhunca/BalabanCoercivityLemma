import THL1

/-!
# THL7 -- a competitor `B~` never sees the boundary of `Omega_0` (lane thin_layer_20261019)

Question (owner): is there a counterexample to the headline for a thin level-0 layer, "a competitor `B~` near `∂Omega_0`"?  The competitors of the headline are the `B~` with
`OnLambdaT Lam B~` (`B~ b = 0` unless an endpoint of `b` lies in `Lambda`, CMP99b p.427).  `LambdaOK` puts `Lambda` (embedded) inside `Omega_k` at unit distance `> R M` from its complement.
`competitor_support_in_Om0`: for ANY tower with nested domains (any `Omega_0`, any layer) and `R M >= 1`, every bond `b` with `B~ b != 0` has BOTH endpoints embedded in `Omega_k ⊆ Omega_0`.
So the support of `B~` is always inside `Omega_k`, at positive distance `>= R M ell^k - 1`(fine sites) from the complement of `Omega_k`, whatever the level-0 layer: no `B~` lives near `∂Omega_0`.
(The boundary of `Omega_0` enters the form only through the Dirichlet operators, not through the competitor.)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.ThinLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

theorem shift_val' {L : PeriodicLatticeExtent} (hL2 : ∀ μ, 2 ≤ L μ + 1) (s : PeriodicLatticeSite L) (μ ρ : Fin 3) :
    ((periodicLatticeShift s μ) ρ).val = if ρ = μ then ((s ρ).val + 1) % (L ρ + 1) else (s ρ).val := by
  unfold periodicLatticeShift
  by_cases h : ρ = μ
  · subst h
    simp only [Function.update_self, if_true]
    rw [Fin.val_add, Fin.val_one']
    have h2 : 1 % (L ρ + 1) = 1 := Nat.mod_eq_of_lt (by have := hL2 ρ; omega)
    rw [h2]
  · simp [h]

theorem pcd_step_le1 (N a : ℕ) (hN : 2 ≤ N) (ha : a < N) : pcd N a ((a + 1) % N) ≤ 1 := by
  unfold pcd
  by_cases h : a + 1 < N
  · rw [Nat.mod_eq_of_lt h]; split_ifs <;> omega
  · have e : a + 1 = N := by omega
    rw [e, Nat.mod_self]; split_ifs <;> omega

theorem pcd_step_le1' (N a : ℕ) (hN : 2 ≤ N) (ha : a < N) : pcd N ((a + 1) % N) a ≤ 1 := by
  unfold pcd
  by_cases h : a + 1 < N
  · rw [Nat.mod_eq_of_lt h]; split_ifs <;> omega
  · have e : a + 1 = N := by omega
    rw [e, Nat.mod_self]; split_ifs <;> omega

theorem pdist_shift_le1 {L : PeriodicLatticeExtent} (hL2 : ∀ μ, 2 ≤ L μ + 1) (s : PeriodicLatticeSite L) (μ : Fin 3) :
    pdist s (periodicLatticeShift s μ) ≤ 1 := by
  unfold pdist
  calc ∑ ρ : Fin 3, pcd (L ρ + 1) (s ρ).val ((periodicLatticeShift s μ) ρ).val
      ≤ ∑ ρ : Fin 3, (if ρ = μ then 1 else 0) := by
        apply Finset.sum_le_sum
        intro ρ _
        rw [shift_val' hL2]
        by_cases h : ρ = μ
        · subst h; simp only [if_true]; exact pcd_step_le1 _ _ (hL2 ρ) (s ρ).isLt
        · simp only [h, if_false]; unfold pcd; split_ifs <;> omega
    _ = 1 := by simp

theorem pdist_shift_le1' {L : PeriodicLatticeExtent} (hL2 : ∀ μ, 2 ≤ L μ + 1) (s : PeriodicLatticeSite L) (μ : Fin 3) :
    pdist (periodicLatticeShift s μ) s ≤ 1 := by
  unfold pdist
  calc ∑ ρ : Fin 3, pcd (L ρ + 1) ((periodicLatticeShift s μ) ρ).val (s ρ).val
      ≤ ∑ ρ : Fin 3, (if ρ = μ then 1 else 0) := by
        apply Finset.sum_le_sum
        intro ρ _
        rw [shift_val' hL2]
        by_cases h : ρ = μ
        · subst h; simp only [if_true]; exact pcd_step_le1' _ _ (hL2 ρ) (s ρ).isLt
        · simp only [h, if_false]; unfold pcd; split_ifs <;> omega
    _ = 1 := by simp

/-- both endpoints of a bond with an endpoint in `Lambda` embed into `Omega_k` (when `1 ≤ R M`, unit tori with `>= 2` sites per direction). -/
theorem bond_endpoints_in_Om_k {Lu Lf : PeriodicLatticeExtent} (hL2 : ∀ μ, 2 ≤ Lu μ + 1) {ell M R k : ℕ} {S : Tower Lf}
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK ell M R k S Lam) (hMR : 1 ≤ R * M) (b : Bond Lu)
    (hb : b.1 ∈ Lam ∨ periodicLatticeShift b.1 b.2 ∈ Lam) :
    ∃ emb : PeriodicLatticeSite Lu → PeriodicLatticeSite Lf, (∀ y μ, (emb y μ).val = ell ^ k * (y μ).val) ∧
      emb b.1 ∈ S.Om k ∧ emb (periodicLatticeShift b.1 b.2) ∈ S.Om k := by
  obtain ⟨-, emb, he1, he2, he3⟩ := hL
  refine ⟨emb, he1, ?_⟩
  rcases hb with h | h
  · refine ⟨he2 _ h, ?_⟩
    by_contra hn
    have := he3 _ h _ hn
    have h1 := pdist_shift_le1 hL2 b.1 b.2
    omega
  · refine ⟨?_, he2 _ h⟩
    by_contra hn
    have := he3 _ h _ hn
    have h1 := pdist_shift_le1' hL2 b.1 b.2
    omega

/-- **a competitor never sees `∂Omega_0`**: every bond in the support of a competitor `B~` (`OnLambdaT Lam B~`, `B~ b ≠ 0`) has both endpoints embedded in `Omega_k`, hence
(nested domains) in `Omega_0` for EVERY level-0 domain with `Omega_1 ⊆ Omega_0`. -/
theorem competitor_support_in_Om0 {Lu Lf : PeriodicLatticeExtent} (hL2 : ∀ μ, 2 ≤ Lu μ + 1) {ell M R k : ℕ} {S : Tower Lf}
    (hnest : ∀ j, S.Om (j + 1) ⊆ S.Om j) {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK ell M R k S Lam) (hMR : 1 ≤ R * M)
    {Bt : Bond Lu → SuTwo} (hB : OnLambdaT Lam Bt) (b : Bond Lu) (hne : Bt b ≠ 0) :
    ∃ emb : PeriodicLatticeSite Lu → PeriodicLatticeSite Lf, (∀ y μ, (emb y μ).val = ell ^ k * (y μ).val) ∧
      emb b.1 ∈ S.Om 0 ∧ emb (periodicLatticeShift b.1 b.2) ∈ S.Om 0 := by
  have hb : b.1 ∈ Lam ∨ periodicLatticeShift b.1 b.2 ∈ Lam := by
    by_contra hcon
    exact hne (hB b hcon)
  obtain ⟨emb, he1, h1, h2⟩ := bond_endpoints_in_Om_k hL2 hL hMR b hb
  have hanti : Antitone S.Om := antitone_nat_of_succ_le hnest
  exact ⟨emb, he1, hanti (Nat.zero_le k) h1, hanti (Nat.zero_le k) h2⟩

end AdalyFormal.ThinLayer

#print axioms AdalyFormal.ThinLayer.pdist_shift_le1
#print axioms AdalyFormal.ThinLayer.pdist_shift_le1'
#print axioms AdalyFormal.ThinLayer.bond_endpoints_in_Om_k
#print axioms AdalyFormal.ThinLayer.competitor_support_in_Om0
