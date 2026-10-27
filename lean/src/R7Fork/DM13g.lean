import R7Fork.DM13f

/-!
# DM13g -- the inductive step of the adjacency induction.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 32000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower Admissible bigSide BlockClosed)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice card_blockOf_of_coarse)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)

section adj
variable {L : PeriodicLatticeExtent}

/-- the means over the `n`-anchored block (depends on the anchor only) -/
noncomputable def Bm (n : ℕ) (Θ : PeriodicLatticeSite L → SuTwo) (x : PeriodicLatticeSite L) : SuTwo :=
  (1 / (n : ℝ) ^ 3) • ∑ w ∈ blockOf (anc n x) n, Θ w

theorem adj_step {ell M R k : ℕ} {S : Tower L} {φ : PeriodicLatticeSite L → SuTwo} {c : Fin 3 → SuTwo}
    (H : AdjHyp ell M R k L S φ c) (m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k)
    (IH : ∀ (u : PeriodicLatticeSite L) (μ : Fin 3), lev S u ≤ m - 1 → lev S (periodicLatticeShift u μ) ≤ m - 1 →
      meanB ell S (Theta φ c) (periodicLatticeShift u μ) = meanB ell S (Theta φ c) u - seam c u μ)
    (u : PeriodicLatticeSite L) (μ : Fin 3) (hu : lev S u ≤ m) (hv : lev S (periodicLatticeShift u μ) ≤ m) :
    meanB ell S (Theta φ c) (periodicLatticeShift u μ) = meanB ell S (Theta φ c) u - seam c u μ := by
  classical
  by_cases hlow : lev S u ≤ m - 1 ∧ lev S (periodicLatticeShift u μ) ≤ m - 1
  · exact IH u μ hlow.1 hlow.2
  have hmax : lev S u = m ∨ lev S (periodicLatticeShift u μ) = m := by
    by_contra h
    push_neg at h
    apply hlow
    constructor <;> omega
  set Θ := Theta φ c with hΘ
  have hell := H.hell
  set n := ell ^ m with hndef
  have hn : 0 < n := pow_pos hell m
  have hdvd : ∀ ν, n ∣ L ν + 1 := level_dvd H.hS hmk
  have hbigm : ∀ ν, 2 * n ≤ L ν + 1 := H.hbig m hmk
  -- key facts for any site of level `<= m`
  have key : ∀ x, lev S x ≤ m → meanB ell S Θ x = Bm n Θ x ∧ anc n x ∉ S.Om (m + 1) ∧
      (lev S x = m → anc n x ∈ S.Om m) := by
    intro x hx
    rcases Nat.lt_or_ge (lev S x) m with hlt | hge
    · have hlevx := lev_spec H.hS x
      have hxnot : x ∉ S.Om m := fun h => hlevx.2.2 (om_anti S H.hS.1 (by omega : lev S x + 1 ≤ m) h)
      have hOm : ∀ w ∈ blockOf (anc n x) n, w ∉ S.Om m := by
        intro w hw hwO
        apply hxnot
        refine H.hS.2.2.2.1 m hmk w hwO x (fun ρ => ?_)
        unfold bigSide
        have h1 := block_div_eq hn (anc_coarse (n := n) x) hw ρ
        have h2 : ((anc n x) ρ).val / n = (x ρ).val / n := by rw [anc_val]; exact Nat.mul_div_cancel_left _ hn
        rw [blk_div, blk_div, ← h2, ← h1]
      have hA2 : ∀ w ∈ blockOf (anc n x) n, lev S w < m ∧ stBlock ell S w ⊆ blockOf (anc n x) n :=
        fun w hw => stBlock_sub_block hell H.hS hm (anc_coarse x) hOm hw
      have hconst : ∀ w ∈ blockOf (anc n x) n, meanB ell S Θ w = meanB ell S Θ (anc n x) := by
        refine box_const H.hN (fun w => meanB ell S Θ w) hn (anc_coarse x) ?_
        intro w hw ν _ hsw
        have h1 := (hA2 w hw).1
        have h2 := (hA2 _ hsw).1
        show meanB ell S Θ (periodicLatticeShift w ν) = meanB ell S Θ w
        rw [IH w ν (by omega) (by omega)]
        have hnw : seam c w ν = 0 := by
          unfold seam
          rw [if_neg]
          intro hwr
          -- w and shift w nu lie in one n-block but have coordinates N-1 and 0
          have e1 := block_div_eq hn (anc_coarse (n := n) x) hw ν
          have e2 := block_div_eq hn (anc_coarse (n := n) x) hsw ν
          have hv0 : ((periodicLatticeShift w ν) ν).val = 0 := by
            rw [shift_val_same H.hN, hwr, Nat.mod_self]
          rw [hv0] at e2
          have hN2 := hbigm ν
          have : (w ν).val / n = 0 := by rw [e1, ← e2]; simp
          have hwlt : (w ν).val < n := by
            rcases Nat.div_eq_zero_iff.mp this with h0 | h1
            · omega
            · exact h1
          omega
        rw [hnw, sub_zero]
      have hxb : x ∈ blockOf (anc n x) n := mem_block_anc hn x
      have hmx : meanB ell S Θ x = meanB ell S Θ (anc n x) := hconst x hxb
      have hsum := sum_block_eq_sum_mean hell H.hS Θ (blockOf (anc n x) n) (fun w hw => (hA2 w hw).2)
      have hcard : (blockOf (anc n x) n).card = n ^ 3 := card_blockOf_of_coarse hdvd (anc_coarse x)
      have hBm : Bm n Θ x = meanB ell S Θ x := by
        unfold Bm
        rw [hsum, Finset.sum_congr rfl (fun w hw => hconst w hw), Finset.sum_const, hcard, ← hmx,
          ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
        have : (1 / (n : ℝ) ^ 3) * ((n ^ 3 : ℕ) : ℝ) = 1 := by
          have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
          push_cast; field_simp
        rw [this, one_smul]
      refine ⟨hBm.symm, ?_, fun h => absurd h (by omega)⟩
      have : anc n x ∉ S.Om m := hOm _ (self_mem_block hn (anc_coarse x))
      exact fun h => this (H.hS.1 m h)
    · have hxm : lev S x = m := by omega
      have hIs : IsLev S k x m := by have := lev_spec H.hS x; rwa [hxm] at this
      obtain ⟨h1, h2⟩ := anc_Om hell H.hS hIs hm
      refine ⟨?_, h2, fun _ => h1⟩
      unfold meanB Bm stBlock
      rw [hxm]
  obtain ⟨ku, hku2, hku3⟩ := key u hu
  obtain ⟨kv, hkv2, hkv3⟩ := key _ hv
  rw [ku, kv]
  rcases anchor_adj hn H.hN hdvd hbigm u μ with ⟨hsame, hnw⟩ | ⟨hadj, hwiff⟩
  · have : seam c u μ = 0 := by unfold seam; rw [if_neg]; exact hnw
    rw [this, sub_zero]
    unfold Bm
    rw [hsame]
  · -- adjacent anchors
    set p := anc n u with hp
    have hpc : p ∈ CoarseLattice L n := anc_coarse u
    have hrow := H.rows m hm hmk p hpc μ
      (by
        rcases hmax with h | h
        · exact Or.inl (hku3 h)
        · right; rw [← hadj]; exact hkv3 h)
      hku2 (by rw [← hadj]; exact hkv2)
    have hT := Theta_block_rel hn H.hN φ c hdvd hpc μ hrow
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hdiff : Bm n Θ (periodicLatticeShift u μ) - Bm n Θ u = - seam c u μ := by
      unfold Bm
      rw [hadj, ← smul_sub, hT, smul_smul]
      unfold seam
      by_cases hw : (u μ).val + 1 = L μ + 1
      · have h1 : (p μ).val + n = L μ + 1 := hwiff.mpr hw
        rw [if_pos h1, if_pos hw]
        have e : (1 / (n : ℝ) ^ 3) * (-((n : ℝ) ^ 3 * ((L μ + 1 : ℕ) : ℝ))) = -((L μ + 1 : ℕ) : ℝ) := by
          field_simp
        rw [e, neg_smul]
      · have h1 : ¬ ((p μ).val + n = L μ + 1) := fun h => hw (hwiff.mp h)
        rw [if_neg h1, if_neg hw]
        simp
    calc Bm n Θ (periodicLatticeShift u μ) = Bm n Θ u + (Bm n Θ (periodicLatticeShift u μ) - Bm n Θ u) := by abel
      _ = Bm n Θ u + (- seam c u μ) := by rw [hdiff]
      _ = Bm n Θ u - seam c u μ := by abel

end adj

#print axioms adj_step

end AdalyFormal.DirichletMono
