import P409B

/-!
# P409C -- `CoversOm0p` and `Admissible` for the one-slab tower (abstract numerics).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge

theorem TG_coversp {L : PeriodicLatticeExtent} {N ell M A0 A B B0 : ℕ} (hN : ∀ μ, L μ + 1 = N) (hN1 : 1 < N)
    (hM : 0 < M) (hell : 2 ≤ ell)
    (hMA0 : M ∣ A0) (hMB0 : M ∣ B0) (hgA : M * ell ∣ A) (hgB : M * ell ∣ B)
    (hsh1 : A0 + 12 * M ≤ A) (hsh2 : B + 12 * M ≤ B0) (hW : A + 12 * (M * ell) ≤ B)
    (hB0N : B0 < N) (hNb : 12 * M + 12 * (M * ell) ≤ N) :
    CoversOm0p ell M 12 1 (TG A0 A B B0 L) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨sites, j, hc, hall⟩ := cover_nbhd hN hM hell hMA0 hMB0 hgA hgB hsh1 hsh2 hW hB0N hNb x ((TG_om0 x).mp hx)
    exact ⟨sites, j, hc, hall x (adjN_refl N x) (((TG_om0 x).mp hx).1) (((TG_om0 x).mp hx).2)⟩
  · intro p hp
    have hmu : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
    have hnu : p.2.1.2 ≠ p.2.1.1 := fun h => hmu h.symm
    have hmem : ∀ e : PeriodicLatticeEdge L, e ∈ periodicPlaquetteBoundaryEdges p ↔
        (e = (p.1, p.2.1.1) ∨ e = (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∨
          e = (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∨ e = (p.1, p.2.1.2)) := by
      intro e
      simp [periodicPlaquetteBoundaryEdges]
    have hx : A0 ≤ (p.1 0).val ∧ (p.1 0).val < B0 :=
      (TG_om0 _).mp (hp (p.1, p.2.1.1) ((hmem _).mpr (Or.inl rfl))).1
    obtain ⟨sites, j, hc, hall⟩ := cover_nbhd hN hM hell hMA0 hMB0 hgA hgB hsh1 hsh2 hW hB0N hNb p.1 hx
    refine ⟨sites, j, hc, fun e he => ?_⟩
    have hcb := hp e he
    have hcb1 := (TG_om0 _).mp hcb.1
    have hcb2 := (TG_om0 _).mp hcb.2
    have a0 : AdjN N p.1 p.1 := adjN_refl N _
    have aμ : AdjN N p.1 (periodicLatticeShift p.1 p.2.1.1) := adjN_shift hN hN1 a0 _ rfl
    have aν : AdjN N p.1 (periodicLatticeShift p.1 p.2.1.2) := adjN_shift hN hN1 a0 _ rfl
    have aμν : AdjN N p.1 (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2) :=
      adjN_shift hN hN1 aμ _ (adjN_shift_coord hN hN1 _ hnu)
    have aνμ : AdjN N p.1 (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.2) p.2.1.1) :=
      adjN_shift hN hN1 aν _ (adjN_shift_coord hN hN1 _ hmu)
    refine ⟨?_, ?_⟩
    · rcases (hmem e).mp he with rfl | rfl | rfl | rfl
      · exact hall _ a0 hcb1.1 hcb1.2
      · exact hall _ aμ hcb1.1 hcb1.2
      · exact hall _ aν hcb1.1 hcb1.2
      · exact hall _ a0 hcb1.1 hcb1.2
    · rcases (hmem e).mp he with rfl | rfl | rfl | rfl
      · exact hall _ aμ hcb2.1 hcb2.2
      · exact hall _ aμν hcb2.1 hcb2.2
      · exact hall _ aνμ hcb2.1 hcb2.2
      · exact hall _ aν hcb2.1 hcb2.2

/-! ## Admissible -/

theorem blk_iv {M a b x y : ℕ} (hM : 0 < M) (ha : M ∣ a) (hb : M ∣ b) (hxy : y / M = x / M)
    (h : a ≤ x ∧ x < b) : a ≤ y ∧ y < b := by
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨q, rfl⟩ := hb
  have h1 : p ≤ x / M := (Nat.le_div_iff_mul_le hM).mpr (by rw [mul_comm]; exact h.1)
  have h2 : x / M < q := (Nat.div_lt_iff_lt_mul hM).mpr (by rw [mul_comm]; exact h.2)
  rw [← hxy] at h1 h2
  have h3 := (Nat.le_div_iff_mul_le hM).mp h1
  have h4 := (Nat.div_lt_iff_lt_mul hM).mp h2
  rw [mul_comm] at h3 h4
  exact ⟨h3, h4⟩

theorem pcd_le_pdist {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) :
    pcd (L 0 + 1) (x 0).val (y 0).val ≤ pdist x y :=
  Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)

theorem TG_admissible {L : PeriodicLatticeExtent} {N ell M R A0 A B B0 : ℕ} (hN : ∀ μ, L μ + 1 = N)
    (hM : 0 < M) (hell : 2 ≤ ell)
    (hA0 : A0 + R * M = A) (hB0 : B + R * M = B0) (hMA0 : M ∣ A0) (hMB0 : M ∣ B0)
    (hgA : M * ell ∣ A) (hgB : M * ell ∣ B) (hMN : M ∣ N) (hgN : M * ell ∣ N)
    (hAB : A < B) (hB0N : B0 ≤ N) :
    Admissible ell M R 1 (TG A0 A B B0 L) := by
  have hdiv : ∀ x : PeriodicLatticeSite L, x ∈ (TG A0 A B B0 L).Om 0 ↔ A0 ≤ (x 0).val ∧ (x 0).val < B0 := TG_om0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (_ | _ | j) x hx
    · exact (TG_om0 x).mpr (by have := (TG_om1 x).mp hx; omega)
    · have h2 : (TG A0 A B B0 L).Om (0 + 1 + 1) = ∅ := TG_om2 0
      rw [h2] at hx; exact absurd hx (Set.notMem_empty _)
    · have h2 := TG_om2 (L := L) (A0 := A0) (A := A) (B := B) (B0 := B0) (j + 1)
      have hx' : x ∈ (TG A0 A B B0 L).Om (j + 1 + 2) := hx
      rw [h2] at hx'; exact absurd hx' (Set.notMem_empty _)
  · rintro (_ | _ | j) hj
    · omega
    · omega
    · exact TG_om2 j
  · intro j hj μ
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · rw [bigSide0, hN μ]; exact hMN
    · rw [bigSide1, hN μ]; exact hgN
  · intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · intro x hx y hy
      rw [bigSide0] at hy
      rw [TG_om0] at hx ⊢
      exact blk_iv hM hMA0 hMB0 (hy 0) hx
    · intro x hx y hy
      rw [bigSide1] at hy
      rw [TG_om1] at hx ⊢
      exact blk_iv (Nat.mul_pos hM (by omega)) hgA hgB (hy 0) hx
  · intro j hj x hx y hy
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · rw [TG_om0] at hx
      rw [TG_om1] at hy
      have hx0 := site_lt hN x 0
      have hy0 := site_lt hN y 0
      have hlt : R * M < pcd (L 0 + 1) (x 0).val (y 0).val := by
        have := hN 0; unfold pcd; split_ifs <;> omega
      rw [bigSide0]
      exact lt_of_lt_of_le hlt (pcd_le_pdist x y)
    · have h2 : (TG A0 A B B0 L).Om (0 + 1 + 1) = ∅ := TG_om2 0
      rw [h2] at hy; exact absurd hy (Set.notMem_empty _)
  · intro x
    rw [TG_om0]
    constructor
    · intro hx
      have hx0 := site_lt hN x 0
      let v : ℕ := if (x 0).val < A then A else if (x 0).val < B then (x 0).val else B - 1
      have hv : v < L 0 + 1 := by have := hN 0; simp only [v]; split_ifs <;> omega
      refine ⟨Function.update x 0 ⟨v, hv⟩, ?_, x, fun μ => rfl, ?_⟩
      · rw [TG_om1]; simp only [Function.update_self]; simp only [v]; split_ifs <;> omega
      · unfold pdist
        rw [Finset.sum_eq_single (0 : Fin 3)]
        · simp only [Function.update_self]
          have := hN 0; unfold pcd; simp only [v]; split_ifs <;> omega
        · intro μ _ h
          rw [Function.update_of_ne h]; unfold pcd; simp
        · intro h; exact absurd (Finset.mem_univ _) h
    · rintro ⟨y, hy, z, hz, hd⟩
      rw [TG_om1] at hy
      have hz0 : (z 0).val / M = (x 0).val / M := hz 0
      have h12 : pcd (L 0 + 1) (z 0).val (y 0).val ≤ R * M := le_trans (pcd_le_pdist z y) hd
      have hzN := site_lt hN z 0
      have hyN := site_lt hN y 0
      have hzr : A0 ≤ (z 0).val ∧ (z 0).val < B0 := by
        have := hN 0; unfold pcd at h12; split_ifs at h12 <;> omega
      exact blk_iv hM hMA0 hMB0 hz0.symm hzr

end AdalyFormal.P409
