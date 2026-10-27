import NB14
/-!
# NB15 -- the cone of a coarse bond / of the identity's ladders lies in the box (piece N2, part 5)

With `m = s·ell`, `B = 2m − s`, `2m < N_ρ`: for a coarse bond `c` whose base is in `Box y s m` with zero
offset in its own direction, every bond read by its blocking has base in `Box y s B` (`cone_box`);
the plaquettes enclosed by the identity's ladders at block sites of `y` have their four bond bases in
`Box y s B` (`ladder_box`).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarsePathEndpoint)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq)

variable {L : PeriodicLatticeExtent}

theorem dvd_lt_add {s a m : ℕ} (ha : s ∣ a) (hm : s ∣ m) (h : a < m) : a + s ≤ m := by
  obtain ⟨q, rfl⟩ := ha
  obtain ⟨r, rfl⟩ := hm
  have hs : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
  have : q < r := (Nat.mul_lt_mul_left hs).mp h
  have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt this)
  rw [Nat.mul_succ] at this; exact this

theorem block_offsets (s ell : ℕ) (c x : PeriodicLatticeSite L)
    (hfit : ∀ σ, (c σ).val + s * ell ≤ L σ + 1) (hx : x ∈ stepBlockOf c s ell) (σ : Fin 3) :
    s ∣ off c x σ ∧ off c x σ + s ≤ s * ell := by
  have h := ((mem_block_iff s ell hfit).mp hx) σ
  exact ⟨h.2, dvd_lt_add h.2 (Dvd.intro ell rfl) h.1⟩

theorem cone_box (s ell : ℕ) (hs : 0 < s) (y : PeriodicLatticeSite L) (c : PeriodicLatticeEdge L)
    (hN : ∀ ρ, 2 * (s * ell) < L ρ + 1) (hm : s ≤ s * ell)
    (hc : Box y s (s * ell) c.1) (hc2 : off y c.1 c.2 = 0)
    (hfit : ∀ σ, (c.1 σ).val + s * ell ≤ L σ + 1) :
    (∀ x ∈ stepBlockOf c.1 s ell, ∀ b ∈ loopBonds s ell c x, Box y s (2 * (s * ell) - s) b.1) ∧
    ∀ b ∈ pathBonds s c.1 (List.replicate ell c.2), Box y s (2 * (s * ell) - s) b.1 := by
  set m := s * ell
  set B := 2 * m - s
  have hB : ∀ ρ, B < L ρ + 1 := fun ρ => by have := hN ρ; omega
  have hcB : Box y s B c.1 := fun σ => ⟨(hc σ).1, by have := (hc σ).2; omega⟩
  refine ⟨?_, ?_⟩
  · intro x hx b hb
    have hxo := block_offsets s ell c.1 x hfit hx
    have hoff : ∀ σ, off y x σ = off c.1 x σ + off y c.1 σ := fun σ =>
      off_add y c.1 x σ (by have := (hxo σ).2; have := (hc σ).2; have := hN σ; omega)
    have hmul : ∀ σ, s * (off c.1 x σ / s) = off c.1 x σ := fun σ =>
      Nat.mul_div_cancel' (hxo σ).1
    unfold loopBonds at hb
    simp only [List.mem_append] at hb
    rcases hb with ((hb | hb) | hb) | hb
    · rw [gamma_eq] at hb
      refine box_stair y c.1 s B _ _ _ hcB ?_ ?_ ?_ hB b hb
      · rw [hmul]; have := (hxo 2).2; have := (hc 2).2; omega
      · rw [hmul]; have := (hxo 1).2; have := (hc 1).2; omega
      · rw [hmul]; have := (hxo 0).2; have := (hc 0).2; omega
    · have hxB : Box y s B x := fun σ => ⟨by rw [hoff]; exact Nat.dvd_add (hxo σ).1 (hc σ).1,
        by rw [hoff]; have := (hxo σ).2; have := (hc σ).2; omega⟩
      refine box_rep y x s B ell c.2 hxB ?_ (hB _) b hb
      rw [hoff, hc2]; have := (hxo c.2).2; omega
    · have hp : cPlusS s ell c = coarseShift c.1 m c.2 := cPlusS_eq s ell c
      rw [hp, gamma_eq] at hb
      have op : ∀ σ, off y (coarseShift c.1 m c.2) σ ≤ m ∧ s ∣ off y (coarseShift c.1 m c.2) σ := by
        intro σ
        by_cases hσ : σ = c.2
        · rw [hσ, off_shift_val _ _ _ _ (by rw [hc2]; have := hN c.2; omega), hc2]
          exact ⟨by omega, ⟨ell, by omega⟩⟩
        · rw [off_shift_ne _ _ _ hσ]; exact ⟨(hc σ).2, (hc σ).1⟩
      have hpB : Box y s B (coarseShift c.1 m c.2) := fun σ =>
        ⟨(op σ).2, by have := (op σ).1; omega⟩
      refine box_stair y _ s B _ _ _ hpB ?_ ?_ ?_ hB b hb
      · rw [hmul]; have := (hxo 2).2; have := (op 2).1; omega
      · rw [hmul]; have := (hxo 1).2; have := (op 1).1; omega
      · rw [hmul]; have := (hxo 0).2; have := (op 0).1; omega
    · refine box_rep y c.1 s B ell c.2 hcB ?_ (hB _) b hb
      rw [hc2]; omega
  · intro b hb
    refine box_rep y c.1 s B ell c.2 hcB ?_ (hB _) b hb
    rw [hc2]; omega

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.cone_box
