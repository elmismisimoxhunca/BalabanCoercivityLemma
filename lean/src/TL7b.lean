import TL7a

/-!
# TL7b -- aligned blocks are mapped bijectively by `phiS`
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf inStepBlock)

theorem blockval_nat (b m o y x : ℕ) (hm0 : 0 < m) (hm : b ∣ m) (ho : b ∣ o) (hy : b ∣ y) (hb : 0 < b) (hyx : y ≤ x) (hxb : x < y + b) :
    (x + o) % m = (y + o) % m + (x - y) := by
  set q := (y + o) % m with hq
  have hqm : q < m := Nat.mod_lt _ hm0
  have hbq : b ∣ q := (Nat.dvd_mod_iff hm).mpr (dvd_add hy ho)
  obtain ⟨t, ht⟩ := hm
  obtain ⟨u, hu⟩ := hbq
  have hut : u < t := by
    by_contra hcon
    push Not at hcon
    have := Nat.mul_le_mul_left b hcon
    rw [hu, ht] at hqm
    omega
  have hq' : q + b ≤ m := by
    rw [hu, ht]
    calc b * u + b = b * (u + 1) := by ring
      _ ≤ b * t := Nat.mul_le_mul_left b hut
  have h1 : x + o = (y + o) + (x - y) := by omega
  have h2 : (y + o) = m * ((y + o) / m) + q := by
    have := Nat.div_add_mod (y + o) m
    omega
  rw [h1, h2, Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- inside an aligned block, `phiS` adds the same displacement -/
theorem phiS_val_in_block {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {b : ℕ} (hp : PhiOK h o b)
    (hb : 0 < b) {y x : PeriodicLatticeSite Lt} (hy : Aligned b y) (μ : Fin 3) (h1 : (y μ).val ≤ (x μ).val)
    (h2 : (x μ).val < (y μ).val + b) :
    (phiS h o x μ).val = (phiS h o y μ).val + ((x μ).val - (y μ).val) := by
  rw [phiS_val, phiS_val]
  exact blockval_nat b (L μ + 1) (o μ) (y μ).val (x μ).val (Nat.succ_pos _) (hp.side μ) (hp.off μ) (hy μ) hb h1 h2

theorem phiS_mem_stepBlock {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {s ell : ℕ}
    (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell) {y x : PeriodicLatticeSite Lt} (hy : Aligned (s * ell) y)
    (hx : x ∈ stepBlockOf y s ell) : phiS h o x ∈ stepBlockOf (phiS h o y) s ell := by
  rw [mem_stepBlockOf] at hx ⊢
  intro μ
  obtain ⟨h1, h2, h3⟩ := hx μ
  have hb : 0 < s * ell := Nat.mul_pos hs hell
  have := phiS_val_in_block hp hb hy μ h1 h2
  refine ⟨by omega, by omega, ?_⟩
  rw [this, Nat.add_sub_cancel_left]; exact h3

theorem aligned_add_le (b N y : ℕ) (hb : b ∣ N) (hy : b ∣ y) (hyN : y < N) : y + b ≤ N := by
  obtain ⟨t, rfl⟩ := hb
  obtain ⟨u, rfl⟩ := hy
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · subst h0; simp at hyN
    · exact h0
  have hut : u < t := Nat.lt_of_mul_lt_mul_left hyN
  calc b * u + b = b * (u + 1) := by ring
    _ ≤ b * t := Nat.mul_le_mul_left b hut

theorem stepBlock_sum {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {s ell : ℕ}
    (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell) {y : PeriodicLatticeSite Lt} (hy : Aligned (s * ell) y)
    {M : Type*} [AddCommMonoid M] (F : PeriodicLatticeSite L → M) :
    ∑ x ∈ stepBlockOf y s ell, F (phiS h o x) = ∑ w ∈ stepBlockOf (phiS h o y) s ell, F w := by
  have hb : 0 < s * ell := Nat.mul_pos hs hell
  refine Finset.sum_bij (fun x _ => phiS h o x) (fun x hx => phiS_mem_stepBlock hp hs hell hy hx) ?_ ?_ (fun _ _ => rfl)
  · intro x hx x' hx' hxx
    rw [mem_stepBlockOf] at hx hx'
    funext μ
    apply Fin.ext
    have e1 := phiS_val_in_block hp hb hy μ (hx μ).1 (hx μ).2.1
    have e2 := phiS_val_in_block hp hb hy μ (hx' μ).1 (hx' μ).2.1
    have e3 : (phiS h o x μ).val = (phiS h o x' μ).val := congrArg (fun z => (z μ).val) hxx
    have e4 := (hx μ).1
    have e5 := (hx' μ).1
    omega
  · intro w hw
    rw [mem_stepBlockOf] at hw
    have key : ∀ μ : Fin 3, ∃ c : Fin (Lt μ + 1), (y μ).val ≤ c.val ∧ c.val < (y μ).val + s * ell ∧
        (phiS h o y μ).val + (c.val - (y μ).val) = (w μ).val := by
      intro μ
      obtain ⟨h1, h2, h3⟩ := hw μ
      have hlt : (y μ).val + ((w μ).val - (phiS h o y μ).val) < Lt μ + 1 := by
        have := aligned_add_le (s * ell) (Lt μ + 1) (y μ).val ((hp.side μ).trans (h μ)) (hy μ) (y μ).isLt
        omega
      refine ⟨⟨(y μ).val + ((w μ).val - (phiS h o y μ).val), hlt⟩, by simp, by simp; omega, ?_⟩
      simp only [Nat.add_sub_cancel_left]; omega
    choose c hc1 hc2 hc3 using key
    refine ⟨c, ?_, ?_⟩
    · rw [mem_stepBlockOf]
      intro μ
      refine ⟨hc1 μ, hc2 μ, ?_⟩
      have := (hw μ).2.2
      have e : (w μ).val - (phiS h o y μ).val = (c μ).val - (y μ).val := by have := hc3 μ; omega
      rw [← e]; exact this
    · funext μ
      apply Fin.ext
      have e1 := phiS_val_in_block hp hb hy μ (hc1 μ) (hc2 μ)
      have := hc3 μ
      omega

end AdalyFormal.Thin
