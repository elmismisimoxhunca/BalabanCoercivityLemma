import ZR2Ops2

/-!
# SC3 -- the flat nested composite is the block mean: tiling of a block of side `s*ell` by the `ell^3` blocks of side `s`
based at the strided centres `stepBlockOf y s ell`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.SiteCoercivity

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

theorem nat_unique {s a b d : ℕ} (hs : 0 < s) (ha1 : s * a ≤ d) (ha2 : d < s * a + s)
    (hb1 : s * b ≤ d) (hb2 : d < s * b + s) : a = b := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : s * (a + 1) ≤ s * b := Nat.mul_le_mul_left s h
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  · have : s * (b + 1) ≤ s * a := Nat.mul_le_mul_left s h
    rw [Nat.mul_add, Nat.mul_one] at this
    omega

/-- the stride centres of a block of side `s*ell` give disjoint sub-blocks of side `s` -/
theorem blockOf_disjoint {y c c' : PeriodicLatticeSite L} {s ell : ℕ} (hs : 0 < s)
    (hc : c ∈ stepBlockOf y s ell) (hc' : c' ∈ stepBlockOf y s ell) (hne : c ≠ c') :
    Disjoint (blockOf c s) (blockOf c' s) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  apply hne
  funext μ
  have h1 := (mem_blockOf.mp hx) μ
  have h2 := (mem_blockOf.mp hx') μ
  obtain ⟨a, ha⟩ := (mem_stepBlockOf.mp hc μ).2.2
  obtain ⟨b, hb⟩ := (mem_stepBlockOf.mp hc' μ).2.2
  have hy := (mem_stepBlockOf.mp hc μ).1
  have hy' := (mem_stepBlockOf.mp hc' μ).1
  have hab : a = b := by
    refine nat_unique (d := (x μ).val - (y μ).val) hs ?_ ?_ ?_ ?_ <;> omega
  subst hab
  apply Fin.ext
  omega


theorem blockOf_biUnion {y : PeriodicLatticeSite L} {s ell : ℕ} (hs : 0 < s) :
    (stepBlockOf y s ell).biUnion (fun c => blockOf c s) = blockOf y (s * ell) := by
  ext x
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, hx⟩
    rw [mem_blockOf]
    intro μ
    have h1 := (mem_blockOf.mp hx) μ
    obtain ⟨a, ha⟩ := (mem_stepBlockOf.mp hc μ).2.2
    have h3 := (mem_stepBlockOf.mp hc μ).2.1
    have h4 := (mem_stepBlockOf.mp hc μ).1
    have hal : a < ell := by
      by_contra hge
      rw [not_lt] at hge
      have := Nat.mul_le_mul_left s hge
      omega
    have : s * (a + 1) ≤ s * ell := Nat.mul_le_mul_left s hal
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  · intro hx
    have hxb := mem_blockOf.mp hx
    let c : PeriodicLatticeSite L := fun μ =>
      ⟨(y μ).val + s * (((x μ).val - (y μ).val) / s), by
        have := (hxb μ).1
        have h2 := Nat.mul_div_le ((x μ).val - (y μ).val) s
        have h3 := (x μ).isLt
        omega⟩
    refine ⟨c, ?_, ?_⟩
    · rw [mem_stepBlockOf]
      intro μ
      have h1 := (hxb μ).1
      have h2 := (hxb μ).2
      have h3 := Nat.mul_div_le ((x μ).val - (y μ).val) s
      refine ⟨by simp [c], ?_, ?_⟩
      · show (y μ).val + s * (((x μ).val - (y μ).val) / s) < (y μ).val + s * ell
        have : s * (((x μ).val - (y μ).val) / s) ≤ (x μ).val - (y μ).val := by
          rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
        omega
      · exact ⟨((x μ).val - (y μ).val) / s, by simp [c]⟩
    · rw [mem_blockOf]
      intro μ
      have h1 := (hxb μ).1
      have hd := Nat.div_add_mod ((x μ).val - (y μ).val) s
      have hm := Nat.mod_lt ((x μ).val - (y μ).val) hs
      show (y μ).val + s * (((x μ).val - (y μ).val) / s) ≤ (x μ).val ∧
        (x μ).val < (y μ).val + s * (((x μ).val - (y μ).val) / s) + s
      omega

theorem sum_blockOf_stepBlock {M : Type*} [AddCommMonoid M] {y : PeriodicLatticeSite L} {s ell : ℕ} (hs : 0 < s)
    (g : PeriodicLatticeSite L → M) :
    ∑ c ∈ stepBlockOf y s ell, ∑ x ∈ blockOf c s, g x = ∑ x ∈ blockOf y (s * ell), g x := by
  rw [← blockOf_biUnion hs, Finset.sum_biUnion]
  intro c hc c' hc' hne
  exact blockOf_disjoint hs hc hc' hne


open AdalyFormal.Balaban.QjComposite (Qcomposite Qcomposite_zero Qcomposite_succ stepAverage_trivialU blockOf_one_eq_singleton)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)

theorem stepBlock_mem_coarse {y c : PeriodicLatticeSite L} {s ell : ℕ}
    (hy : y ∈ CoarseLattice L (s * ell)) (hc : c ∈ stepBlockOf y s ell) : c ∈ CoarseLattice L s := by
  rw [mem_CoarseLattice] at hy ⊢
  intro μ
  have h1 := hy μ
  have h2 := (mem_stepBlockOf.mp hc μ)
  have hd : s ∣ (y μ).val := by
    have : (s * ell) ∣ (y μ).val := Nat.dvd_of_mod_eq_zero h1
    exact Dvd.dvd.trans (Dvd.intro ell rfl) this
  have hd2 : s ∣ (c μ).val - (y μ).val := h2.2.2
  have hd3 : s ∣ (c μ).val := by
    have : (c μ).val = (y μ).val + ((c μ).val - (y μ).val) := by omega
    rw [this]; exact Nat.dvd_add hd hd2
  exact Nat.mod_eq_zero_of_dvd hd3

/-- THE FLAT NESTED COMPOSITE IS THE BLOCK MEAN: at every level-`j` centre. -/
theorem Qflat_eq_blockMean (ell : ℕ) (hell : 0 < ell) (g : PeriodicLatticeSite L → SuTwo) :
    ∀ (j : ℕ) (y : PeriodicLatticeSite L), y ∈ CoarseLattice L (ell ^ j) →
      Qcomposite (fun _ => trivialU L) ell j g y
        = (1 / (((ell ^ j : ℕ)) : ℝ) ^ 3) • ∑ x ∈ blockOf y (ell ^ j), g x := by
  intro j
  induction j with
  | zero =>
    intro y _
    simp [Qcomposite_zero, blockOf_one_eq_singleton]
  | succ j ih =>
    intro y hy
    have hs : 0 < ell ^ j := pow_pos hell j
    rw [Qcomposite_succ, stepAverage_trivialU]
    have hterm : ∀ c ∈ stepBlockOf y (ell ^ j) ell,
        Qcomposite (fun _ => trivialU L) ell j g c
          = (1 / (((ell ^ j : ℕ)) : ℝ) ^ 3) • ∑ x ∈ blockOf c (ell ^ j), g x := by
      intro c hc
      exact ih c (stepBlock_mem_coarse (by rw [← pow_succ]; exact hy) hc)
    rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, smul_smul]
    rw [sum_blockOf_stepBlock hs, ← pow_succ]
    congr 1
    push_cast
    field_simp
    ring

end AdalyFormal.SiteCoercivity
