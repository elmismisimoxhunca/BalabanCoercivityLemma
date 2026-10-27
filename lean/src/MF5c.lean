import MF5b
import FE2
import AdalyFormal.Balaban.LineIntegralCovariant
import AdalyFormal.Balaban.ReparamCDisjoint

/-!
# MF5c -- an explicit right inverse of the FLAT top-level bond map `Q_k(1)` (the `n`-block line average), every `n`, every torus with `n ∣ L+1`.

`bondE n W (x, μ) = Σ_c bK n x μ c • W c`, `bK n x μ c = [c.2 = μ] · gprof n ((x_μ − y_μ) mod) · Π_{ν≠μ} [(x_ν − y_ν) mod < n]`, `y = c.1`:
on each block column the field is the linear profile `g(t) = (4 − 2n + 6t)/(n+1)` along `μ` times the coarse value.
* `bondE_rightInv` : `lineCoarseRestrictSuTwo n (bondE n W) c = W c` for every coarse bond `c`;
* `bondE_norm_sq`  : `Σ_b ‖bondE n W b‖² ≤ 16 n³ Σ_c ‖W c‖²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M0Finish

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.QOne (pathSite)

variable {L : PeriodicLatticeExtent}

/-- the 1D factor in direction `ν` of the kernel for bonds of direction `μ` -/
noncomputable def fac (n : ℕ) (μ ν : Fin 3) (t : ℕ) : ℝ := if ν = μ then gprof n t else (if t < n then 1 else 0)

noncomputable def bK (n : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) (c : CoarseBond L n) : ℝ :=
  if c.2 = μ then ∏ ν : Fin 3, fac n μ ν ((x ν - c.1.1 ν).val) else 0

/-- **the flat bond right inverse** -/
noncomputable def bondE (n : ℕ) (W : CoarseBond L n → SuTwo) : Bond L → SuTwo :=
  fun b => ∑ c : CoarseBond L n, bK n b.1 b.2 c • W c

/-! ## 1D, on one coordinate -/

theorem fin_sub_val {N : ℕ} [NeZero N] (a b : Fin N) : (a - b).val = (N - b.val + a.val) % N := by
  rw [Fin.sub_def]

theorem dvd_sub_val {N n : ℕ} [NeZero N] (hnN : n ∣ N) (z y : Fin N) (hz : n ∣ z.val) (hy : n ∣ y.val) :
    n ∣ (z - y).val := by
  have h := AdalyFormal.FlatExt.sub_val_mod hnN z y hy
  exact Nat.dvd_of_mod_eq_zero (by rw [h]; exact Nat.mod_eq_zero_of_dvd hz)

theorem block_reindex {N : ℕ} [NeZero N] (n : ℕ) (z : Fin N) (hzn : z.val + n ≤ N) (F : ℕ → ℝ) :
    ∑ a ∈ univ.filter (fun a : Fin N => z.val ≤ a.val ∧ a.val < z.val + n), F a.val
      = ∑ r ∈ range n, F (z.val + r) := by
  refine Finset.sum_bij' (fun a _ => a.val - z.val) (fun r hr => (⟨z.val + r, by
      have := mem_range.mp hr; omega⟩ : Fin N)) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [mem_filter, mem_univ, true_and] at ha; simp only [mem_range]; omega
  · intro r hr; have := mem_range.mp hr; simp only [mem_filter, mem_univ, true_and]; omega
  · intro a ha; simp only [mem_filter, mem_univ, true_and] at ha; apply Fin.ext; simp; omega
  · intro r hr; simp
  · intro a ha; simp only [mem_filter, mem_univ, true_and] at ha; congr 1; omega

theorem coord_fit {N n : ℕ} (hn : 0 < n) (hnN : n ∣ N) (z : Fin N) (hz : n ∣ z.val) : z.val + n ≤ N := by
  obtain ⟨Nu, hNu⟩ := hnN
  obtain ⟨m, hm⟩ := hz
  have h1 : n * m < n * Nu := by rw [← hm, ← hNu]; exact z.isLt
  have h2 : m < Nu := Nat.lt_of_mul_lt_mul_left h1
  have h3 := Nat.mul_le_mul_left n (show m + 1 ≤ Nu by omega)
  rw [Nat.mul_succ] at h3; omega

/-- the line factor: own block only, weight `n²` -/
theorem line_factor {M n : ℕ} (hn : 0 < n) (hnN : n ∣ M + 1) (z y : Fin (M + 1)) (hz : n ∣ z.val) (hy : n ∣ y.val) :
    ∑ a ∈ univ.filter (fun a : Fin (M + 1) => z.val ≤ a.val ∧ a.val < z.val + n),
      ∑ i ∈ range n, gprof n ((a + i • (1 : Fin (M + 1)) - y).val) = if z = y then (n : ℝ) ^ 2 else 0 := by
  set D := (z - y).val with hD
  have hDd : n ∣ D := dvd_sub_val hnN z y hz hy
  have hDN : D < M + 1 := (z - y).isLt
  have hval : ∀ a : Fin (M + 1), ∀ i : ℕ, a.val = z.val + (a.val - z.val) → z.val ≤ a.val →
      (a + i • (1 : Fin (M + 1)) - y).val = (D + (a.val - z.val) + i) % (M + 1) := by
    intro a i _ hza
    rw [fin_sub_val, Fin.val_add, AdalyFormal.Balaban.Q1Real.nsmul_one_val, hD, fin_sub_val]
    have h1 : (M + 1 - y.val + (a.val + i % (M + 1)) % (M + 1)) ≡ (M + 1 - y.val + (a.val + i)) [MOD (M + 1)] :=
      Nat.ModEq.add_left (M + 1 - y.val)
        ((Nat.mod_modEq (a.val + i % (M + 1)) (M + 1)).trans (Nat.ModEq.add_left a.val (Nat.mod_modEq i (M + 1))))
    have h2 : ((M + 1 - y.val + z.val) % (M + 1) + (a.val - z.val) + i) ≡ (M + 1 - y.val + z.val + (a.val - z.val) + i)
        [MOD (M + 1)] :=
      Nat.ModEq.add_right i (Nat.ModEq.add_right (a.val - z.val) (Nat.mod_modEq _ (M + 1)))
    have e : M + 1 - y.val + (a.val + i) = M + 1 - y.val + z.val + (a.val - z.val) + i := by omega
    rw [e] at h1
    exact h1.trans h2.symm
  have hfit := coord_fit hn hnN z hz
  have hstep : ∑ a ∈ univ.filter (fun a : Fin (M + 1) => z.val ≤ a.val ∧ a.val < z.val + n),
      ∑ i ∈ range n, gprof n ((a + i • (1 : Fin (M + 1)) - y).val)
      = ∑ a ∈ univ.filter (fun a : Fin (M + 1) => z.val ≤ a.val ∧ a.val < z.val + n),
          (fun v : ℕ => ∑ i ∈ range n, gprof n ((D + (v - z.val) + i) % (M + 1))) a.val := by
    refine sum_congr rfl (fun a ha => ?_)
    simp only [mem_filter, mem_univ, true_and] at ha
    refine sum_congr rfl (fun i _ => ?_)
    rw [hval a i (by omega) ha.1]
  rw [hstep, block_reindex n z hfit (fun v : ℕ => ∑ i ∈ range n, gprof n ((D + (v - z.val) + i) % (M + 1)))]
  have e2 : ∀ r ∈ range n, (fun v : ℕ => ∑ i ∈ range n, gprof n ((D + (v - z.val) + i) % (M + 1))) (z.val + r)
      = ∑ i ∈ range n, gprof n ((D + r + i) % (M + 1)) := by
    intro r _; simp
  rw [sum_congr rfl e2, core_line (M + 1) n D hn hnN hDd hDN]
  have hiff : D = 0 ↔ z = y := by
    rw [hD, Fin.val_eq_zero_iff, sub_eq_zero]
  by_cases h : z = y
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

/-- the transverse factor: weight `n` -/
theorem ind_factor {M n : ℕ} (hn : 0 < n) (hnN : n ∣ M + 1) (z y : Fin (M + 1)) (hz : n ∣ z.val) (hy : n ∣ y.val) :
    ∑ a ∈ univ.filter (fun a : Fin (M + 1) => z.val ≤ a.val ∧ a.val < z.val + n),
      (if (a - y).val < n then (1 : ℝ) else 0) = if z = y then (n : ℝ) else 0 := by
  set D := (z - y).val with hD
  have hDd : n ∣ D := dvd_sub_val hnN z y hz hy
  have hDN : D < M + 1 := (z - y).isLt
  have hfit := coord_fit hn hnN z hz
  have hstep : ∑ a ∈ univ.filter (fun a : Fin (M + 1) => z.val ≤ a.val ∧ a.val < z.val + n),
      (if (a - y).val < n then (1 : ℝ) else 0)
      = ∑ a ∈ univ.filter (fun a : Fin (M + 1) => z.val ≤ a.val ∧ a.val < z.val + n),
          (fun v : ℕ => if (D + (v - z.val)) % (M + 1) < n then (1 : ℝ) else 0) a.val := by
    refine sum_congr rfl (fun a ha => ?_)
    simp only [mem_filter, mem_univ, true_and] at ha
    have : (a - y).val = (D + (a.val - z.val)) % (M + 1) := by
      rw [fin_sub_val, hD, fin_sub_val, Nat.mod_add_mod]
      congr 1; omega
    rw [this]
  rw [hstep, block_reindex n z hfit (fun v : ℕ => if (D + (v - z.val)) % (M + 1) < n then (1 : ℝ) else 0)]
  have e2 : ∀ r ∈ range n, (fun v : ℕ => if (D + (v - z.val)) % (M + 1) < n then (1 : ℝ) else 0) (z.val + r)
      = if (D + r) % (M + 1) < n then (1 : ℝ) else 0 := by
    intro r _; simp
  rw [sum_congr rfl e2, core_ind (M + 1) n D hn hnN hDd hDN]
  have hiff : D = 0 ↔ z = y := by
    rw [hD, Fin.val_eq_zero_iff, sub_eq_zero]
  by_cases h : z = y
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

/-! ## 3D -/

/-- the per-coordinate factor after the line sum -/
noncomputable def Hf (n : ℕ) (μ : Fin 3) (y : PeriodicLatticeSite L) (ν : Fin 3) (a : Fin (L ν + 1)) : ℝ :=
  if ν = μ then ∑ i ∈ range n, fac n μ ν ((a + i • (1 : Fin (L ν + 1)) - y ν).val) else fac n μ ν ((a - y ν).val)

theorem line_prod (n : ℕ) (x y : PeriodicLatticeSite L) (μ : Fin 3) :
    ∑ i ∈ range n, ∏ ν : Fin 3, fac n μ ν (((pathSite x μ i) ν - y ν).val) = ∏ ν : Fin 3, Hf n μ y ν (x ν) := by
  have hL : ∀ i, ∏ ν : Fin 3, fac n μ ν (((pathSite x μ i) ν - y ν).val)
      = fac n μ μ ((x μ + i • (1 : Fin (L μ + 1)) - y μ).val)
        * ∏ ν ∈ ({μ}ᶜ : Finset (Fin 3)), fac n μ ν ((x ν - y ν).val) := by
    intro i
    rw [Fintype.prod_eq_mul_prod_compl μ]
    congr 1
    · rw [AdalyFormal.Balaban.ReparamCDisjoint.pathSite_eq, Function.update_self]
    · refine Finset.prod_congr rfl (fun ν hν => ?_)
      have hne : ν ≠ μ := by simpa [Finset.mem_compl, Finset.mem_singleton] using hν
      rw [AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_ne x μ ν i hne]
  have hR : ∏ ν : Fin 3, Hf n μ y ν (x ν)
      = (∑ i ∈ range n, fac n μ μ ((x μ + i • (1 : Fin (L μ + 1)) - y μ).val))
        * ∏ ν ∈ ({μ}ᶜ : Finset (Fin 3)), fac n μ ν ((x ν - y ν).val) := by
    rw [Fintype.prod_eq_mul_prod_compl μ]
    congr 1
    · simp [Hf]
    · refine Finset.prod_congr rfl (fun ν hν => ?_)
      have hne : ν ≠ μ := by simpa [Finset.mem_compl, Finset.mem_singleton] using hν
      simp only [Hf, if_neg hne]
  rw [hR, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => hL i)

theorem blockOf_pi (z : PeriodicLatticeSite L) (n : ℕ) :
    blockOf z n = Fintype.piFinset (fun ν => univ.filter
      (fun a : Fin (L ν + 1) => (z ν).val ≤ a.val ∧ a.val < (z ν).val + n)) := by
  ext x
  simp only [mem_blockOf, Fintype.mem_piFinset, mem_filter, mem_univ, true_and,
    AdalyFormal.Balaban.AdmissibleSubspace.inBlock]

/-- **the block-line sum of the kernel**: `n⁴` on the own coarse bond, `0` elsewhere. -/
theorem block_line_sum (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν, n ∣ L ν + 1)
    (z : PeriodicLatticeSite L) (hz : z ∈ CoarseLattice L n) (μ : Fin 3) (c : CoarseBond L n) :
    ∑ x ∈ blockOf z n, ∑ i ∈ range n, bK n (pathSite x μ i) μ c
      = if c = (⟨z, hz⟩, μ) then (n : ℝ) ^ 4 else 0 := by
  classical
  by_cases hc : c.2 = μ
  · have hzd : ∀ ν, n ∣ (z ν).val := fun ν => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hz ν)
    have hyd : ∀ ν, n ∣ (c.1.1 ν).val := fun ν => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp c.1.2 ν)
    have h1 : ∀ x ∈ blockOf z n, ∑ i ∈ range n, bK n (pathSite x μ i) μ c = ∏ ν : Fin 3, Hf n μ c.1.1 ν (x ν) := by
      intro x _
      simp only [bK, if_pos hc]
      exact line_prod n x c.1.1 μ
    rw [sum_congr rfl h1, blockOf_pi, ← Finset.prod_univ_sum]
    have hfac : ∀ ν : Fin 3, ∑ a ∈ univ.filter (fun a : Fin (L ν + 1) => (z ν).val ≤ a.val ∧ a.val < (z ν).val + n),
        Hf n μ c.1.1 ν a = if z ν = c.1.1 ν then (if ν = μ then (n : ℝ) ^ 2 else (n : ℝ)) else 0 := by
      intro ν
      by_cases hνμ : ν = μ
      · simp only [Hf, if_pos hνμ, fac]
        rw [line_factor hn (hdvd ν) (z ν) (c.1.1 ν) (hzd ν) (hyd ν)]
      · simp only [Hf, if_neg hνμ, fac]
        rw [ind_factor hn (hdvd ν) (z ν) (c.1.1 ν) (hzd ν) (hyd ν)]
    rw [Finset.prod_congr rfl (fun ν _ => hfac ν)]
    by_cases hzy : z = c.1.1
    · have hce : c = (⟨z, hz⟩, μ) := by
        obtain ⟨⟨y, hy⟩, μ'⟩ := c
        simp only at hzy hc
        subst hzy; subst hc; rfl
      rw [if_pos hce]
      simp only [hzy, if_true]
      rw [Fin.prod_univ_three]
      fin_cases μ <;> simp <;> ring
    · have hce : ¬ c = (⟨z, hz⟩, μ) := by
        intro h; apply hzy; rw [h]
      rw [if_neg hce]
      have : ∃ ν, z ν ≠ c.1.1 ν := by
        by_contra hall; push_neg at hall; exact hzy (funext hall)
      obtain ⟨ν, hν⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_univ ν) (by rw [if_neg hν])
  · have h0 : ∀ x ∈ blockOf z n, ∑ i ∈ range n, bK n (pathSite x μ i) μ c = 0 := by
      intro x _; simp [bK, hc]
    rw [sum_congr rfl h0, sum_const_zero, if_neg]
    intro h; apply hc; rw [h]

/-- **`Q_k(1) E = id`** on the line-average carrier. -/
theorem bondE_rightInv (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν, n ∣ L ν + 1) (W : CoarseBond L n → SuTwo)
    (c0 : CoarseBond L n) : lineCoarseRestrictSuTwo n (bondE n W) c0 = W c0 := by
  classical
  obtain ⟨⟨z, hz⟩, μ⟩ := c0
  unfold lineCoarseRestrictSuTwo bondE
  simp only
  have h1 : ∑ x ∈ blockOf z n, ∑ i ∈ range n, ∑ c : CoarseBond L n, bK n (pathSite x μ i) μ c • W c
      = ∑ c : CoarseBond L n, (∑ x ∈ blockOf z n, ∑ i ∈ range n, bK n (pathSite x μ i) μ c) • W c := by
    have hx : ∀ x : PeriodicLatticeSite L, ∑ i ∈ range n, ∑ c : CoarseBond L n, bK n (pathSite x μ i) μ c • W c
        = ∑ c : CoarseBond L n, (∑ i ∈ range n, bK n (pathSite x μ i) μ c) • W c := by
      intro x
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun c _ => Finset.sum_smul.symm)
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c _ => Finset.sum_smul.symm)
  rw [h1]
  simp only [block_line_sum n hn hdvd z hz μ, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [smul_smul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show (1 / (n : ℝ) ^ 4) * (n : ℝ) ^ 4 = 1 by field_simp, one_smul]

#print axioms fin_sub_val
#print axioms dvd_sub_val
#print axioms block_reindex
#print axioms coord_fit
#print axioms line_factor
#print axioms ind_factor
#print axioms line_prod
#print axioms blockOf_pi
#print axioms block_line_sum
#print axioms bondE_rightInv

end AdalyFormal.M0Finish
