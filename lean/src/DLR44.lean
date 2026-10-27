import DLR43
import MF5c

/-!
# DL44 -- the profile-GENERIC flat bond right inverse (MF5c with arbitrary profiles), instantiated with the SMOOTH profiles

`gbondE g h n W (x, μ) = Σ_c gbK g h n x μ c • W c`, `gbK = [c.2 = μ] · Π_ν gfac g h μ ν ((x_ν − y_ν) mod)` (`y = c.1`,
`gfac = g` along the bond direction, `h` transversally).  For `g` with the two line-average moments and `h` with mass `n`:
* **`gbondE_rightInv`** : `lineCoarseRestrictSuTwo n (gbondE g h n W) c = W c` (the flat top-level `Q₁ E = id`).
* `sbondE n := gbondE (tprof n) (pprof n) n` (DL43): **`sbondE_rightInv`**.
MF5c's `bondE` is the instance `g = gprof n`, `h = 1_{[0,n)}` (discontinuous at block faces); the proofs are MF5c's, profile-generic.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.DLayer

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.M0Finish (fin_sub_val dvd_sub_val block_reindex coord_fit blockOf_pi)

variable {L : PeriodicLatticeExtent}

/-- the 1D factor in direction `ν` of the kernel for bonds of direction `μ` -/
noncomputable def gfac (g h : ℕ → ℝ) (μ ν : Fin 3) (t : ℕ) : ℝ := if ν = μ then g t else h t

noncomputable def gbK (g h : ℕ → ℝ) (n : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) (c : CoarseBond L n) : ℝ :=
  if c.2 = μ then ∏ ν : Fin 3, gfac g h μ ν ((x ν - c.1.1 ν).val) else 0

/-- the profile-generic flat bond right inverse -/
noncomputable def gbondE (g h : ℕ → ℝ) (n : ℕ) (W : CoarseBond L n → SuTwo) : Bond L → SuTwo :=
  fun b => ∑ c : CoarseBond L n, gbK g h n b.1 b.2 c • W c

/-- the line factor: own block only, weight `n²` -/
theorem line_factor_g (g : ℕ → ℝ) {M n : ℕ} (hz : ∀ t, n ≤ t → g t = 0)
    (m1 : ∑ s ∈ range n, ((s : ℝ) + 1) * g s = (n : ℝ) ^ 2)
    (m2 : ∑ s ∈ range n, ((n : ℝ) - 1 - (s : ℝ)) * g s = 0)
    (hn : 0 < n) (hnN : n ∣ M + 1) (z y : Fin (M + 1)) (hz' : n ∣ z.val) (hy : n ∣ y.val) :
    ∑ a ∈ univ.filter (fun a : Fin (M + 1) => z.val ≤ a.val ∧ a.val < z.val + n),
      ∑ i ∈ range n, g ((a + i • (1 : Fin (M + 1)) - y).val) = if z = y then (n : ℝ) ^ 2 else 0 := by
  set D := (z - y).val with hD
  have hDd : n ∣ D := dvd_sub_val hnN z y hz' hy
  have hDN : D < M + 1 := (z - y).isLt
  have hval : ∀ a : Fin (M + 1), ∀ i : ℕ, z.val ≤ a.val →
      (a + i • (1 : Fin (M + 1)) - y).val = (D + (a.val - z.val) + i) % (M + 1) := by
    intro a i hza
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
  have hfit := coord_fit hn hnN z hz'
  have hstep : ∑ a ∈ univ.filter (fun a : Fin (M + 1) => z.val ≤ a.val ∧ a.val < z.val + n),
      ∑ i ∈ range n, g ((a + i • (1 : Fin (M + 1)) - y).val)
      = ∑ a ∈ univ.filter (fun a : Fin (M + 1) => z.val ≤ a.val ∧ a.val < z.val + n),
          (fun v : ℕ => ∑ i ∈ range n, g ((D + (v - z.val) + i) % (M + 1))) a.val := by
    refine sum_congr rfl (fun a ha => ?_)
    simp only [mem_filter, mem_univ, true_and] at ha
    refine sum_congr rfl (fun i _ => ?_)
    rw [hval a i ha.1]
  rw [hstep, block_reindex n z hfit (fun v : ℕ => ∑ i ∈ range n, g ((D + (v - z.val) + i) % (M + 1)))]
  have e2 : ∀ r ∈ range n, (fun v : ℕ => ∑ i ∈ range n, g ((D + (v - z.val) + i) % (M + 1))) (z.val + r)
      = ∑ i ∈ range n, g ((D + r + i) % (M + 1)) := by
    intro r _; simp
  rw [sum_congr rfl e2, core_line_g g (M + 1) n D hz m1 m2 hn hnN hDd hDN]
  have hiff : D = 0 ↔ z = y := by
    rw [hD, Fin.val_eq_zero_iff, sub_eq_zero]
  by_cases h : z = y
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

/-- the transverse factor: weight `n` -/
theorem ind_factor_g (h : ℕ → ℝ) {M n : ℕ} (hz : ∀ t, n ≤ t → h t = 0) (m0 : ∑ s ∈ range n, h s = (n : ℝ))
    (hn : 0 < n) (hnN : n ∣ M + 1) (z y : Fin (M + 1)) (hz' : n ∣ z.val) (hy : n ∣ y.val) :
    ∑ a ∈ univ.filter (fun a : Fin (M + 1) => z.val ≤ a.val ∧ a.val < z.val + n),
      h ((a - y).val) = if z = y then (n : ℝ) else 0 := by
  set D := (z - y).val with hD
  have hDd : n ∣ D := dvd_sub_val hnN z y hz' hy
  have hDN : D < M + 1 := (z - y).isLt
  have hfit := coord_fit hn hnN z hz'
  have hstep : ∑ a ∈ univ.filter (fun a : Fin (M + 1) => z.val ≤ a.val ∧ a.val < z.val + n), h ((a - y).val)
      = ∑ a ∈ univ.filter (fun a : Fin (M + 1) => z.val ≤ a.val ∧ a.val < z.val + n),
          (fun v : ℕ => h ((D + (v - z.val)) % (M + 1))) a.val := by
    refine sum_congr rfl (fun a ha => ?_)
    simp only [mem_filter, mem_univ, true_and] at ha
    have : (a - y).val = (D + (a.val - z.val)) % (M + 1) := by
      rw [fin_sub_val, hD, fin_sub_val, Nat.mod_add_mod]
      congr 1; omega
    rw [this]
  rw [hstep, block_reindex n z hfit (fun v : ℕ => h ((D + (v - z.val)) % (M + 1)))]
  have e2 : ∀ r ∈ range n, (fun v : ℕ => h ((D + (v - z.val)) % (M + 1))) (z.val + r) = h ((D + r) % (M + 1)) := by
    intro r _; simp
  rw [sum_congr rfl e2, core_ind_g h (M + 1) n D hz m0 hn hnN hDd hDN]
  have hiff : D = 0 ↔ z = y := by
    rw [hD, Fin.val_eq_zero_iff, sub_eq_zero]
  by_cases hh : z = y
  · rw [if_pos (hiff.mpr hh), if_pos hh]
  · rw [if_neg (fun h' => hh (hiff.mp h')), if_neg hh]

/-- the per-coordinate factor after the line sum -/
noncomputable def Hfg (g h : ℕ → ℝ) (n : ℕ) (μ : Fin 3) (y : PeriodicLatticeSite L) (ν : Fin 3) (a : Fin (L ν + 1)) : ℝ :=
  if ν = μ then ∑ i ∈ range n, gfac g h μ ν ((a + i • (1 : Fin (L ν + 1)) - y ν).val) else gfac g h μ ν ((a - y ν).val)

theorem line_prod_g (g h : ℕ → ℝ) (n : ℕ) (x y : PeriodicLatticeSite L) (μ : Fin 3) :
    ∑ i ∈ range n, ∏ ν : Fin 3, gfac g h μ ν (((pathSite x μ i) ν - y ν).val) = ∏ ν : Fin 3, Hfg g h n μ y ν (x ν) := by
  have hL : ∀ i, ∏ ν : Fin 3, gfac g h μ ν (((pathSite x μ i) ν - y ν).val)
      = gfac g h μ μ ((x μ + i • (1 : Fin (L μ + 1)) - y μ).val)
        * ∏ ν ∈ ({μ}ᶜ : Finset (Fin 3)), gfac g h μ ν ((x ν - y ν).val) := by
    intro i
    rw [Fintype.prod_eq_mul_prod_compl μ]
    congr 1
    · rw [AdalyFormal.Balaban.ReparamCDisjoint.pathSite_eq, Function.update_self]
    · refine Finset.prod_congr rfl (fun ν hν => ?_)
      have hne : ν ≠ μ := by simpa [Finset.mem_compl, Finset.mem_singleton] using hν
      rw [AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_ne x μ ν i hne]
  have hR : ∏ ν : Fin 3, Hfg g h n μ y ν (x ν)
      = (∑ i ∈ range n, gfac g h μ μ ((x μ + i • (1 : Fin (L μ + 1)) - y μ).val))
        * ∏ ν ∈ ({μ}ᶜ : Finset (Fin 3)), gfac g h μ ν ((x ν - y ν).val) := by
    rw [Fintype.prod_eq_mul_prod_compl μ]
    congr 1
    · simp [Hfg]
    · refine Finset.prod_congr rfl (fun ν hν => ?_)
      have hne : ν ≠ μ := by simpa [Finset.mem_compl, Finset.mem_singleton] using hν
      simp only [Hfg, if_neg hne]
  rw [hR, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => hL i)

/-- **the block-line sum of the kernel**: `n⁴` on the own coarse bond, `0` elsewhere. -/
theorem block_line_sum_g (g h : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν, n ∣ L ν + 1)
    (hgz : ∀ t, n ≤ t → g t = 0) (m1 : ∑ s ∈ range n, ((s : ℝ) + 1) * g s = (n : ℝ) ^ 2)
    (m2 : ∑ s ∈ range n, ((n : ℝ) - 1 - (s : ℝ)) * g s = 0)
    (hhz : ∀ t, n ≤ t → h t = 0) (m0 : ∑ s ∈ range n, h s = (n : ℝ))
    (z : PeriodicLatticeSite L) (hz : z ∈ CoarseLattice L n) (μ : Fin 3) (c : CoarseBond L n) :
    ∑ x ∈ blockOf z n, ∑ i ∈ range n, gbK g h n (pathSite x μ i) μ c
      = if c = (⟨z, hz⟩, μ) then (n : ℝ) ^ 4 else 0 := by
  classical
  by_cases hc : c.2 = μ
  · have hzd : ∀ ν, n ∣ (z ν).val := fun ν => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hz ν)
    have hyd : ∀ ν, n ∣ (c.1.1 ν).val := fun ν => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp c.1.2 ν)
    have h1 : ∀ x ∈ blockOf z n, ∑ i ∈ range n, gbK g h n (pathSite x μ i) μ c
        = ∏ ν : Fin 3, Hfg g h n μ c.1.1 ν (x ν) := by
      intro x _
      simp only [gbK, if_pos hc]
      exact line_prod_g g h n x c.1.1 μ
    rw [sum_congr rfl h1, blockOf_pi, ← Finset.prod_univ_sum]
    have hfac : ∀ ν : Fin 3, ∑ a ∈ univ.filter (fun a : Fin (L ν + 1) => (z ν).val ≤ a.val ∧ a.val < (z ν).val + n),
        Hfg g h n μ c.1.1 ν a = if z ν = c.1.1 ν then (if ν = μ then (n : ℝ) ^ 2 else (n : ℝ)) else 0 := by
      intro ν
      by_cases hνμ : ν = μ
      · simp only [Hfg, if_pos hνμ, gfac]
        rw [line_factor_g g hgz m1 m2 hn (hdvd ν) (z ν) (c.1.1 ν) (hzd ν) (hyd ν)]
      · simp only [Hfg, if_neg hνμ, gfac]
        rw [ind_factor_g h hhz m0 hn (hdvd ν) (z ν) (c.1.1 ν) (hzd ν) (hyd ν)]
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
        intro hh; apply hzy; rw [hh]
      rw [if_neg hce]
      have : ∃ ν, z ν ≠ c.1.1 ν := by
        by_contra hall; push_neg at hall; exact hzy (funext hall)
      obtain ⟨ν, hν⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_univ ν) (by rw [if_neg hν])
  · have h0 : ∀ x ∈ blockOf z n, ∑ i ∈ range n, gbK g h n (pathSite x μ i) μ c = 0 := by
      intro x _; simp [gbK, hc]
    rw [sum_congr rfl h0, sum_const_zero, if_neg]
    intro hh; apply hc; rw [hh]

/-- **`Q_k(1) E = id`** for the profile-generic right inverse. -/
theorem gbondE_rightInv (g h : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν, n ∣ L ν + 1)
    (hgz : ∀ t, n ≤ t → g t = 0) (m1 : ∑ s ∈ range n, ((s : ℝ) + 1) * g s = (n : ℝ) ^ 2)
    (m2 : ∑ s ∈ range n, ((n : ℝ) - 1 - (s : ℝ)) * g s = 0)
    (hhz : ∀ t, n ≤ t → h t = 0) (m0 : ∑ s ∈ range n, h s = (n : ℝ))
    (W : CoarseBond L n → SuTwo) (c0 : CoarseBond L n) :
    lineCoarseRestrictSuTwo n (gbondE g h n W) c0 = W c0 := by
  classical
  obtain ⟨⟨z, hz⟩, μ⟩ := c0
  unfold lineCoarseRestrictSuTwo gbondE
  simp only
  have h1 : ∑ x ∈ blockOf z n, ∑ i ∈ range n, ∑ c : CoarseBond L n, gbK g h n (pathSite x μ i) μ c • W c
      = ∑ c : CoarseBond L n, (∑ x ∈ blockOf z n, ∑ i ∈ range n, gbK g h n (pathSite x μ i) μ c) • W c := by
    have hx : ∀ x : PeriodicLatticeSite L, ∑ i ∈ range n, ∑ c : CoarseBond L n, gbK g h n (pathSite x μ i) μ c • W c
        = ∑ c : CoarseBond L n, (∑ i ∈ range n, gbK g h n (pathSite x μ i) μ c) • W c := by
      intro x
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun c _ => Finset.sum_smul.symm)
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c _ => Finset.sum_smul.symm)
  rw [h1]
  simp only [block_line_sum_g g h n hn hdvd hgz m1 m2 hhz m0 z hz μ, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [smul_smul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show (1 / (n : ℝ) ^ 4) * (n : ℝ) ^ 4 = 1 by field_simp, one_smul]

/-- the SMOOTH flat bond right inverse -/
noncomputable def sbondE (n : ℕ) (W : CoarseBond L n → SuTwo) : Bond L → SuTwo := gbondE (tprof n) (pprof n) n W

/-- **`Q_k(1) (sbondE W) = W`** -/
theorem sbondE_rightInv (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν, n ∣ L ν + 1) (W : CoarseBond L n → SuTwo)
    (c0 : CoarseBond L n) : lineCoarseRestrictSuTwo n (sbondE n W) c0 = W c0 :=
  gbondE_rightInv (tprof n) (pprof n) n hn hdvd (tprof_eq_zero n) (tprof_moment_own n) (tprof_moment_next n)
    (pprof_eq_zero n) (pprof_sum n) W c0

#print axioms line_factor_g
#print axioms ind_factor_g
#print axioms line_prod_g
#print axioms block_line_sum_g
#print axioms gbondE_rightInv
#print axioms sbondE_rightInv

end AdalyFormal.DLayer
