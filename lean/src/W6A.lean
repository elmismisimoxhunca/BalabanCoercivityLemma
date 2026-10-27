import W6P3

/-!
# W6A -- generic-moment block line sums and the UPPER profile (W6 lane, 2026-10-13)

For a profile `g` supported in `[0,n)` write `own g = Σ_{s<n} (s+1) g s` and `nxt g = Σ_{s<n} (n−1−s) g s`.
* `core_line_gen` : `Σ_{r<n} Σ_{i<n} g((D+r+i) mod N) = [D = 0]·own g + [(D+n) mod N = 0]·nxt g` (no moment hypothesis).
* `line_factor_gen` : the same on a block coordinate (`z`, `y` aligned), with the second condition read as `(z+n) mod N = y`.
* **`block_line_sum_gen`** : the `n`-line average of the product kernel `gbK g h n · c` over the block of `z` is
  `[c = (z,μ)]·n²·own g + [c = (z⁺,μ)]·n²·nxt g` (`z⁺ = z + n e_μ`, `h` of mass `n`).
* `uprof n = (2n·pprof n − (n+1)·tprof n)/(n−1)` : `own uprof = 0`, `nxt uprof = n²` (`n ≥ 2`), and `SProf n uprof 33 240`.
  (A kernel with this profile on the block of `z⁺` is seen with weight `n⁴` by the row `(z,μ)` and with weight `0` by the
  row `(z⁺,μ)`: the UPPER kernel of a row whose lower end-point is outside `Λ_j`.)
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.W6

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq coarseShift_mem_coarseLattice)
open AdalyFormal.M0Finish (fin_sub_val dvd_sub_val block_reindex coord_fit blockOf_pi pair_own pair_next cases_of_dvd
  sum_range_id_real sum_range_sq_real)
open AdalyFormal.W6P (point_cases_g gfac gbK Hfg line_prod_g ind_factor_g tprof pprof tprof_eq_zero pprof_eq_zero
  tprof_moment_own tprof_moment_next pprof_sum sum_range_cube_real SProf sprof_tprof sprof_pprof abs_tprof_le
  abs_pprof_le tprof_step_le pprof_step_le tprof_first_le tprof_last_le pprof_first_le pprof_last_le)

/-- own-block moment -/
noncomputable def ownM (n : ℕ) (g : ℕ → ℝ) : ℝ := ∑ s ∈ range n, ((s : ℝ) + 1) * g s
/-- next-block moment -/
noncomputable def nxtM (n : ℕ) (g : ℕ → ℝ) : ℝ := ∑ s ∈ range n, ((n : ℝ) - 1 - (s : ℝ)) * g s

theorem core_line_gen (g : ℕ → ℝ) (N n D : ℕ) (hz : ∀ t, n ≤ t → g t = 0)
    (hn : 0 < n) (hN : n ∣ N) (hD : n ∣ D) (hDN : D < N) :
    ∑ r ∈ range n, ∑ i ∈ range n, g ((D + r + i) % N)
      = (if D = 0 then ownM n g else 0) + (if (D + n) % N = 0 then nxtM n g else 0) := by
  have hc := cases_of_dvd N n D hn hN hD hDN
  have hpt : ∀ r ∈ range n, ∀ i ∈ range n, g ((D + r + i) % N)
      = (if D = 0 then (if r + i < n then g (r + i) else 0) else 0)
        + (if (D + n) % N = 0 then (if n ≤ r + i then g (r + i - n) else 0) else 0) :=
    fun r hr i hi => point_cases_g g N n D r i hz (mem_range.mp hr) (mem_range.mp hi) hc
  rw [sum_congr rfl (fun r hr => sum_congr rfl (fun i hi => hpt r hr i hi))]
  simp only [sum_add_distrib]
  congr 1
  · split_ifs with h
    · rw [pair_own g n]; rfl
    · simp
  · split_ifs with h
    · rw [pair_next g n]; rfl
    · simp

/-- `(D + n) mod N = 0` for `D = (z − y) mod N` is the statement `y = z + n` on the cycle. -/
theorem next_iff {N : ℕ} [NeZero N] (n : ℕ) (z y : Fin N) :
    ((z - y).val + n) % N = 0 ↔ (z.val + n) % N = y.val := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hy := y.isLt
  have e1 : ((z - y).val + n) % N = ((z.val + n) % N + (N - y.val)) % N := by
    rw [fin_sub_val, Nat.mod_add_mod, Nat.mod_add_mod]
    congr 1; omega
  rw [e1]
  set a := (z.val + n) % N with ha
  have haN : a < N := Nat.mod_lt _ hNpos
  constructor
  · intro h
    by_contra hne
    rcases Nat.lt_or_ge a y.val with hlt | hge
    · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h; omega
  · intro h
    rw [h, show y.val + (N - y.val) = N by omega, Nat.mod_self]

theorem line_factor_gen (g : ℕ → ℝ) {M n : ℕ} (hz : ∀ t, n ≤ t → g t = 0)
    (hn : 0 < n) (hnN : n ∣ M + 1) (z y : Fin (M + 1)) (hz' : n ∣ z.val) (hy : n ∣ y.val) :
    ∑ a ∈ univ.filter (fun a : Fin (M + 1) => z.val ≤ a.val ∧ a.val < z.val + n),
      ∑ i ∈ range n, g ((a + i • (1 : Fin (M + 1)) - y).val)
      = (if z = y then ownM n g else 0) + (if (z.val + n) % (M + 1) = y.val then nxtM n g else 0) := by
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
  rw [sum_congr rfl e2, core_line_gen g (M + 1) n D hz hn hnN hDd hDN]
  have hiff : D = 0 ↔ z = y := by
    rw [hD, Fin.val_eq_zero_iff, sub_eq_zero]
  have hiff2 : (D + n) % (M + 1) = 0 ↔ (z.val + n) % (M + 1) = y.val := next_iff n z y
  congr 1
  · by_cases h : z = y
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  · by_cases h : (z.val + n) % (M + 1) = y.val
    · rw [if_pos (hiff2.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff2.mp h')), if_neg h]

/-- the coarse bond one block up in its own direction -/
def cbUp {L : PeriodicLatticeExtent} (n : ℕ) (hdvd : ∀ ν, n ∣ L ν + 1) (c : CoarseBond L n) : CoarseBond L n :=
  (⟨coarseShift c.1.1 n c.2, coarseShift_mem_coarseLattice hdvd c.1.2 c.2⟩, c.2)

/-- **the block-line sum of a product kernel with ARBITRARY longitudinal moments**. -/
theorem block_line_sum_gen {L : PeriodicLatticeExtent} (g h : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν, n ∣ L ν + 1)
    (hgz : ∀ t, n ≤ t → g t = 0) (hhz : ∀ t, n ≤ t → h t = 0) (m0 : ∑ s ∈ range n, h s = (n : ℝ))
    (z : PeriodicLatticeSite L) (hz : z ∈ CoarseLattice L n) (μ : Fin 3) (c : CoarseBond L n) :
    ∑ x ∈ blockOf z n, ∑ i ∈ range n, gbK g h n (pathSite x μ i) μ c
      = (if c = (⟨z, hz⟩, μ) then (n : ℝ) ^ 2 * ownM n g else 0)
        + (if c = cbUp n hdvd (⟨z, hz⟩, μ) then (n : ℝ) ^ 2 * nxtM n g else 0) := by
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
    set F : ℝ := (if z μ = c.1.1 μ then ownM n g else 0)
        + (if ((z μ).val + n) % (L μ + 1) = (c.1.1 μ).val then nxtM n g else 0) with hF
    have hfacμ : ∑ a ∈ univ.filter (fun a : Fin (L μ + 1) => (z μ).val ≤ a.val ∧ a.val < (z μ).val + n),
        Hfg g h n μ c.1.1 μ a = F := by
      simp only [Hfg, gfac]
      exact line_factor_gen g hgz hn (hdvd μ) (z μ) (c.1.1 μ) (hzd μ) (hyd μ)
    have hfacν : ∀ ν, ν ≠ μ → ∑ a ∈ univ.filter (fun a : Fin (L ν + 1) => (z ν).val ≤ a.val ∧ a.val < (z ν).val + n),
        Hfg g h n μ c.1.1 ν a = if z ν = c.1.1 ν then (n : ℝ) else 0 := by
      intro ν hνμ
      simp only [Hfg, if_neg hνμ, gfac]
      exact ind_factor_g h hhz m0 hn (hdvd ν) (z ν) (c.1.1 ν) (hzd ν) (hyd ν)
    rw [Fintype.prod_eq_mul_prod_compl μ, hfacμ]
    rw [Finset.prod_congr rfl (fun ν hν => hfacν ν (by simpa [Finset.mem_compl, Finset.mem_singleton] using hν))]
    have hcard : (({μ}ᶜ : Finset (Fin 3))).card = 2 := by
      rw [Finset.card_compl, Finset.card_singleton]; rfl
    by_cases hoff : ∀ ν, ν ≠ μ → z ν = c.1.1 ν
    · have hP : ∏ ν ∈ ({μ}ᶜ : Finset (Fin 3)), (if z ν = c.1.1 ν then (n : ℝ) else 0) = (n : ℝ) ^ 2 := by
        rw [Finset.prod_congr rfl (fun ν hν => by
          rw [if_pos (hoff ν (by simpa [Finset.mem_compl, Finset.mem_singleton] using hν))]), Finset.prod_const, hcard]
      rw [hP]
      have hA : c = (⟨z, hz⟩, μ) ↔ z μ = c.1.1 μ := by
        constructor
        · intro hh; rw [hh]
        · intro hh
          obtain ⟨⟨y, hy⟩, μ'⟩ := c
          simp only at hc hh hoff
          subst hc
          have : y = z := by
            funext ν
            by_cases hν : ν = μ'
            · subst hν; exact hh.symm
            · exact (hoff ν hν).symm
          subst this; rfl
      have hB : c = cbUp n hdvd (⟨z, hz⟩, μ) ↔ ((z μ).val + n) % (L μ + 1) = (c.1.1 μ).val := by
        constructor
        · intro hh; rw [hh]; simp only [cbUp]; rw [coarseShift_val_eq]
        · intro hh
          obtain ⟨⟨y, hy⟩, μ'⟩ := c
          simp only at hc hh hoff
          subst hc
          simp only [cbUp, Prod.mk.injEq, and_true]
          apply Subtype.ext
          funext ν
          by_cases hν : ν = μ'
          · subst hν; apply Fin.ext; rw [coarseShift_val_eq]; exact hh.symm
          · show y ν = coarseShift z n μ' ν
            rw [coarseShift_apply_ne _ _ _ _ hν]; exact (hoff ν hν).symm
      rw [hF]
      by_cases h1 : z μ = c.1.1 μ
      · rw [if_pos h1, if_pos (hA.mpr h1)]
        by_cases h2 : ((z μ).val + n) % (L μ + 1) = (c.1.1 μ).val
        · rw [if_pos h2, if_pos (hB.mpr h2)]; ring
        · rw [if_neg h2, if_neg (fun hh => h2 (hB.mp hh))]; ring
      · rw [if_neg h1, if_neg (fun hh => h1 (hA.mp hh))]
        by_cases h2 : ((z μ).val + n) % (L μ + 1) = (c.1.1 μ).val
        · rw [if_pos h2, if_pos (hB.mpr h2)]; ring
        · rw [if_neg h2, if_neg (fun hh => h2 (hB.mp hh))]; ring
    · push Not at hoff
      obtain ⟨ν, hνμ, hν⟩ := hoff
      have hP : ∏ ν ∈ ({μ}ᶜ : Finset (Fin 3)), (if z ν = c.1.1 ν then (n : ℝ) else 0) = 0 :=
        Finset.prod_eq_zero (by simpa [Finset.mem_compl, Finset.mem_singleton] using hνμ) (by rw [if_neg hν])
      rw [hP, mul_zero]
      have hA : ¬ c = (⟨z, hz⟩, μ) := by intro hh; apply hν; rw [hh]
      have hB : ¬ c = cbUp n hdvd (⟨z, hz⟩, μ) := by
        intro hh; apply hν; rw [hh]; simp only [cbUp]; rw [coarseShift_apply_ne _ _ _ _ hνμ]
      rw [if_neg hA, if_neg hB]; ring
  · have h0 : ∀ x ∈ blockOf z n, ∑ i ∈ range n, gbK g h n (pathSite x μ i) μ c = 0 := by
      intro x _; simp [gbK, hc]
    rw [sum_congr rfl h0, sum_const_zero, if_neg, if_neg]
    · simp
    · intro hh; apply hc; rw [hh]; rfl
    · intro hh; apply hc; rw [hh]

/-! ## the upper profile -/

/-- `uprof n = (2n·pprof n − (n+1)·tprof n)/(n−1)` -/
noncomputable def uprof (n t : ℕ) : ℝ := (2 * (n : ℝ) * pprof n t - ((n : ℝ) + 1) * tprof n t) / ((n : ℝ) - 1)

theorem uprof_eq_zero (n t : ℕ) (h : n ≤ t) : uprof n t = 0 := by
  unfold uprof; rw [pprof_eq_zero n t h, tprof_eq_zero n t h]; simp

theorem pprof_own (n : ℕ) : ownM n (pprof n) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  unfold ownM
  have hD : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  have h : ∀ s ∈ range n, ((s : ℝ) + 1) * pprof n s
      = (6 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) * ((-1) * (s : ℝ) ^ 3 + ((n : ℝ) - 2) * (s : ℝ) ^ 2
          + (2 * (n : ℝ) - 1) * (s : ℝ) + (n : ℝ)) := by
    intro s hs
    rw [pprof, if_pos (mem_range.mp hs)]
    field_simp; ring
  rw [sum_congr rfl h, ← mul_sum]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  rw [sum_range_cube_real, sum_range_sq_real, sum_range_id_real]
  field_simp; ring

theorem pprof_nxt (n : ℕ) : nxtM n (pprof n) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  have hsum : ownM n (pprof n) + nxtM n (pprof n) = (n : ℝ) * (n : ℝ) := by
    unfold ownM nxtM
    rw [← sum_add_distrib]
    have : ∀ s ∈ range n, ((s : ℝ) + 1) * pprof n s + ((n : ℝ) - 1 - (s : ℝ)) * pprof n s = (n : ℝ) * pprof n s := by
      intro s _; ring
    rw [sum_congr rfl this, ← mul_sum, pprof_sum]
  rw [pprof_own] at hsum
  linarith

theorem uprof_own (n : ℕ) (hn : 2 ≤ n) : ownM n (uprof n) = 0 := by
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold ownM uprof
  have : ∀ s ∈ range n, ((s : ℝ) + 1) * ((2 * (n : ℝ) * pprof n s - ((n : ℝ) + 1) * tprof n s) / ((n : ℝ) - 1))
      = (2 * (n : ℝ) / ((n : ℝ) - 1)) * (((s : ℝ) + 1) * pprof n s)
        - (((n : ℝ) + 1) / ((n : ℝ) - 1)) * (((s : ℝ) + 1) * tprof n s) := by
    intro s _; field_simp
  rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, ← mul_sum]
  have h1 := pprof_own n
  have h2 := tprof_moment_own n
  unfold ownM at h1
  rw [h1, h2]
  field_simp; ring

theorem uprof_nxt (n : ℕ) (hn : 2 ≤ n) : nxtM n (uprof n) = (n : ℝ) ^ 2 := by
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold nxtM uprof
  have : ∀ s ∈ range n, ((n : ℝ) - 1 - (s : ℝ)) * ((2 * (n : ℝ) * pprof n s - ((n : ℝ) + 1) * tprof n s) / ((n : ℝ) - 1))
      = (2 * (n : ℝ) / ((n : ℝ) - 1)) * (((n : ℝ) - 1 - (s : ℝ)) * pprof n s)
        - (((n : ℝ) + 1) / ((n : ℝ) - 1)) * (((n : ℝ) - 1 - (s : ℝ)) * tprof n s) := by
    intro s _; field_simp
  rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, ← mul_sum]
  have h1 := pprof_nxt n
  have h2 := tprof_moment_next n
  unfold nxtM at h1
  rw [h1, h2]
  field_simp; ring

theorem tprof_own (n : ℕ) : ownM n (tprof n) = (n : ℝ) ^ 2 := tprof_moment_own n
theorem tprof_nxt (n : ℕ) : nxtM n (tprof n) = 0 := tprof_moment_next n

/-- the two-term bound used for every `uprof` estimate. -/
theorem abs_comb_le (n : ℕ) (hn : 2 ≤ n) (a b A B : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |(2 * (n : ℝ) * a - ((n : ℝ) + 1) * b) / ((n : ℝ) - 1)| ≤ (2 * (n : ℝ) * A + ((n : ℝ) + 1) * B) / ((n : ℝ) - 1) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  rw [abs_div, abs_of_pos hpos]
  apply div_le_div_of_nonneg_right _ hpos.le
  calc |2 * (n : ℝ) * a - ((n : ℝ) + 1) * b| ≤ |2 * (n : ℝ) * a| + |((n : ℝ) + 1) * b| := abs_sub _ _
    _ = 2 * (n : ℝ) * |a| + ((n : ℝ) + 1) * |b| := by
        have h1 : (0 : ℝ) ≤ n := by positivity
        have h2 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h2, abs_of_nonneg h1]; norm_num
    _ ≤ 2 * (n : ℝ) * A + ((n : ℝ) + 1) * B := by
        have h1 : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
        have h2 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left ha h1, mul_le_mul_of_nonneg_left hb h2]

theorem abs_uprof_le (n t : ℕ) (hn : 2 ≤ n) : |uprof n t| ≤ 33 := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  refine (abs_comb_le n hn _ _ (3 / 2) 9 (abs_pprof_le n t) (abs_tprof_le n t)).trans ?_
  rw [div_le_iff₀ hpos]; nlinarith

/-- steps of `uprof` are `≤ 240/n`. -/
theorem uprof_step_le (n t : ℕ) (hn : 2 ≤ n) (h : t + 1 < n) : |uprof n (t + 1) - uprof n t| ≤ 240 / n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have e : uprof n (t + 1) - uprof n t
      = (2 * (n : ℝ) * (pprof n (t + 1) - pprof n t) - ((n : ℝ) + 1) * (tprof n (t + 1) - tprof n t)) / ((n : ℝ) - 1) := by
    unfold uprof; field_simp; ring
  rw [e]
  refine (abs_comb_le n hn _ _ (6 / n) (72 / n) (pprof_step_le n t h) (tprof_step_le n t h)).trans ?_
  rw [div_le_div_iff₀ hpos hnp]
  have : 2 * (n : ℝ) * (6 / n) = 12 := by field_simp; norm_num
  rw [this]
  have h72 : ((n : ℝ) + 1) * (72 / n) ≤ 108 := by
    rw [mul_div_assoc', div_le_iff₀ hnp]; nlinarith
  nlinarith

theorem uprof_first_le (n : ℕ) (hn : 2 ≤ n) : |uprof n 0| ≤ 240 / n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  refine (abs_comb_le n hn _ _ (6 / n) (72 / n) (pprof_first_le n (by omega)) (tprof_first_le n (by omega))).trans ?_
  rw [div_le_div_iff₀ hpos hnp]
  have : 2 * (n : ℝ) * (6 / n) = 12 := by field_simp; norm_num
  rw [this]
  have h72 : ((n : ℝ) + 1) * (72 / n) ≤ 108 := by
    rw [mul_div_assoc', div_le_iff₀ hnp]; nlinarith
  nlinarith

theorem uprof_last_le (n : ℕ) (hn : 2 ≤ n) : |uprof n (n - 1)| ≤ 240 / n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  refine (abs_comb_le n hn _ _ (6 / n) (72 / n) (pprof_last_le n (by omega)) (tprof_last_le n (by omega))).trans ?_
  rw [div_le_div_iff₀ hpos hnp]
  have : 2 * (n : ℝ) * (6 / n) = 12 := by field_simp; norm_num
  rw [this]
  have h72 : ((n : ℝ) + 1) * (72 / n) ≤ 108 := by
    rw [mul_div_assoc', div_le_iff₀ hnp]; nlinarith
  nlinarith

theorem sprof_uprof (n : ℕ) (hn : 2 ≤ n) : SProf n (uprof n) 33 240 :=
  ⟨by omega, uprof_eq_zero n, fun t => abs_uprof_le n t hn, fun t h => uprof_step_le n t hn h,
    uprof_first_le n hn, uprof_last_le n hn⟩

end AdalyFormal.W6

#print axioms AdalyFormal.W6.core_line_gen
#print axioms AdalyFormal.W6.next_iff
#print axioms AdalyFormal.W6.line_factor_gen
#print axioms AdalyFormal.W6.cbUp
#print axioms AdalyFormal.W6.block_line_sum_gen
#print axioms AdalyFormal.W6.uprof
#print axioms AdalyFormal.W6.uprof_eq_zero
#print axioms AdalyFormal.W6.pprof_own
#print axioms AdalyFormal.W6.pprof_nxt
#print axioms AdalyFormal.W6.uprof_own
#print axioms AdalyFormal.W6.uprof_nxt
#print axioms AdalyFormal.W6.tprof_own
#print axioms AdalyFormal.W6.tprof_nxt
#print axioms AdalyFormal.W6.abs_comb_le
#print axioms AdalyFormal.W6.abs_uprof_le
#print axioms AdalyFormal.W6.uprof_step_le
#print axioms AdalyFormal.W6.uprof_first_le
#print axioms AdalyFormal.W6.uprof_last_le
#print axioms AdalyFormal.W6.sprof_uprof
