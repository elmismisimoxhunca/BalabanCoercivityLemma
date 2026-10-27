import M1A

/-!
# M1G2 -- G2 `stratWeight` + `strat_geom_sum`: a stratum-adapted Combes–Thomas weight with a k-flat geometric sum
(M1 lane B, 2026-10-13)

`StratLip S k ell θ φ` : `|φ(x+e_μ) − φ(x)| ≤ θ ell^{-bstrat(x,μ)}` on every bond (position-dependent `WtLip`; the both-endpoint
stratum, plan D4; plan = `compute/plan_m1m2_20261012/PLAN.md`).  `stratLip_site`: with G1 this gives `|φ(x+e_μ) − φ(x)| ≤ θ ell · ell^{-strat x}`.
The explicit weight centred at a site `c` of stratum `s` (`stratWeight`):
  `V_c(x) = min_{m ∈ [s+1, k+1]} ( |c − x| ell^{-m} + (m − s − 1) R M / 2 )`,   `φ_c = θ V_c`.
* `stratWeight_self`: `V_c(c) = 0`;  `stratWeight_lip`: `StratLip` with constant `1` for `V_c`, i.e. `θ V_c` is `StratLip θ` (needs `Admissible`, `2 ≤ ell`).  Mechanism: on a bond
  of stratum `b ≥ s+2` both ends are at distance `> R M ell^{b-1}` from `c` (collar), and there the terms `m < b` are dominated by `m = b`
  (Bernoulli, `ell ≥ 2`); on a bond of stratum `≤ s+1` every term has slope `≤ ell^{-(s+1)} ≤ ell^{-b}`.
* `exp_pdist_sum`: `Σ_x e^{-a|c−x|} ≤ (2/(1 − e^{-a}))³`;  `strat_geom_sum`:
  `Σ_x e^{-2θ V_c(x)} ≤ Σ_{m=s+1}^{k+1} e^{-θ(m−s−1) R M} (2 + ell^m/θ)³`;
* `strat_geom_sum_flat`: if `ell³ e^{-θ R M} ≤ 1/2` (i.e. `θ R M ≥ 3 ln ell + ln 2`), `Σ_x e^{-2θ V_c(x)} ≤ 64 + 8 ell³ (ell^s/θ)³`
  -- free of `k`, the torus and the tower.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_shift_le pdist_triangle pdist_self pcd_comm)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

/-- position-dependent Lipschitz weight: `|φ(x+e_μ) − φ(x)| ≤ θ ell^{-bstrat}`. -/
def StratLip (S : Tower L) (k ell : ℕ) (θ : ℝ) (φ : PeriodicLatticeSite L → ℝ) : Prop :=
  ∀ (x : PeriodicLatticeSite L) (μ : Fin 3),
    |φ (periodicLatticeShift x μ) - φ x| ≤ θ / (ell : ℝ) ^ bstrat S k (x, μ)

/-- with G1, `StratLip θ` gives the base-site form with constant `θ ell`. -/
theorem stratLip_site {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hell : 1 ≤ ell) {θ : ℝ} (hθ : 0 ≤ θ) {φ : PeriodicLatticeSite L → ℝ} (h : StratLip S k ell θ φ)
    (x : PeriodicLatticeSite L) (μ : Fin 3) :
    |φ (periodicLatticeShift x μ) - φ x| ≤ θ * ell / (ell : ℝ) ^ strat S k x := by
  refine (h x μ).trans ?_
  have hb : strat S k x ≤ bstrat S k (x, μ) + 1 := bstrat_ge hA hR hM hell (x, μ)
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hp1 : (0 : ℝ) < (ell : ℝ) ^ bstrat S k (x, μ) := by positivity
  have hp2 : (0 : ℝ) < (ell : ℝ) ^ strat S k x := by positivity
  rw [div_le_div_iff₀ hp1 hp2]
  have : (ell : ℝ) ^ strat S k x ≤ (ell : ℝ) ^ bstrat S k (x, μ) * ell := by
    rw [← pow_succ]; exact pow_le_pow_right₀ hellr hb
  nlinarith

/-- the term of index `m` of the weight. -/
noncomputable def wTerm (R M : ℕ) (ell s m : ℕ) (c x : PeriodicLatticeSite L) : ℝ :=
  (pdist c x : ℝ) / (ell : ℝ) ^ m + ((m - (s + 1) : ℕ) : ℝ) * (R * M) / 2

theorem Icc_nonempty (s k : ℕ) (h : s ≤ k) : (Finset.Icc (s + 1) (k + 1)).Nonempty :=
  ⟨s + 1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩

/-- **the stratified weight** centred at `c` (unit `θ = 1`). -/
noncomputable def stratWeight (S : Tower L) (ell M R k : ℕ) (c x : PeriodicLatticeSite L) : ℝ :=
  (Finset.Icc (strat S k c + 1) (k + 1)).inf' (Icc_nonempty _ k (strat_le S k c))
    (fun m => wTerm R M ell (strat S k c) m c x)

theorem wTerm_nonneg (R M ell s m : ℕ) (c x : PeriodicLatticeSite L) : 0 ≤ wTerm R M ell s m c x := by
  unfold wTerm; positivity

theorem stratWeight_self (S : Tower L) (ell M R k : ℕ) (c : PeriodicLatticeSite L) : stratWeight S ell M R k c c = 0 := by
  apply le_antisymm
  · refine (Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨le_rfl, by have := strat_le S k c; omega⟩)).trans ?_
    unfold wTerm; rw [pdist_self]; simp
  · exact Finset.le_inf' _ _ (fun _ _ => wTerm_nonneg _ _ _ _ _ _ _)

theorem stratWeight_nonneg (S : Tower L) (ell M R k : ℕ) (c x : PeriodicLatticeSite L) : 0 ≤ stratWeight S ell M R k c x :=
  Finset.le_inf' _ _ (fun _ _ => wTerm_nonneg _ _ _ _ _ _ _)

/-- `inf'` of functions with uniformly bounded increments has the same bound. -/
theorem inf'_lip {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (f g : ι → ℝ) (δ : ℝ) (h : ∀ i ∈ I, |f i - g i| ≤ δ) :
    |I.inf' hI f - I.inf' hI g| ≤ δ := by
  obtain ⟨i, hi, hgi⟩ := Finset.exists_mem_eq_inf' hI g
  obtain ⟨i', hi', hfi⟩ := Finset.exists_mem_eq_inf' hI f
  have h1 : I.inf' hI f ≤ f i := Finset.inf'_le _ hi
  have h2 : I.inf' hI g ≤ g i' := Finset.inf'_le _ hi'
  have a1 := abs_le.mp (h i hi)
  have a2 := abs_le.mp (h i' hi')
  rw [abs_le]; constructor <;> linarith

/-- `inf'` over `I` equals `inf'` over a subset `J` when every element of `I` is dominated by one of `J`. -/
theorem inf'_eq_of_dom {ι : Type*} (I J : Finset ι) (hI : I.Nonempty) (hJ : J.Nonempty) (hJI : J ⊆ I) (f : ι → ℝ)
    (hdom : ∀ i ∈ I, ∃ j ∈ J, f j ≤ f i) : I.inf' hI f = J.inf' hJ f := by
  apply le_antisymm
  · exact Finset.le_inf' _ _ (fun j hj => Finset.inf'_le _ (hJI hj))
  · refine Finset.le_inf' _ _ (fun i hi => ?_)
    obtain ⟨j, hj, hle⟩ := hdom i hi
    exact (Finset.inf'_le _ hj).trans hle

/-- a single term has increment `≤ ell^{-m}` along a bond. -/
theorem wTerm_lip (R M ell s m : ℕ) (hell : 1 ≤ ell) (c x : PeriodicLatticeSite L) (μ : Fin 3) :
    |wTerm R M ell s m c (periodicLatticeShift x μ) - wTerm R M ell s m c x| ≤ 1 / (ell : ℝ) ^ m := by
  unfold wTerm
  have h1e : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hp : (0 : ℝ) < (ell : ℝ) ^ m := by positivity
  have e : (pdist c (periodicLatticeShift x μ) : ℝ) / (ell : ℝ) ^ m + ((m - (s + 1) : ℕ) : ℝ) * (R * M) / 2
      - ((pdist c x : ℝ) / (ell : ℝ) ^ m + ((m - (s + 1) : ℕ) : ℝ) * (R * M) / 2)
      = ((pdist c (periodicLatticeShift x μ) : ℝ) - pdist c x) / (ell : ℝ) ^ m := by ring
  rw [e, abs_div, abs_of_pos hp]
  apply div_le_div_of_nonneg_right _ hp.le
  have t1 := pdist_triangle c x (periodicLatticeShift x μ)
  have t2 := pdist_triangle c (periodicLatticeShift x μ) x
  have t3 := pdist_shift_le x μ
  have t4 := pdist_comm (periodicLatticeShift x μ) x
  have r1 : (pdist c (periodicLatticeShift x μ) : ℝ) ≤ pdist c x + 1 := by exact_mod_cast (show _ ≤ _ by omega)
  have r2 : (pdist c x : ℝ) ≤ pdist c (periodicLatticeShift x μ) + 1 := by exact_mod_cast (show _ ≤ _ by omega)
  rw [abs_le]; constructor <;> linarith

/-- **dominance**: at a site `z` of stratum `≥ b ≥ s+2`, the term `m ∈ [s+1, b)` is `≥` the term `b` (`ell ≥ 2`). -/
theorem wTerm_dom {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hell : 2 ≤ ell)
    {c z : PeriodicLatticeSite L} {b m : ℕ} (hb : strat S k c + 2 ≤ b) (hbz : b ≤ strat S k z)
    (hm1 : strat S k c + 1 ≤ m) (hmb : m < b) :
    wTerm R M ell (strat S k c) b c z ≤ wTerm R M ell (strat S k c) m c z := by
  set s := strat S k c
  have hbk : b ≤ k := hbz.trans (strat_le S k z)
  -- collar: |c − z| > R M ell^{b-1}
  have hz : z ∈ S.Om (b - 1 + 1) := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ b)]
    exact (le_strat_iff hA (by omega) hbk z).mp hbz
  have hc : c ∉ S.Om (b - 1) := by
    intro h
    have := le_strat_of_mem (k := k) (by omega : b - 1 ≤ k) h
    omega
  have hcol := collar hA (j := b - 1) (by omega) hc hz
  have hP : (R : ℝ) * M * (ell : ℝ) ^ (b - 1) ≤ pdist c z := by
    have : R * bigSide M ell (b - 1) ≤ pdist c z := hcol.le
    unfold bigSide at this
    exact_mod_cast (show R * M * ell ^ (b - 1) ≤ pdist c z by rw [Nat.mul_assoc]; exact this)
  unfold wTerm
  set r := b - m with hr
  have hr1 : 1 ≤ r := by omega
  have hellr : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpm : (0 : ℝ) < (ell : ℝ) ^ m := by positivity
  have hpow : (ell : ℝ) ^ b = (ell : ℝ) ^ m * (ell : ℝ) ^ r := by rw [← pow_add]; congr 1; omega
  have hpow1 : (ell : ℝ) ^ b = (ell : ℝ) ^ (b - 1) * ell := by rw [← pow_succ]; congr 1; omega
  -- Bernoulli: ell^r ≥ 1 + r (ell − 1)
  have hbern : 1 + (r : ℝ) * ((ell : ℝ) - 1) ≤ (ell : ℝ) ^ r := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ (ell : ℝ) - 1 by linarith) r
    simpa using this
  have hcast : ((b - (s + 1) : ℕ) : ℝ) = ((m - (s + 1) : ℕ) : ℝ) + r := by
    rw [hr]; push_cast [show s + 1 ≤ b by omega, show s + 1 ≤ m by omega, show m ≤ b by omega]; ring
  rw [hcast]
  set P : ℝ := (pdist c z : ℝ)
  have hRM : (0 : ℝ) ≤ (R : ℝ) * M := by positivity
  -- P/ell^m − P/ell^b ≥ r R M / 2
  have key : (r : ℝ) * (R * M) / 2 ≤ P / (ell : ℝ) ^ m - P / (ell : ℝ) ^ b := by
    have hpb : (0 : ℝ) < (ell : ℝ) ^ b := by positivity
    have e1 : P / (ell : ℝ) ^ m - P / (ell : ℝ) ^ b = P * ((ell : ℝ) ^ r - 1) / (ell : ℝ) ^ b := by
      rw [hpow]; field_simp
    rw [e1, le_div_iff₀ hpb]
    have hr0 : (0 : ℝ) ≤ (ell : ℝ) ^ r - 1 := by nlinarith
    have h1 : (R : ℝ) * M * (ell : ℝ) ^ (b - 1) * ((ell : ℝ) ^ r - 1) ≤ P * ((ell : ℝ) ^ r - 1) :=
      mul_le_mul_of_nonneg_right hP hr0
    have h2 : (r : ℝ) * (R * M) / 2 * (ell : ℝ) ^ b ≤ (R : ℝ) * M * (ell : ℝ) ^ (b - 1) * ((ell : ℝ) ^ r - 1) := by
      rw [hpow1]
      have hpb1 : (0 : ℝ) ≤ (ell : ℝ) ^ (b - 1) := by positivity
      have h3 : (r : ℝ) * ell / 2 ≤ (ell : ℝ) ^ r - 1 := by
        have : (r : ℝ) * ell / 2 ≤ (r : ℝ) * ((ell : ℝ) - 1) := by
          have hr0' : (0 : ℝ) ≤ r := Nat.cast_nonneg _
          nlinarith
        linarith
      have := mul_le_mul_of_nonneg_left h3 (mul_nonneg hRM hpb1)
      nlinarith
    linarith
  linarith

/-- **`stratWeight` is `StratLip` with constant `1`** (so `θ · stratWeight` is `StratLip θ`). -/
theorem stratWeight_lip {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hell : 2 ≤ ell)
    (c : PeriodicLatticeSite L) : StratLip S k ell 1 (stratWeight S ell M R k c) := by
  intro x μ
  set s := strat S k c
  set b := bstrat S k (x, μ) with hbdef
  set y := periodicLatticeShift x μ with hy
  have hell1 : 1 ≤ ell := by omega
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have slope : ∀ m, b ≤ m → |wTerm R M ell s m c y - wTerm R M ell s m c x| ≤ 1 / (ell : ℝ) ^ b := by
    intro m hm
    refine (wTerm_lip R M ell s m hell1 c x μ).trans ?_
    have hp1 : (0 : ℝ) < (ell : ℝ) ^ b := by positivity
    exact one_div_le_one_div_of_le hp1 (pow_le_pow_right₀ hellr hm)
  by_cases hbs : b ≤ s + 1
  · unfold stratWeight
    exact inf'_lip _ _ _ _ _ (fun m hm => slope m (le_trans hbs (Finset.mem_Icc.mp hm).1))
  · push Not at hbs
    have hxb : b ≤ strat S k x := min_le_left _ _
    have hyb : b ≤ strat S k y := min_le_right _ _
    have hbk : b ≤ k := bstrat_le S k (x, μ)
    set J := Finset.Icc b (k + 1) with hJ
    have hJne : J.Nonempty := ⟨b, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
    have hJI : J ⊆ Finset.Icc (s + 1) (k + 1) := by
      intro m hm; rw [Finset.mem_Icc] at hm ⊢; omega
    have hdomz : ∀ z, b ≤ strat S k z → ∀ m ∈ Finset.Icc (s + 1) (k + 1), ∃ j ∈ J,
        wTerm R M ell s j c z ≤ wTerm R M ell s m c z := by
      intro z hz m hm
      rw [Finset.mem_Icc] at hm
      by_cases hmb : m < b
      · exact ⟨b, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, wTerm_dom hA hell (by omega) hz hm.1 hmb⟩
      · exact ⟨m, Finset.mem_Icc.mpr ⟨by omega, hm.2⟩, le_rfl⟩
    unfold stratWeight
    rw [inf'_eq_of_dom _ J _ hJne hJI _ (hdomz y hyb), inf'_eq_of_dom _ J _ hJne hJI _ (hdomz x hxb)]
    exact inf'_lip _ _ _ _ _ (fun m hm => slope m (Finset.mem_Icc.mp hm).1)

/-! ## the geometric sum -/

/-- `1/(1 − e^{-a}) ≤ 1 + 1/a`. -/
theorem inv_one_sub_exp_le {a : ℝ} (ha : 0 < a) : 1 / (1 - Real.exp (-a)) ≤ 1 + 1 / a := by
  have h1 : Real.exp (-a) * (1 + a) ≤ 1 := by
    have := Real.add_one_le_exp a
    have he : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (-a)
    nlinarith
  have hlt : Real.exp (-a) < 1 := by rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]; exact Real.exp_lt_exp.mpr (by linarith)
  have hd : 0 < 1 - Real.exp (-a) := by linarith
  rw [div_le_iff₀ hd]
  have : (1 + 1 / a) * (1 - Real.exp (-a)) = 1 + 1 / a - Real.exp (-a) * (1 + a) / a := by field_simp; ring
  rw [this]
  have : Real.exp (-a) * (1 + a) / a ≤ 1 / a := div_le_div_of_nonneg_right h1 ha.le
  linarith

/-- a geometric sum over the offsets `(t + K) mod N`. -/
theorem exp_off_sum (N K : ℕ) (a : ℝ) (ha : 0 < a) :
    ∑ t : Fin N, Real.exp (-(a * (((t.val + K) % N : ℕ) : ℝ))) ≤ 1 / (1 - Real.exp (-a)) := by
  have hlt : Real.exp (-a) < 1 := by rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]; exact Real.exp_lt_exp.mpr (by linarith)
  set F : ℕ → ℝ := fun j => Real.exp (-(a * (j : ℝ))) with hF
  set f : Fin N → ℕ := fun t => (t.val + K) % N with hf
  have hinj : Set.InjOn f (Finset.univ : Finset (Fin N)) := by
    intro t _ t' _ h
    have hmod : t.val ≡ t'.val [MOD N] := Nat.ModEq.add_right_cancel' K h
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hmod t.isLt t'.isLt)
  have h1 : ∑ t : Fin N, F (f t) = ∑ j ∈ (Finset.univ : Finset (Fin N)).image f, F j :=
    (Finset.sum_image hinj).symm
  have hsub : (Finset.univ : Finset (Fin N)).image f ⊆ Finset.range N := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨t, -, rfl⟩ := hj
    rw [Finset.mem_range]
    exact Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) t.isLt)
  have h2 : ∑ j ∈ (Finset.univ : Finset (Fin N)).image f, F j ≤ ∑ j ∈ Finset.range N, F j :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => (Real.exp_pos _).le)
  have e : ∀ j : ℕ, F j = Real.exp (-a) ^ j := by
    intro j; rw [hF, ← Real.exp_nat_mul]; ring_nf
  have h3 : ∑ j ∈ Finset.range N, F j ≤ 1 / (1 - Real.exp (-a)) := by
    simp only [e]
    rw [Finset.range_eq_Ico]
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) (Real.exp_pos (-a)).le hlt
    simpa using this
  calc _ = ∑ t : Fin N, F (f t) := rfl
    _ ≤ _ := h1 ▸ h2.trans h3

/-- 1D: `Σ_{t<N} e^{-a pcd(t,y)} ≤ 2/(1 − e^{-a})`. -/
theorem exp_pcd_sum (N : ℕ) (a : ℝ) (ha : 0 < a) (y : ℕ) (hy : y < N) :
    ∑ t : Fin N, Real.exp (-(a * (pcd N t.val y : ℝ))) ≤ 2 / (1 - Real.exp (-a)) := by
  have hsplit : ∀ t : Fin N, Real.exp (-(a * (pcd N t.val y : ℝ)))
      ≤ Real.exp (-(a * (((t.val + (N - y)) % N : ℕ) : ℝ))) + Real.exp (-(a * (((y + (N - t.val)) % N : ℕ) : ℝ))) := by
    intro t
    have ht := t.isLt
    have key : pcd N t.val y = (t.val + (N - y)) % N ∨ pcd N t.val y = (y + (N - t.val)) % N := by
      unfold pcd
      by_cases h : t.val ≤ y
      · rw [if_pos h]
        have e1 : t.val + (N - y) = N - (y - t.val) := by omega
        by_cases he : t.val = y
        · left; subst he; rw [Nat.sub_self, Nat.sub_zero, Nat.add_sub_cancel' ht.le, Nat.mod_self]; simp
        · have e2 : y + (N - t.val) = (y - t.val) + N := by omega
          rw [e1, Nat.mod_eq_of_lt (by omega), e2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rcases le_total (y - t.val) (N - (y - t.val)) with h2 | h2
          · right; exact min_eq_left h2
          · left; exact min_eq_right h2
      · rw [if_neg h]
        have e1 : t.val + (N - y) = (t.val - y) + N := by omega
        have e2 : y + (N - t.val) = N - (t.val - y) := by omega
        rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), e2, Nat.mod_eq_of_lt (by omega)]
        rcases le_total (t.val - y) (N - (t.val - y)) with h2 | h2
        · left; exact min_eq_left h2
        · right; exact min_eq_right h2
    have p1 := Real.exp_pos (-(a * (((t.val + (N - y)) % N : ℕ) : ℝ)))
    have p2 := Real.exp_pos (-(a * (((y + (N - t.val)) % N : ℕ) : ℝ)))
    rcases key with h | h <;> rw [h] <;> linarith
  have hb : ∑ t : Fin N, Real.exp (-(a * (((y + (N - t.val)) % N : ℕ) : ℝ))) ≤ 1 / (1 - Real.exp (-a)) := by
    -- the reflected offsets `(y + N − t) mod N` are injective in `t` as well
    have hlt : Real.exp (-a) < 1 := by rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]; exact Real.exp_lt_exp.mpr (by linarith)
    set F : ℕ → ℝ := fun j => Real.exp (-(a * (j : ℝ))) with hF
    set f : Fin N → ℕ := fun t => (y + (N - t.val)) % N with hf
    have hinj : Set.InjOn f (Finset.univ : Finset (Fin N)) := by
      intro t _ t' _ h
      have h' : (y + (N - t.val)) % N = (y + (N - t'.val)) % N := h
      have ht := t.isLt; have ht' := t'.isLt
      have hmod : (N - t.val) ≡ (N - t'.val) [MOD N] := Nat.ModEq.add_left_cancel' y h'
      have hq : (N - t.val) + t.val + t'.val ≡ (N - t'.val) + t'.val + t.val [MOD N] := by
        have := Nat.ModEq.add_right (t.val + t'.val) hmod
        rw [show N - t.val + t.val + t'.val = N - t.val + (t.val + t'.val) by ring,
          show N - t'.val + t'.val + t.val = N - t'.val + (t.val + t'.val) by ring]
        exact this
      rw [Nat.sub_add_cancel ht.le, Nat.sub_add_cancel ht'.le] at hq
      have hq' : t'.val ≡ t.val [MOD N] := Nat.ModEq.add_left_cancel' N hq
      exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hq'.symm ht ht')
    have h1 : ∑ t : Fin N, F (f t) = ∑ j ∈ (Finset.univ : Finset (Fin N)).image f, F j :=
      (Finset.sum_image hinj).symm
    have hsub : (Finset.univ : Finset (Fin N)).image f ⊆ Finset.range N := by
      intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨t, -, rfl⟩ := hj
      rw [Finset.mem_range]
      exact Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) t.isLt)
    have h2 : ∑ j ∈ (Finset.univ : Finset (Fin N)).image f, F j ≤ ∑ j ∈ Finset.range N, F j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => (Real.exp_pos _).le)
    have e : ∀ j : ℕ, F j = Real.exp (-a) ^ j := by
      intro j; rw [hF, ← Real.exp_nat_mul]; ring_nf
    have h3 : ∑ j ∈ Finset.range N, F j ≤ 1 / (1 - Real.exp (-a)) := by
      simp only [e]
      rw [Finset.range_eq_Ico]
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) (Real.exp_pos (-a)).le hlt
      simpa using this
    calc _ = ∑ t : Fin N, F (f t) := rfl
      _ ≤ _ := h1 ▸ h2.trans h3
  have ha' := exp_off_sum N (N - y) a ha
  calc _ ≤ ∑ t : Fin N, (Real.exp (-(a * (((t.val + (N - y)) % N : ℕ) : ℝ)))
          + Real.exp (-(a * (((y + (N - t.val)) % N : ℕ) : ℝ)))) := Finset.sum_le_sum (fun t _ => hsplit t)
    _ = _ + _ := Finset.sum_add_distrib
    _ ≤ 1 / (1 - Real.exp (-a)) + 1 / (1 - Real.exp (-a)) := add_le_add ha' hb
    _ = 2 / (1 - Real.exp (-a)) := by ring

/-- 3D: `Σ_x e^{-a |c − x|} ≤ (2/(1 − e^{-a}))³`. -/
theorem exp_pdist_sum (a : ℝ) (ha : 0 < a) (c : PeriodicLatticeSite L) :
    ∑ x : PeriodicLatticeSite L, Real.exp (-(a * (pdist c x : ℝ))) ≤ (2 / (1 - Real.exp (-a))) ^ 3 := by
  have hlt : Real.exp (-a) < 1 := by rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]; exact Real.exp_lt_exp.mpr (by linarith)
  have hfac : ∀ x : PeriodicLatticeSite L, Real.exp (-(a * (pdist c x : ℝ)))
      = ∏ μ : Fin 3, Real.exp (-(a * (pcd (L μ + 1) (x μ).val (c μ).val : ℝ))) := by
    intro x
    rw [← Real.exp_sum]
    congr 1
    unfold pdist
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun μ _ => by rw [pcd_comm])
  simp only [hfac]
  rw [← Fintype.prod_sum (fun μ (t : Fin (L μ + 1)) =>
      Real.exp (-(a * (pcd (L μ + 1) t.val (c μ).val : ℝ))))]
  calc ∏ μ : Fin 3, ∑ t : Fin (L μ + 1), Real.exp (-(a * (pcd (L μ + 1) t.val (c μ).val : ℝ)))
      ≤ ∏ _μ : Fin 3, 2 / (1 - Real.exp (-a)) :=
        Finset.prod_le_prod (fun μ _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
          (fun μ _ => exp_pcd_sum (L μ + 1) a ha (c μ).val (c μ).isLt)
    _ = (2 / (1 - Real.exp (-a))) ^ 3 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **G2 geometric sum (`strat_geom_sum`)**, explicit form. -/
theorem strat_geom_sum {ell M R k : ℕ} {S : Tower L} (hell : 1 ≤ ell) {θ : ℝ} (hθ : 0 < θ)
    (c : PeriodicLatticeSite L) :
    ∑ x : PeriodicLatticeSite L, Real.exp (-(2 * θ * stratWeight S ell M R k c x))
      ≤ ∑ m ∈ Finset.Icc (strat S k c + 1) (k + 1),
          Real.exp (-(θ * (((m - (strat S k c + 1) : ℕ) : ℝ) * (R * M)))) * (2 + (ell : ℝ) ^ m / θ) ^ 3 := by
  set s := strat S k c
  set I := Finset.Icc (s + 1) (k + 1)
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  -- pointwise: e^{-2θ V} ≤ Σ_m e^{-2θ T_m}
  have hpt : ∀ x, Real.exp (-(2 * θ * stratWeight S ell M R k c x))
      ≤ ∑ m ∈ I, Real.exp (-(2 * θ * wTerm R M ell s m c x)) := by
    intro x
    obtain ⟨m, hm, hmeq⟩ := Finset.exists_mem_eq_inf' (Icc_nonempty s k (strat_le S k c))
      (fun m => wTerm R M ell s m c x)
    have : stratWeight S ell M R k c x = wTerm R M ell s m c x := hmeq
    rw [this]
    exact Finset.single_le_sum (f := fun m => Real.exp (-(2 * θ * wTerm R M ell s m c x)))
      (fun _ _ => (Real.exp_pos _).le) hm
  calc ∑ x, Real.exp (-(2 * θ * stratWeight S ell M R k c x))
      ≤ ∑ x, ∑ m ∈ I, Real.exp (-(2 * θ * wTerm R M ell s m c x)) := Finset.sum_le_sum (fun x _ => hpt x)
    _ = ∑ m ∈ I, ∑ x, Real.exp (-(2 * θ * wTerm R M ell s m c x)) := Finset.sum_comm
    _ ≤ _ := by
      refine Finset.sum_le_sum (fun m hm => ?_)
      have hpm : (0 : ℝ) < (ell : ℝ) ^ m := by positivity
      set a : ℝ := 2 * θ / (ell : ℝ) ^ m with hadef
      have ha : 0 < a := by positivity
      have hterm : ∀ x, Real.exp (-(2 * θ * wTerm R M ell s m c x))
          = Real.exp (-(θ * (((m - (s + 1) : ℕ) : ℝ) * (R * M)))) * Real.exp (-(a * (pdist c x : ℝ))) := by
        intro x
        rw [← Real.exp_add]; congr 1
        unfold wTerm; rw [hadef]; field_simp; ring
      simp only [hterm]
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      refine (exp_pdist_sum a ha c).trans ?_
      have h1 := inv_one_sub_exp_le ha
      have hlt : Real.exp (-a) < 1 := by rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]; exact Real.exp_lt_exp.mpr (by linarith)
      have hd : 0 < 1 - Real.exp (-a) := by linarith
      have h2 : 2 / (1 - Real.exp (-a)) ≤ 2 + (ell : ℝ) ^ m / θ := by
        have e : 2 / (1 - Real.exp (-a)) = 2 * (1 / (1 - Real.exp (-a))) := by ring
        have e2 : 2 * (1 + 1 / a) = 2 + (ell : ℝ) ^ m / θ := by rw [hadef]; field_simp
        rw [e, ← e2]; linarith
      exact pow_le_pow_left₀ (by positivity) h2 3

/-- **G2, k-flat form (`strat_geom_sum_flat`)**: if `ell³ e^{-θ R M} ≤ 1/2`, then
`Σ_x e^{-2θ V_c(x)} ≤ 64 + 8 ell³ (ell^{strat c}/θ)³` -- independent of `k`, of the torus and of the tower. -/
theorem strat_geom_sum_flat {ell M R k : ℕ} {S : Tower L} (hell : 1 ≤ ell) {θ : ℝ} (hθ : 0 < θ)
    (hq : (ell : ℝ) ^ 3 * Real.exp (-(θ * (R * M))) ≤ 1 / 2) (c : PeriodicLatticeSite L) :
    ∑ x : PeriodicLatticeSite L, Real.exp (-(2 * θ * stratWeight S ell M R k c x))
      ≤ 64 + 8 * (ell : ℝ) ^ 3 * ((ell : ℝ) ^ strat S k c / θ) ^ 3 := by
  set s := strat S k c
  refine (strat_geom_sum (S := S) (M := M) (R := R) hell hθ c).trans ?_
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  set q : ℝ := Real.exp (-(θ * (R * M))) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 / 2 := by
    have : q ≤ (ell : ℝ) ^ 3 * q := le_mul_of_one_le_left hq0.le (one_le_pow₀ hellr)
    linarith
  set X : ℝ := (ell : ℝ) ^ s / θ with hX
  have hX0 : 0 ≤ X := by positivity
  -- reindex m = s + 1 + r
  have hre : ∑ m ∈ Finset.Icc (s + 1) (k + 1),
        Real.exp (-(θ * (((m - (s + 1) : ℕ) : ℝ) * (R * M)))) * (2 + (ell : ℝ) ^ m / θ) ^ 3
      = ∑ r ∈ Finset.range (k + 1 - s),
        Real.exp (-(θ * ((r : ℝ) * (R * M)))) * (2 + (ell : ℝ) ^ (s + 1 + r) / θ) ^ 3 := by
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by rw [Order.succ_eq_add_one]; congr 1; omega) (fun r _ => ?_)
    rw [Nat.add_sub_cancel_left]
  rw [hre]
  have hterm : ∀ r : ℕ, Real.exp (-(θ * ((r : ℝ) * (R * M)))) * (2 + (ell : ℝ) ^ (s + 1 + r) / θ) ^ 3
      ≤ 32 * q ^ r + 4 * (ell : ℝ) ^ 3 * X ^ 3 * ((ell : ℝ) ^ 3 * q) ^ r := by
    intro r
    have he : Real.exp (-(θ * ((r : ℝ) * (R * M)))) = q ^ r := by
      rw [hqdef, ← Real.exp_nat_mul]; ring_nf
    rw [he]
    have hY : (ell : ℝ) ^ (s + 1 + r) / θ = (ell : ℝ) * (ell : ℝ) ^ r * X := by
      rw [hX, pow_add, pow_add]; ring
    rw [hY]
    set Y := (ell : ℝ) * (ell : ℝ) ^ r * X
    have hY0 : 0 ≤ Y := by positivity
    have hcube : (2 + Y) ^ 3 ≤ 4 * (8 + Y ^ 3) := by nlinarith [sq_nonneg (Y - 2), sq_nonneg Y]
    have hqr : 0 ≤ q ^ r := by positivity
    have e3 : Y ^ 3 = (ell : ℝ) ^ 3 * X ^ 3 * ((ell : ℝ) ^ 3) ^ r := by
      simp only [Y]; rw [← pow_mul, mul_comm 3 r, pow_mul]; ring
    calc q ^ r * (2 + Y) ^ 3 ≤ q ^ r * (4 * (8 + Y ^ 3)) := mul_le_mul_of_nonneg_left hcube hqr
      _ = 32 * q ^ r + 4 * (ell : ℝ) ^ 3 * X ^ 3 * ((ell : ℝ) ^ 3 * q) ^ r := by rw [e3, mul_pow]; ring
  have hgeo : ∀ z : ℝ, 0 ≤ z → z ≤ 1 / 2 → ∀ n : ℕ, ∑ r ∈ Finset.range n, z ^ r ≤ 2 := by
    intro z hz0 hz n
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hz0 (by linarith)
    rw [← Finset.range_eq_Ico] at h
    simp at h
    have : 1 / (1 - z) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    rw [one_div] at this
    linarith
  calc ∑ r ∈ Finset.range (k + 1 - s), Real.exp (-(θ * ((r : ℝ) * (R * M)))) * (2 + (ell : ℝ) ^ (s + 1 + r) / θ) ^ 3
      ≤ ∑ r ∈ Finset.range (k + 1 - s), (32 * q ^ r + 4 * (ell : ℝ) ^ 3 * X ^ 3 * ((ell : ℝ) ^ 3 * q) ^ r) :=
        Finset.sum_le_sum (fun r _ => hterm r)
    _ = 32 * ∑ r ∈ Finset.range (k + 1 - s), q ^ r
        + 4 * (ell : ℝ) ^ 3 * X ^ 3 * ∑ r ∈ Finset.range (k + 1 - s), ((ell : ℝ) ^ 3 * q) ^ r := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 32 * 2 + 4 * (ell : ℝ) ^ 3 * X ^ 3 * 2 := by
        have h1 := hgeo q hq0.le hq1 (k + 1 - s)
        have h2 := hgeo ((ell : ℝ) ^ 3 * q) (by positivity) hq (k + 1 - s)
        have h3 : 0 ≤ 4 * (ell : ℝ) ^ 3 * X ^ 3 := by positivity
        nlinarith
    _ = 64 + 8 * (ell : ℝ) ^ 3 * X ^ 3 := by ring

#print axioms stratLip_site
#print axioms stratWeight_self
#print axioms stratWeight_nonneg
#print axioms inf'_lip
#print axioms inf'_eq_of_dom
#print axioms wTerm_lip
#print axioms wTerm_dom
#print axioms stratWeight_lip
#print axioms inv_one_sub_exp_le
#print axioms exp_off_sum
#print axioms exp_pcd_sum
#print axioms exp_pdist_sum
#print axioms strat_geom_sum
#print axioms strat_geom_sum_flat

end AdalyFormal.M1
