import M1G2

/-!
# DW1 -- the Combes–Thomas weight of the D2 column bound, with decay across SHALLOW strata (M1 D-layer lane, 2026-10-14)

Lane B's G2 weight `V_c = stratWeight` (M1G2) grows by `R M / 2` per crossed collar only towards COARSER strata.  Towards
finer strata (`strat x < strat c`) it grows at the slow rate `ℓ^{-(s+1)}` and the D2 column sum
`Σ_x ℓ^{-4 strat x} e^{-2θV_c(x)}` is not uniform in `s = strat c` (FINDING of this lane, NOTES.md).  The repair:
`uT i x = min(1, dist(x, Ω_i)/(R M ℓ^{i-1}))` (as an `inf'` over sites), and
  `phiC θ c x = θ V_c(x) + θ R M Σ_{1 ≤ i ≤ s} uT i x`.
* `uT_zero_of_mem` (`x ∈ Ω_i ⇒ uT = 0`), `uT_one_of_not_mem` (`x ∉ Ω_{i-1} ⇒ uT = 1`, the collar), `uT_lip`, `uT_step`
  (`uT` changes across a bond only if an endpoint has stratum `i − 1`);
* `phiC_self` : `phiC θ c c = 0`;  `phiC_step` : `|φ(x+e_μ) − φ(x)| ≤ 3θℓ/ℓ^{strat x}`;
* `phiC_block` : two sites of stratum `j` at `pdist ≤ 3ℓ^j` have `|φ(x) − φ(y)| ≤ 6θ` (constraint blocks);
* `sum_uT_ge` : `s − 1 − strat x ≤ Σ_i uT i x`;
* **`phiC_colsum`** : if `ℓ³ e^{-θRM} ≤ 1/2`:  `Σ_x (ℓ^{strat x})^{-4} e^{-2 phiC θ c x} ≤ ℓ⁴(64 + 8ℓ³/θ³) · (ℓ^{strat c})^{-1}`,
  free of `k`, the torus and the tower.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1DStrat

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_shift_le pdist_triangle pdist_self)
open AdalyFormal.M1

variable {L : PeriodicLatticeExtent}

/-! ## 1. the collar profile `uT` -/

open Classical in
/-- one term of `uT` -/
noncomputable def uTerm (S : Tower L) (ell M R i : ℕ) (x y : PeriodicLatticeSite L) : ℝ :=
  if y ∈ S.Om i then min 1 ((pdist x y : ℝ) / ((R : ℝ) * M * (ell : ℝ) ^ (i - 1))) else 1

/-- `uT i x = min(1, dist(x, Ω_i)/(R M ℓ^{i-1}))` -/
noncomputable def uT (S : Tower L) (ell M R i : ℕ) (x : PeriodicLatticeSite L) : ℝ :=
  Finset.univ.inf' ⟨x, Finset.mem_univ x⟩ (fun y => uTerm S ell M R i x y)

theorem uTerm_nonneg (S : Tower L) (ell M R i : ℕ) (x y : PeriodicLatticeSite L) : 0 ≤ uTerm S ell M R i x y := by
  unfold uTerm
  split_ifs
  · exact le_min zero_le_one (by positivity)
  · exact zero_le_one

theorem uT_nonneg (S : Tower L) (ell M R i : ℕ) (x : PeriodicLatticeSite L) : 0 ≤ uT S ell M R i x :=
  Finset.le_inf' _ _ (fun y _ => uTerm_nonneg S ell M R i x y)

theorem uT_le_one (S : Tower L) (ell M R i : ℕ) (x : PeriodicLatticeSite L) : uT S ell M R i x ≤ 1 := by
  refine (Finset.inf'_le _ (Finset.mem_univ x)).trans ?_
  unfold uTerm; split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem uT_zero_of_mem (S : Tower L) (ell M R i : ℕ) {x : PeriodicLatticeSite L} (hx : x ∈ S.Om i) :
    uT S ell M R i x = 0 := by
  refine le_antisymm ((Finset.inf'_le _ (Finset.mem_univ x)).trans (le_of_eq ?_)) (uT_nonneg S ell M R i x)
  unfold uTerm
  rw [if_pos hx, pdist_self]
  simp

theorem uT_one_of_not_mem {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hell : 1 ≤ ell) {i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) {x : PeriodicLatticeSite L} (hx : x ∉ S.Om (i - 1)) :
    uT S ell M R i x = 1 := by
  refine le_antisymm (uT_le_one S ell M R i x) (Finset.le_inf' _ _ (fun y _ => ?_))
  unfold uTerm
  split_ifs with hy
  · have hy' : y ∈ S.Om (i - 1 + 1) := by rw [Nat.sub_add_cancel hi]; exact hy
    have hcol := collar hA (j := i - 1) (by omega) hx hy'
    unfold bigSide at hcol
    have hpos : (0 : ℝ) < (R : ℝ) * M * (ell : ℝ) ^ (i - 1) := by
      have : (1 : ℝ) ≤ R := by exact_mod_cast hR
      have : (1 : ℝ) ≤ M := by exact_mod_cast hM
      have : (1 : ℝ) ≤ (ell : ℝ) ^ (i - 1) := one_le_pow₀ (by exact_mod_cast hell)
      positivity
    have hlt : (R : ℝ) * M * (ell : ℝ) ^ (i - 1) < (pdist x y : ℝ) := by
      have : R * M * ell ^ (i - 1) < pdist x y := by rw [Nat.mul_assoc]; exact hcol
      exact_mod_cast this
    refine le_min le_rfl ?_
    rw [le_div_iff₀ hpos]; linarith
  · exact le_rfl

theorem uT_lip (S : Tower L) (ell M R i : ℕ) (x x' : PeriodicLatticeSite L) :
    |uT S ell M R i x - uT S ell M R i x'| ≤ (pdist x x' : ℝ) / ((R : ℝ) * M * (ell : ℝ) ^ (i - 1)) := by
  have hD : (0 : ℝ) ≤ (R : ℝ) * M * (ell : ℝ) ^ (i - 1) := by positivity
  unfold uT
  have e : (Finset.univ.inf' ⟨x', Finset.mem_univ x'⟩ (fun y => uTerm S ell M R i x' y))
      = (Finset.univ.inf' ⟨x, Finset.mem_univ x⟩ (fun y => uTerm S ell M R i x' y)) := rfl
  rw [e]
  refine inf'_lip _ _ _ _ _ (fun y _ => ?_)
  unfold uTerm
  split_ifs
  · refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero]
    refine max_le (div_nonneg (Nat.cast_nonneg _) hD) ?_
    rw [← sub_div, abs_div, abs_of_nonneg hD]
    apply div_le_div_of_nonneg_right _ hD
    have t1 := pdist_triangle x x' y
    have t2 := pdist_triangle x' x y
    have t3 := pdist_comm x x'
    rw [abs_le]; constructor
    · have h2 : (pdist x' y : ℝ) ≤ pdist x' x + pdist x y := by exact_mod_cast t2
      have h3 : (pdist x x' : ℝ) = pdist x' x := by exact_mod_cast t3
      linarith
    · have : (pdist x y : ℝ) ≤ pdist x x' + pdist x' y := by exact_mod_cast t1
      linarith
  · simp only [sub_self, abs_zero]
    exact div_nonneg (Nat.cast_nonneg _) hD

/-- `uT i` changes across a bond only if an endpoint has stratum `i − 1`. -/
theorem uT_step {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hell : 1 ≤ ell) {i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (x : PeriodicLatticeSite L) (μ : Fin 3)
    (h1 : strat S k x ≠ i - 1) (h2 : strat S k (periodicLatticeShift x μ) ≠ i - 1) :
    uT S ell M R i (periodicLatticeShift x μ) = uT S ell M R i x := by
  have hadj := strat_adj hA hR hM hell x μ
  set y := periodicLatticeShift x μ
  by_cases hxi : i ≤ strat S k x
  · have hy : i ≤ strat S k y := by omega
    rw [uT_zero_of_mem S ell M R i ((le_strat_iff hA hi hik x).mp hxi),
      uT_zero_of_mem S ell M R i ((le_strat_iff hA hi hik y).mp hy)]
  · have hx' : x ∉ S.Om (i - 1) := by
      intro h; have := le_strat_of_mem (k := k) (by omega) h; omega
    have hy' : y ∉ S.Om (i - 1) := by
      intro h; have := le_strat_of_mem (k := k) (by omega) h; omega
    rw [uT_one_of_not_mem hA hR hM hell hi hik hx', uT_one_of_not_mem hA hR hM hell hi hik hy']

/-! ## 2. the weight -/

/-- **the D2 Combes–Thomas weight** centred at `c` -/
noncomputable def phiC (S : Tower L) (ell M R k : ℕ) (θ : ℝ) (c x : PeriodicLatticeSite L) : ℝ :=
  θ * stratWeight S ell M R k c x
    + θ * ((R : ℝ) * M) * ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i x

theorem sum_uT_nonneg (S : Tower L) (ell M R k : ℕ) (c x : PeriodicLatticeSite L) :
    0 ≤ ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i x :=
  Finset.sum_nonneg (fun i _ => uT_nonneg S ell M R i x)

theorem phiC_nonneg (S : Tower L) (ell M R k : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (c x : PeriodicLatticeSite L) :
    0 ≤ phiC S ell M R k θ c x := by
  unfold phiC
  have := stratWeight_nonneg S ell M R k c x
  have := sum_uT_nonneg S ell M R k c x
  positivity

theorem phiC_self {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (θ : ℝ) (c : PeriodicLatticeSite L) :
    phiC S ell M R k θ c c = 0 := by
  unfold phiC
  rw [stratWeight_self]
  have : ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i c = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    exact uT_zero_of_mem S ell M R i ((le_strat_iff hA hi.1 (hi.2.trans (strat_le S k c)) c).mp hi.2)
  rw [this]; ring

/-- the sum of the `uT` increments across a bond -/
theorem sum_uT_step {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hell : 1 ≤ ell) (c x : PeriodicLatticeSite L) (μ : Fin 3) :
    |∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i (periodicLatticeShift x μ)
        - ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i x|
      ≤ 2 * (ell : ℝ) / ((R : ℝ) * M * (ell : ℝ) ^ strat S k x) := by
  have hadj := strat_adj hA hR hM hell x μ
  set y := periodicLatticeShift x μ
  set a := strat S k x + 1 with hadef
  set b := strat S k y + 1 with hbdef
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  set D0 : ℝ := (R : ℝ) * M * (ell : ℝ) ^ strat S k x with hD0
  have hD0p : 0 < D0 := by have := one_le_pow₀ (n := strat S k x) hellr; positivity
  -- bound per index
  have hterm : ∀ i ∈ Finset.Icc 1 (strat S k c),
      |uT S ell M R i y - uT S ell M R i x|
        ≤ (if i = a then 1 / D0 else 0) + (if i = b then (ell : ℝ) / D0 else 0) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hik : i ≤ k := hi.2.trans (strat_le S k c)
    have hlip := uT_lip S ell M R i y x
    have hpd : (pdist y x : ℝ) ≤ 1 := by
      have := pdist_shift_le x μ; rw [pdist_comm] at this; exact_mod_cast this
    by_cases ha : i = a
    · rw [if_pos ha]
      have hb0 : 0 ≤ (if i = b then (ell : ℝ) / D0 else 0) := by split_ifs <;> positivity
      have : (pdist y x : ℝ) / ((R : ℝ) * M * (ell : ℝ) ^ (i - 1)) ≤ 1 / D0 := by
        have e : i - 1 = strat S k x := by omega
        rw [e]; exact div_le_div_of_nonneg_right hpd hD0p.le
      linarith
    · by_cases hb : i = b
      · rw [if_neg ha, if_pos hb, zero_add]
        refine hlip.trans ?_
        have e : i - 1 = strat S k y := by omega
        rw [e]
        have hpy : (0 : ℝ) < (R : ℝ) * M * (ell : ℝ) ^ strat S k y := by
          have := one_le_pow₀ (n := strat S k y) hellr; positivity
        rw [div_le_div_iff₀ hpy hD0p]
        have hpow : (ell : ℝ) ^ strat S k x ≤ (ell : ℝ) ^ strat S k y * ell := by
          rw [← pow_succ]; exact pow_le_pow_right₀ hellr (by omega)
        have hRM : (0 : ℝ) ≤ (R : ℝ) * M := by positivity
        have : (pdist y x : ℝ) * ((R : ℝ) * M * (ell : ℝ) ^ strat S k x)
            ≤ 1 * ((R : ℝ) * M * ((ell : ℝ) ^ strat S k y * ell)) := by
          have h0 : (0 : ℝ) ≤ (R : ℝ) * M * (ell : ℝ) ^ strat S k x := hD0p.le
          calc (pdist y x : ℝ) * ((R : ℝ) * M * (ell : ℝ) ^ strat S k x)
              ≤ 1 * ((R : ℝ) * M * (ell : ℝ) ^ strat S k x) := mul_le_mul_of_nonneg_right hpd h0
            _ ≤ 1 * ((R : ℝ) * M * ((ell : ℝ) ^ strat S k y * ell)) := by
                rw [one_mul, one_mul]; exact mul_le_mul_of_nonneg_left hpow hRM
        linarith
      · rw [if_neg ha, if_neg hb, add_zero]
        have hx1 : strat S k x ≠ i - 1 := by
          intro h; apply ha; rw [hadef]; have := hi.1; omega
        have hy1 : strat S k y ≠ i - 1 := by
          intro h; apply hb; rw [hbdef]; have := hi.1; omega
        rw [uT_step hA hR hM hell hi.1 hik x μ hx1 hy1, sub_self, abs_zero]
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib]
  have s1 : ∑ i ∈ Finset.Icc 1 (strat S k c), (if i = a then 1 / D0 else 0) ≤ 1 / D0 := by
    rw [Finset.sum_ite_eq']; split_ifs
    · exact le_rfl
    · positivity
  have s2 : ∑ i ∈ Finset.Icc 1 (strat S k c), (if i = b then (ell : ℝ) / D0 else 0) ≤ (ell : ℝ) / D0 := by
    rw [Finset.sum_ite_eq']; split_ifs
    · exact le_rfl
    · positivity
  have : 1 / D0 ≤ (ell : ℝ) / D0 := div_le_div_of_nonneg_right hellr hD0p.le
  have e : 2 * (ell : ℝ) / D0 = (ell : ℝ) / D0 + (ell : ℝ) / D0 := by ring
  rw [e]; linarith

/-- **bond increment of the weight**: `|φ(x+e_μ) − φ(x)| ≤ 3θℓ/ℓ^{strat x}` -/
theorem phiC_step {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hell : 2 ≤ ell) {θ : ℝ} (hθ : 0 ≤ θ) (c x : PeriodicLatticeSite L) (μ : Fin 3) :
    |phiC S ell M R k θ c (periodicLatticeShift x μ) - phiC S ell M R k θ c x|
      ≤ 3 * θ * ell / (ell : ℝ) ^ strat S k x := by
  have hV := stratLip_site hA hR hM (by omega) zero_le_one (stratWeight_lip hA hell c) x μ
  have hU := sum_uT_step hA hR hM (by omega) c x μ
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hp : (0 : ℝ) < (ell : ℝ) ^ strat S k x := by positivity
  unfold phiC
  set dV := stratWeight S ell M R k c (periodicLatticeShift x μ) - stratWeight S ell M R k c x
  set dU := ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i (periodicLatticeShift x μ)
        - ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i x
  have e : θ * stratWeight S ell M R k c (periodicLatticeShift x μ)
        + θ * ((R : ℝ) * M) * ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i (periodicLatticeShift x μ)
      - (θ * stratWeight S ell M R k c x + θ * ((R : ℝ) * M) * ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i x)
      = θ * dV + θ * ((R : ℝ) * M) * dU := by ring
  rw [e]
  have hRM : (0 : ℝ) < (R : ℝ) * M := by positivity
  have h1 : |θ * dV| ≤ θ * (1 * ell / (ell : ℝ) ^ strat S k x) := by
    rw [abs_mul, abs_of_nonneg hθ]; exact mul_le_mul_of_nonneg_left hV hθ
  have h2 : |θ * ((R : ℝ) * M) * dU| ≤ θ * (2 * ell / (ell : ℝ) ^ strat S k x) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have : θ * ((R : ℝ) * M) * (2 * (ell : ℝ) / ((R : ℝ) * M * (ell : ℝ) ^ strat S k x))
        = θ * (2 * ell / (ell : ℝ) ^ strat S k x) := by field_simp
    rw [← this]; exact mul_le_mul_of_nonneg_left hU (by positivity)
  have e2 : 3 * θ * ell / (ell : ℝ) ^ strat S k x
      = θ * (1 * ell / (ell : ℝ) ^ strat S k x) + θ * (2 * ell / (ell : ℝ) ^ strat S k x) := by ring
  rw [e2]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-! ## 3. constraint blocks -/

theorem wTerm_lip_pd (R M ell s m : ℕ) (hell : 1 ≤ ell) (c x y : PeriodicLatticeSite L) :
    |wTerm R M ell s m c x - wTerm R M ell s m c y| ≤ (pdist x y : ℝ) / (ell : ℝ) ^ m := by
  unfold wTerm
  have hp : (0 : ℝ) < (ell : ℝ) ^ m := by have := one_le_pow₀ (n := m) (show (1 : ℝ) ≤ ell by exact_mod_cast hell); positivity
  have e : (pdist c x : ℝ) / (ell : ℝ) ^ m + ((m - (s + 1) : ℕ) : ℝ) * (R * M) / 2
      - ((pdist c y : ℝ) / (ell : ℝ) ^ m + ((m - (s + 1) : ℕ) : ℝ) * (R * M) / 2)
      = ((pdist c x : ℝ) - pdist c y) / (ell : ℝ) ^ m := by ring
  rw [e, abs_div, abs_of_pos hp]
  apply div_le_div_of_nonneg_right _ hp.le
  have t1 := pdist_triangle c y x
  have t2 := pdist_triangle c x y
  have t3 := pdist_comm x y
  have r1 : (pdist c x : ℝ) ≤ pdist c y + pdist x y := by
    have : pdist c x ≤ pdist c y + pdist y x := t1
    rw [← t3] at this; exact_mod_cast this
  have r2 : (pdist c y : ℝ) ≤ pdist c x + pdist x y := by exact_mod_cast t2
  rw [abs_le]; constructor <;> linarith

/-- the `V_c` part is `≤ 3` across two sites of one stratum `j` at distance `≤ 3ℓ^j`. -/
theorem stratWeight_block {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hell : 2 ≤ ell)
    (c : PeriodicLatticeSite L) {j : ℕ} {x y : PeriodicLatticeSite L} (hx : strat S k x = j) (hy : strat S k y = j)
    (hxy : (pdist x y : ℝ) ≤ 3 * (ell : ℝ) ^ j) :
    |stratWeight S ell M R k c x - stratWeight S ell M R k c y| ≤ 3 := by
  set s := strat S k c
  have hell1 : 1 ≤ ell := by omega
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have slope : ∀ m, j ≤ m → |wTerm R M ell s m c x - wTerm R M ell s m c y| ≤ 3 := by
    intro m hm
    refine (wTerm_lip_pd R M ell s m hell1 c x y).trans ?_
    have hp : (0 : ℝ) < (ell : ℝ) ^ m := by have := one_le_pow₀ (n := m) hellr; positivity
    rw [div_le_iff₀ hp]
    have : (ell : ℝ) ^ j ≤ (ell : ℝ) ^ m := pow_le_pow_right₀ hellr hm
    linarith
  by_cases hjs : j ≤ s + 1
  · unfold stratWeight
    exact inf'_lip _ _ _ _ _ (fun m hm => slope m (le_trans hjs (Finset.mem_Icc.mp hm).1))
  · push Not at hjs
    have hjk : j ≤ k := hx ▸ strat_le S k x
    set J := Finset.Icc j (k + 1) with hJ
    have hJne : J.Nonempty := ⟨j, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
    have hJI : J ⊆ Finset.Icc (s + 1) (k + 1) := by
      intro m hm; rw [Finset.mem_Icc] at hm ⊢; omega
    have hdomz : ∀ z, j ≤ strat S k z → ∀ m ∈ Finset.Icc (s + 1) (k + 1), ∃ i ∈ J,
        wTerm R M ell s i c z ≤ wTerm R M ell s m c z := by
      intro z hz m hm
      rw [Finset.mem_Icc] at hm
      by_cases hmb : m < j
      · exact ⟨j, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, wTerm_dom hA hell (by omega) hz hm.1 hmb⟩
      · exact ⟨m, Finset.mem_Icc.mpr ⟨by omega, hm.2⟩, le_rfl⟩
    unfold stratWeight
    rw [inf'_eq_of_dom _ J _ hJne hJI _ (hdomz x (by omega)), inf'_eq_of_dom _ J _ hJne hJI _ (hdomz y (by omega))]
    exact inf'_lip _ _ _ _ _ (fun m hm => slope m (Finset.mem_Icc.mp hm).1)

/-- **block oscillation of the weight**: `≤ 6θ` across two sites of one stratum `j` (both in `Ω₀`) at distance `≤ 3ℓ^j`. -/
theorem phiC_block {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hell : 2 ≤ ell) {θ : ℝ} (hθ : 0 ≤ θ) (c : PeriodicLatticeSite L) {j : ℕ} {x y : PeriodicLatticeSite L}
    (hx0 : x ∈ S.Om 0) (hy0 : y ∈ S.Om 0)
    (hx : strat S k x = j) (hy : strat S k y = j) (hxy : (pdist x y : ℝ) ≤ 3 * (ell : ℝ) ^ j) :
    |phiC S ell M R k θ c x - phiC S ell M R k θ c y| ≤ 6 * θ := by
  have hV := stratWeight_block hA hell c hx hy hxy
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hRM : (0 : ℝ) < (R : ℝ) * M := by positivity
  -- the `u` part: only `i = j + 1` contributes, by `3 / (R M)`
  have hU : |∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i x - ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i y|
      ≤ 3 / ((R : ℝ) * M) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ i ∈ Finset.Icc 1 (strat S k c), |uT S ell M R i x - uT S ell M R i y|
        ≤ if i = j + 1 then 3 / ((R : ℝ) * M) else 0 := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      have hik : i ≤ k := hi.2.trans (strat_le S k c)
      by_cases hij : i = j + 1
      · rw [if_pos hij]
        refine (uT_lip S ell M R i x y).trans ?_
        have e : i - 1 = j := by omega
        rw [e]
        have hp : (0 : ℝ) < (R : ℝ) * M * (ell : ℝ) ^ j := by have := one_le_pow₀ (n := j) hellr; positivity
        rw [div_le_div_iff₀ hp hRM]
        have : (pdist x y : ℝ) * ((R : ℝ) * M) ≤ 3 * (ell : ℝ) ^ j * ((R : ℝ) * M) :=
          mul_le_mul_of_nonneg_right hxy hRM.le
        linarith
      · rw [if_neg hij]
        by_cases hle : i ≤ j
        · rw [uT_zero_of_mem S ell M R i (mem_of_le_strat hA hx0 (by omega)),
            uT_zero_of_mem S ell M R i (mem_of_le_strat hA hy0 (by omega)), sub_self, abs_zero]
        · have hx' : x ∉ S.Om (i - 1) := by
            intro h; have := le_strat_of_mem (k := k) (by omega) h; omega
          have hy' : y ∉ S.Om (i - 1) := by
            intro h; have := le_strat_of_mem (k := k) (by omega) h; omega
          rw [uT_one_of_not_mem hA hR hM (by omega) hi.1 hik hx', uT_one_of_not_mem hA hR hM (by omega) hi.1 hik hy',
            sub_self, abs_zero]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_ite_eq']; split_ifs
    · exact le_rfl
    · positivity
  unfold phiC
  have e : θ * stratWeight S ell M R k c x + θ * ((R : ℝ) * M) * ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i x
      - (θ * stratWeight S ell M R k c y + θ * ((R : ℝ) * M) * ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i y)
      = θ * (stratWeight S ell M R k c x - stratWeight S ell M R k c y)
        + θ * ((R : ℝ) * M) * (∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i x
          - ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i y) := by ring
  rw [e]
  have h1 : |θ * (stratWeight S ell M R k c x - stratWeight S ell M R k c y)| ≤ θ * 3 := by
    rw [abs_mul, abs_of_nonneg hθ]; exact mul_le_mul_of_nonneg_left hV hθ
  have h2 : |θ * ((R : ℝ) * M) * (∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i x
      - ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i y)| ≤ θ * 3 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have : θ * ((R : ℝ) * M) * (3 / ((R : ℝ) * M)) = θ * 3 := by field_simp
    rw [← this]; exact mul_le_mul_of_nonneg_left hU (by positivity)
  have := (abs_add_le _ _).trans (add_le_add h1 h2)
  linarith

/-! ## 4. decay across shallow strata and the column sum -/

theorem sum_uT_ge {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hell : 1 ≤ ell) (c x : PeriodicLatticeSite L) :
    ((strat S k c - 1 - strat S k x : ℕ) : ℝ) ≤ ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i x := by
  set s := strat S k c
  set t := strat S k x
  have hsub : Finset.Icc (t + 2) s ⊆ Finset.Icc 1 s := by
    intro i hi; rw [Finset.mem_Icc] at hi ⊢; omega
  have h1 : ∑ i ∈ Finset.Icc (t + 2) s, uT S ell M R i x = ((Finset.Icc (t + 2) s).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    have hik : i ≤ k := hi.2.trans (strat_le S k c)
    have hx' : x ∉ S.Om (i - 1) := by
      intro h; have := le_strat_of_mem (k := k) (by omega) h; omega
    rw [uT_one_of_not_mem hA hR hM hell (by omega) hik hx']; simp
  have h2 : ∑ i ∈ Finset.Icc (t + 2) s, uT S ell M R i x ≤ ∑ i ∈ Finset.Icc 1 s, uT S ell M R i x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => uT_nonneg S ell M R i x)
  have hc : (Finset.Icc (t + 2) s).card = s - 1 - t := by rw [Nat.card_Icc]; omega
  rw [h1, hc] at h2
  exact h2

/-- the stratum factor: `(ℓ^t)^{-4} q^{2(s−1−t)} ≤ (ℓ^{s−1})^{-4}` when `ℓ⁴ q² ≤ 1`. -/
theorem strat_factor_le {ell : ℕ} (hell : 1 ≤ ell) {q : ℝ} (hq0 : 0 ≤ q) (hq : (ell : ℝ) ^ 4 * q ^ 2 ≤ 1)
    (s t : ℕ) : (((ell : ℝ) ^ t)⁻¹) ^ 4 * q ^ (2 * (s - 1 - t)) ≤ (((ell : ℝ) ^ (s - 1))⁻¹) ^ 4 := by
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hp : ∀ n : ℕ, (0 : ℝ) < (ell : ℝ) ^ n := fun n => by have := one_le_pow₀ (n := n) hellr; positivity
  by_cases hts : s - 1 ≤ t
  · have hn : s - 1 - t = 0 := by omega
    rw [hn, mul_zero, pow_zero, mul_one]
    have : (ell : ℝ) ^ (s - 1) ≤ (ell : ℝ) ^ t := pow_le_pow_right₀ hellr hts
    have : ((ell : ℝ) ^ t)⁻¹ ≤ ((ell : ℝ) ^ (s - 1))⁻¹ := inv_anti₀ (hp _) this
    exact pow_le_pow_left₀ (inv_nonneg.mpr (hp _).le) this 4
  · push Not at hts
    set n := s - 1 - t with hn
    have hsum : s - 1 = t + n := by omega
    have hpos : (0 : ℝ) < ((ell : ℝ) ^ n) ^ 4 := by have := hp n; positivity
    have key : q ^ (2 * n) ≤ (((ell : ℝ) ^ n)⁻¹) ^ 4 := by
      have h2 : ((ell : ℝ) ^ 4 * q ^ 2) ^ n ≤ 1 := pow_le_one₀ (by positivity) hq
      have e1 : ((ell : ℝ) ^ 4 * q ^ 2) ^ n = q ^ (2 * n) * ((ell : ℝ) ^ n) ^ 4 := by ring
      rw [e1] at h2
      rw [inv_pow, ← one_div, le_div_iff₀ hpos]
      exact h2
    have ht0 : (0 : ℝ) ≤ (((ell : ℝ) ^ t)⁻¹) ^ 4 := by have := hp t; positivity
    calc (((ell : ℝ) ^ t)⁻¹) ^ 4 * q ^ (2 * n) ≤ (((ell : ℝ) ^ t)⁻¹) ^ 4 * (((ell : ℝ) ^ n)⁻¹) ^ 4 :=
          mul_le_mul_of_nonneg_left key ht0
      _ = (((ell : ℝ) ^ (s - 1))⁻¹) ^ 4 := by rw [hsum, pow_add, mul_inv, mul_pow]

/-- **the D2 column sum**: `Σ_x (ℓ^{strat x})^{-4} e^{-2φ_c(x)} ≤ ℓ⁴(64 + 8ℓ³/θ³) (ℓ^{strat c})^{-1}`. -/
theorem phiC_colsum {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hell : 1 ≤ ell) {θ : ℝ} (hθ : 0 < θ)
    (hq : (ell : ℝ) ^ 3 * Real.exp (-(θ * (R * M))) ≤ 1 / 2) (c : PeriodicLatticeSite L) :
    ∑ x : PeriodicLatticeSite L, (((ell : ℝ) ^ strat S k x)⁻¹) ^ 4 * Real.exp (-(2 * phiC S ell M R k θ c x))
      ≤ (ell : ℝ) ^ 4 * (64 + 8 * (ell : ℝ) ^ 3 / θ ^ 3) * ((ell : ℝ) ^ strat S k c)⁻¹ := by
  set s := strat S k c
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hp : ∀ n : ℕ, (0 : ℝ) < (ell : ℝ) ^ n := fun n => by have := one_le_pow₀ (n := n) hellr; positivity
  set q : ℝ := Real.exp (-(θ * (R * M))) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hq4 : (ell : ℝ) ^ 4 * q ^ 2 ≤ 1 := by
    have h1 : (ell : ℝ) ^ 4 * q ^ 2 ≤ ((ell : ℝ) ^ 3 * q) ^ 2 := by
      have : (ell : ℝ) ^ 4 ≤ (ell : ℝ) ^ 6 := pow_le_pow_right₀ hellr (by norm_num)
      nlinarith [sq_nonneg q]
    have h2 : ((ell : ℝ) ^ 3 * q) ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ (by positivity) hq 2
    nlinarith
  -- pointwise
  have hpt : ∀ x, (((ell : ℝ) ^ strat S k x)⁻¹) ^ 4 * Real.exp (-(2 * phiC S ell M R k θ c x))
      ≤ (((ell : ℝ) ^ (s - 1))⁻¹) ^ 4 * Real.exp (-(2 * θ * stratWeight S ell M R k c x)) := by
    intro x
    set t := strat S k x
    have hU := sum_uT_ge hA hR hM hell c x
    have hsplit : Real.exp (-(2 * phiC S ell M R k θ c x))
        = Real.exp (-(2 * θ * stratWeight S ell M R k c x))
          * Real.exp (-(2 * (θ * ((R : ℝ) * M)) * ∑ i ∈ Finset.Icc 1 s, uT S ell M R i x)) := by
      rw [← Real.exp_add]; unfold phiC; congr 1; ring
    have hq2 : Real.exp (-(2 * (θ * ((R : ℝ) * M)) * ∑ i ∈ Finset.Icc 1 s, uT S ell M R i x))
        ≤ q ^ (2 * (s - 1 - t)) := by
      rw [hqdef, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hRM : (0 : ℝ) ≤ θ * ((R : ℝ) * M) := by positivity
      push_cast
      have := mul_le_mul_of_nonneg_left hU (show (0 : ℝ) ≤ 2 * (θ * ((R : ℝ) * M)) by positivity)
      nlinarith
    have hf := strat_factor_le hell hq0.le hq4 s t
    rw [hsplit]
    have he := Real.exp_pos (-(2 * θ * stratWeight S ell M R k c x))
    have hq2' := mul_le_mul_of_nonneg_left hq2 (show (0 : ℝ) ≤ (((ell : ℝ) ^ t)⁻¹) ^ 4 by have := hp t; positivity)
    calc (((ell : ℝ) ^ t)⁻¹) ^ 4 * (Real.exp (-(2 * θ * stratWeight S ell M R k c x))
          * Real.exp (-(2 * (θ * ((R : ℝ) * M)) * ∑ i ∈ Finset.Icc 1 s, uT S ell M R i x)))
        = ((((ell : ℝ) ^ t)⁻¹) ^ 4
          * Real.exp (-(2 * (θ * ((R : ℝ) * M)) * ∑ i ∈ Finset.Icc 1 s, uT S ell M R i x)))
          * Real.exp (-(2 * θ * stratWeight S ell M R k c x)) := by ring
      _ ≤ ((((ell : ℝ) ^ t)⁻¹) ^ 4 * q ^ (2 * (s - 1 - t))) * Real.exp (-(2 * θ * stratWeight S ell M R k c x)) :=
          mul_le_mul_of_nonneg_right hq2' he.le
      _ ≤ (((ell : ℝ) ^ (s - 1))⁻¹) ^ 4 * Real.exp (-(2 * θ * stratWeight S ell M R k c x)) :=
          mul_le_mul_of_nonneg_right hf he.le
  have hG := strat_geom_sum_flat (S := S) (M := M) (R := R) (k := k) hell hθ hq c
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpt x)
  rw [← Finset.mul_sum] at hsum
  have hA0 : (0 : ℝ) ≤ (((ell : ℝ) ^ (s - 1))⁻¹) ^ 4 := by have := hp (s - 1); positivity
  refine hsum.trans ((mul_le_mul_of_nonneg_left hG hA0).trans ?_)
  -- arithmetic
  have hs1 : (ell : ℝ) ^ s ≤ (ell : ℝ) ^ (s - 1) * ell := by
    rw [← pow_succ]; exact pow_le_pow_right₀ hellr (by omega)
  have hinv : ((ell : ℝ) ^ (s - 1))⁻¹ ≤ (ell : ℝ) * ((ell : ℝ) ^ s)⁻¹ := by
    rw [inv_le_comm₀ (hp _) (by have := hp s; positivity), mul_inv, inv_inv]
    have hl0 : (0 : ℝ) < ell := by linarith
    calc (ell : ℝ)⁻¹ * (ell : ℝ) ^ s ≤ (ell : ℝ)⁻¹ * ((ell : ℝ) ^ (s - 1) * ell) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = (ell : ℝ) ^ (s - 1) := by field_simp
  have hinv4 : (((ell : ℝ) ^ (s - 1))⁻¹) ^ 4 ≤ (ell : ℝ) ^ 4 * (((ell : ℝ) ^ s)⁻¹) ^ 4 := by
    have := pow_le_pow_left₀ (inv_nonneg.mpr (hp _).le) hinv 4
    rw [mul_pow] at this; exact this
  set X : ℝ := (ell : ℝ) ^ s with hX
  have hX1 : 1 ≤ X := one_le_pow₀ hellr
  have hXp : 0 < X := by linarith
  have hG0 : 0 ≤ 64 + 8 * (ell : ℝ) ^ 3 * (X / θ) ^ 3 := by positivity
  refine (mul_le_mul_of_nonneg_right hinv4 hG0).trans ?_
  have e : (ell : ℝ) ^ 4 * (X⁻¹) ^ 4 * (64 + 8 * (ell : ℝ) ^ 3 * (X / θ) ^ 3)
      = (ell : ℝ) ^ 4 * (64 * (X⁻¹) ^ 4 + 8 * (ell : ℝ) ^ 3 / θ ^ 3 * X⁻¹) := by
    field_simp
  rw [e]
  have h1 : (X⁻¹) ^ 4 ≤ X⁻¹ := by
    have hi : X⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hX1
    have hi0 : 0 ≤ X⁻¹ := by positivity
    calc (X⁻¹) ^ 4 = X⁻¹ * (X⁻¹) ^ 3 := by ring
      _ ≤ X⁻¹ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hi0 hi) hi0
      _ = X⁻¹ := mul_one _
  have h4 : (0 : ℝ) ≤ (ell : ℝ) ^ 4 := by positivity
  have h5 : 64 * (X⁻¹) ^ 4 + 8 * (ell : ℝ) ^ 3 / θ ^ 3 * X⁻¹ ≤ (64 + 8 * (ell : ℝ) ^ 3 / θ ^ 3) * X⁻¹ := by
    nlinarith
  have := mul_le_mul_of_nonneg_left h5 h4
  linarith

#print axioms uTerm
#print axioms uT
#print axioms uT_nonneg
#print axioms uT_le_one
#print axioms uT_zero_of_mem
#print axioms uT_one_of_not_mem
#print axioms uT_lip
#print axioms uT_step
#print axioms phiC
#print axioms phiC_nonneg
#print axioms phiC_self
#print axioms sum_uT_step
#print axioms phiC_step
#print axioms wTerm_lip_pd
#print axioms stratWeight_block
#print axioms phiC_block
#print axioms sum_uT_ge
#print axioms strat_factor_le
#print axioms phiC_colsum

end AdalyFormal.M1DStrat
