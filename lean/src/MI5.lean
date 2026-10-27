import M1G2

/-!
# MI5 -- the smooth stratified log-weight `ψ ≈ strat · ln ℓ` (M1 lane E, 2026-10-13)

`dcap S W ell m x = min(Wℓ^m, dist(x, Ω_{m+1}ᶜ))` (capped ℓ¹ distance to the complement of `Ω_{m+1}`),
`tw m x = dcap m x / (Wℓ^m) ∈ [0,1]`, `psiW x = ln ℓ · Σ_{m<k} tw m x`.  On an admissible tower with `1 ≤ W ≤ R M ℓ`:
* `psiW_bounds`  : `(strat x − 1)·ln ℓ ≤ ψ(x) ≤ strat x · ln ℓ` (and `ψ = 0` on stratum `0`): `e^ψ ≍ ℓ^{strat}` within a factor `ℓ`;
* `psiW_lip`     : `|ψ(x) − ψ(x+e_μ)| ≤ θ / ℓ^{strat(x+e_μ)}` and `≤ θ / ℓ^{strat x}`, `θ = 2 ℓ² ln ℓ / W`;
* `psiW_osc`     : two sites of the same stratum `j` at ℓ¹-distance `d`: `|ψ(x) − ψ(y)| ≤ ln ℓ · d / (W ℓ^{j−1})`.
`θ` is small when the collar parameter `W` (≤ R M ℓ) is large: this is the Combes–Thomas weight of the stratified site chain.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1IMS

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_shift_le pdist_triangle pdist_self)
open AdalyFormal.M1

variable {L : PeriodicLatticeExtent}

open Classical

/-- the cap at level `m`. -/
noncomputable def capW (W ell m : ℕ) : ℝ := (W : ℝ) * (ell : ℝ) ^ m

/-- capped distance to the complement of `Ω_{m+1}`. -/
noncomputable def dcap (S : Tower L) (W ell m : ℕ) (x : PeriodicLatticeSite L) : ℝ :=
  min (capW W ell m)
    (Finset.univ.inf' Finset.univ_nonempty
      (fun z : PeriodicLatticeSite L => if z ∈ S.Om (m + 1) then capW W ell m else (pdist x z : ℝ)))

/-- the level-`m` transition profile, in `[0,1]`. -/
noncomputable def tw (S : Tower L) (W ell m : ℕ) (x : PeriodicLatticeSite L) : ℝ := dcap S W ell m x / capW W ell m

/-- **the stratified log-weight.** -/
noncomputable def psiW (S : Tower L) (W ell k : ℕ) (x : PeriodicLatticeSite L) : ℝ :=
  Real.log ell * ∑ m ∈ Finset.range k, tw S W ell m x

theorem capW_pos {W ell : ℕ} (hW : 1 ≤ W) (hell : 1 ≤ ell) (m : ℕ) : 0 < capW W ell m := by
  unfold capW
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  positivity

theorem dcap_le (S : Tower L) (W ell m : ℕ) (x : PeriodicLatticeSite L) : dcap S W ell m x ≤ capW W ell m :=
  min_le_left _ _

theorem dcap_nonneg (S : Tower L) {W ell : ℕ} (hW : 1 ≤ W) (hell : 1 ≤ ell) (m : ℕ) (x : PeriodicLatticeSite L) :
    0 ≤ dcap S W ell m x := by
  unfold dcap
  refine le_min (capW_pos hW hell m).le ?_
  refine Finset.le_inf' _ _ (fun z _ => ?_)
  split_ifs
  · exact (capW_pos hW hell m).le
  · exact Nat.cast_nonneg _

/-- `dcap` is `1`-Lipschitz for the ℓ¹ distance. -/
theorem dcap_lip (S : Tower L) (W ell m : ℕ) (x y : PeriodicLatticeSite L) :
    |dcap S W ell m x - dcap S W ell m y| ≤ (pdist x y : ℝ) := by
  unfold dcap
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) ?_)
  refine inf'_lip _ _ _ _ _ (fun z _ => ?_)
  split_ifs
  · simp
  · have t1 := pdist_triangle x y z
    have t2 := pdist_triangle y x z
    have t3 := pdist_comm x y
    have r1 : (pdist x z : ℝ) ≤ pdist x y + pdist y z := by exact_mod_cast t1
    have r2 : (pdist y z : ℝ) ≤ pdist x y + pdist x z := by
      have : pdist y z ≤ pdist x y + pdist x z := by omega
      exact_mod_cast this
    rw [abs_le]; constructor <;> linarith

/-- off `Ω_{m+1}` the capped distance vanishes. -/
theorem dcap_off (S : Tower L) {W ell : ℕ} (hW : 1 ≤ W) (hell : 1 ≤ ell) (m : ℕ) {x : PeriodicLatticeSite L}
    (hx : x ∉ S.Om (m + 1)) : dcap S W ell m x = 0 := by
  refine le_antisymm ?_ (dcap_nonneg S hW hell m x)
  unfold dcap
  refine (min_le_right _ _).trans ?_
  refine (Finset.inf'_le _ (Finset.mem_univ x)).trans ?_
  rw [if_neg hx, pdist_self]; simp

/-- deep in `Ω_{m+2}` the capped distance is the cap (collar; `W ≤ R M ℓ`). -/
theorem dcap_deep {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) {W : ℕ}
    (hWR : W ≤ R * M * ell) {m : ℕ} (hm : m + 1 ≤ k) {x : PeriodicLatticeSite L} (hx : x ∈ S.Om (m + 2)) :
    dcap S W ell m x = capW W ell m := by
  unfold dcap
  refine min_eq_left (Finset.le_inf' _ _ (fun z _ => ?_))
  split_ifs with hz
  · exact le_rfl
  · have hc := collar hA (j := m + 1) hm hz hx
    have hc' : R * bigSide M ell (m + 1) < pdist x z := by rw [pdist_comm]; exact hc
    unfold bigSide at hc'
    have h1 : W * ell ^ m ≤ R * (M * ell ^ (m + 1)) := by
      calc W * ell ^ m ≤ R * M * ell * ell ^ m := Nat.mul_le_mul_right _ hWR
        _ = R * (M * ell ^ (m + 1)) := by rw [pow_succ]; ring
    have h2 : W * ell ^ m < pdist x z := lt_of_le_of_lt h1 hc'
    unfold capW
    have : ((W * ell ^ m : ℕ) : ℝ) < (pdist x z : ℝ) := by exact_mod_cast h2
    push_cast at this
    linarith

theorem tw_nonneg (S : Tower L) {W ell : ℕ} (hW : 1 ≤ W) (hell : 1 ≤ ell) (m : ℕ) (x : PeriodicLatticeSite L) :
    0 ≤ tw S W ell m x := div_nonneg (dcap_nonneg S hW hell m x) (capW_pos hW hell m).le

theorem tw_le_one (S : Tower L) {W ell : ℕ} (hW : 1 ≤ W) (hell : 1 ≤ ell) (m : ℕ) (x : PeriodicLatticeSite L) :
    tw S W ell m x ≤ 1 := by
  unfold tw; rw [div_le_one (capW_pos hW hell m)]; exact dcap_le S W ell m x

theorem tw_lip (S : Tower L) {W ell : ℕ} (hW : 1 ≤ W) (hell : 1 ≤ ell) (m : ℕ) (x y : PeriodicLatticeSite L) :
    |tw S W ell m x - tw S W ell m y| ≤ (pdist x y : ℝ) / capW W ell m := by
  unfold tw
  rw [← sub_div, abs_div, abs_of_pos (capW_pos hW hell m)]
  exact div_le_div_of_nonneg_right (dcap_lip S W ell m x y) (capW_pos hW hell m).le

/-- the profile of level `m` as a function of the stratum. -/
theorem tw_of_strat {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) {W : ℕ} (hW : 1 ≤ W)
    (hell : 1 ≤ ell) (hWR : W ≤ R * M * ell) {m : ℕ} (hm : m < k) (x : PeriodicLatticeSite L) :
    (strat S k x ≤ m → tw S W ell m x = 0) ∧ (m + 2 ≤ strat S k x → tw S W ell m x = 1) := by
  constructor
  · intro hs
    have hx : x ∉ S.Om (m + 1) := by
      intro hx
      have := (le_strat_iff hA (by omega) (by omega) x).mpr hx
      omega
    unfold tw; rw [dcap_off S hW hell m hx, zero_div]
  · intro hs
    have hx : x ∈ S.Om (m + 2) := (le_strat_iff hA (by omega) (by have := strat_le S k x; omega) x).mp hs
    unfold tw; rw [dcap_deep hA hWR (by omega) hx, div_self (capW_pos hW hell m).ne']

/-- **`ψ ≍ strat · ln ℓ`**: `(strat − 1) ln ℓ ≤ ψ ≤ strat · ln ℓ`, `0 ≤ ψ`. -/
theorem psiW_bounds {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) {W : ℕ} (hW : 1 ≤ W)
    (hell : 1 ≤ ell) (hWR : W ≤ R * M * ell) (x : PeriodicLatticeSite L) :
    0 ≤ psiW S W ell k x ∧ psiW S W ell k x ≤ (strat S k x : ℝ) * Real.log ell ∧
      ((strat S k x : ℝ) - 1) * Real.log ell ≤ psiW S W ell k x := by
  set s := strat S k x with hs
  have hsk : s ≤ k := strat_le S k x
  have hlog : 0 ≤ Real.log ell := Real.log_nonneg (by exact_mod_cast hell)
  have hsum_le : ∑ m ∈ Finset.range k, tw S W ell m x ≤ s := by
    have : ∀ m ∈ Finset.range k, tw S W ell m x ≤ if m < s then 1 else 0 := by
      intro m hm
      have hm' := Finset.mem_range.mp hm
      split_ifs with h
      · exact tw_le_one S hW hell m x
      · exact le_of_eq ((tw_of_strat hA hW hell hWR hm' x).1 (by omega))
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : ((Finset.range k).filter (fun m => m < s)).card ≤ s := by
      calc ((Finset.range k).filter (fun m => m < s)).card ≤ (Finset.range s).card := by
            refine Finset.card_le_card (fun m hm => ?_)
            simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢; exact hm.2
        _ = s := Finset.card_range s
    exact_mod_cast this
  have hsum_ge : (s : ℝ) - 1 ≤ ∑ m ∈ Finset.range k, tw S W ell m x := by
    have : ∀ m ∈ Finset.range k, (if m + 2 ≤ s then (1 : ℝ) else 0) ≤ tw S W ell m x := by
      intro m hm
      have hm' := Finset.mem_range.mp hm
      split_ifs with h
      · exact le_of_eq ((tw_of_strat hA hW hell hWR hm' x).2 h).symm
      · exact tw_nonneg S hW hell m x
    refine le_trans ?_ (Finset.sum_le_sum this)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · rw [h0]; simp
    · have hsub2 : Finset.range (s - 1) ⊆ (Finset.range k).filter (fun m => m + 2 ≤ s) := by
        intro m hm
        simp only [Finset.mem_range] at hm
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by omega⟩
      have h4 := Finset.card_le_card hsub2
      rw [Finset.card_range] at h4
      have h5 : ((s - 1 : ℕ) : ℝ) ≤ (((Finset.range k).filter (fun m => m + 2 ≤ s)).card : ℝ) := by exact_mod_cast h4
      have h3 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      linarith
  have hsum0 : 0 ≤ ∑ m ∈ Finset.range k, tw S W ell m x :=
    Finset.sum_nonneg (fun m _ => tw_nonneg S hW hell m x)
  unfold psiW
  refine ⟨mul_nonneg hlog hsum0, ?_, ?_⟩
  · rw [mul_comm]; exact mul_le_mul_of_nonneg_right hsum_le hlog
  · rw [mul_comm (Real.log ell)]; exact mul_le_mul_of_nonneg_right hsum_ge hlog

/-- the profile of level `m` is constant (`0` or `1`) unless `m + 1` is the stratum of one of two adjacent sites. -/
theorem tw_eq_of_adj {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) {W : ℕ} (hW : 1 ≤ W)
    (hell : 1 ≤ ell) (hR : 1 ≤ R) (hM : 1 ≤ M) (hWR : W ≤ R * M * ell) {m : ℕ} (hm : m < k)
    (x : PeriodicLatticeSite L) (μ : Fin 3) (hne : strat S k x ≠ m + 1)
    (hne' : strat S k (periodicLatticeShift x μ) ≠ m + 1) :
    tw S W ell m x = tw S W ell m (periodicLatticeShift x μ) := by
  have hadj := strat_adj hA hR hM hell x μ
  have h1 := tw_of_strat hA hW hell hWR hm x
  have h2 := tw_of_strat hA hW hell hWR hm (periodicLatticeShift x μ)
  rcases le_or_gt (strat S k x) m with hx | hx
  · rw [h1.1 hx, h2.1 (by omega)]
  · rw [h1.2 (by omega), h2.2 (by omega)]

/-- **bond Lipschitz bound of `ψ`** (indexed by either endpoint's stratum): `|ψ(x) − ψ(x+e_μ)| ≤ θ/ℓ^{strat}`,
`θ = 2 ℓ² ln ℓ / W`. -/
theorem psiW_lip {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) {W : ℕ} (hW : 1 ≤ W)
    (hell : 1 ≤ ell) (hR : 1 ≤ R) (hM : 1 ≤ M) (hWR : W ≤ R * M * ell) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    |psiW S W ell k x - psiW S W ell k (periodicLatticeShift x μ)|
        ≤ (2 * (ell : ℝ) ^ 2 * Real.log ell / W) / (ell : ℝ) ^ strat S k (periodicLatticeShift x μ) ∧
      |psiW S W ell k x - psiW S W ell k (periodicLatticeShift x μ)|
        ≤ (2 * (ell : ℝ) ^ 2 * Real.log ell / W) / (ell : ℝ) ^ strat S k x := by
  have hadj := strat_adj hA hR hM hell x μ
  set x' := periodicLatticeShift x μ
  set s := strat S k x
  set s' := strat S k x'
  have hlog : 0 ≤ Real.log ell := Real.log_nonneg (by exact_mod_cast hell)
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  -- per-level difference
  have hd : ∀ m ∈ Finset.range k, |tw S W ell m x - tw S W ell m x'|
      ≤ (if m + 1 = s ∨ m + 1 = s' then 1 / capW W ell m else 0) := by
    intro m hm
    have hm' := Finset.mem_range.mp hm
    split_ifs with h
    · have := tw_lip S hW hell m x x'
      refine this.trans ?_
      have hp : (pdist x x' : ℝ) ≤ 1 := by exact_mod_cast pdist_shift_le x μ
      exact div_le_div_of_nonneg_right hp (capW_pos hW hell m).le
    · push Not at h
      rw [tw_eq_of_adj hA hW hell hR hM hWR hm' x μ (fun e => h.1 e.symm) (fun e => h.2 e.symm), sub_self, abs_zero]
  have hsum : |∑ m ∈ Finset.range k, (tw S W ell m x - tw S W ell m x')|
      ≤ ∑ m ∈ Finset.range k, (if m + 1 = s ∨ m + 1 = s' then 1 / capW W ell m else 0) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hd)
  -- the right side has at most two nonzero terms, each ≤ ℓ / (W ℓ^{min(s,s')})
  set t := min s s' with ht
  have hterm : ∀ m ∈ Finset.range k, (if m + 1 = s ∨ m + 1 = s' then 1 / capW W ell m else 0)
      ≤ (if m + 1 = s then (ell : ℝ) / (W * (ell : ℝ) ^ t) else 0)
        + (if m + 1 = s' then (ell : ℝ) / (W * (ell : ℝ) ^ t) else 0) := by
    intro m _
    have hb : ∀ (hm1 : m + 1 = s ∨ m + 1 = s'), 1 / capW W ell m ≤ (ell : ℝ) / (W * (ell : ℝ) ^ t) := by
      intro hm1
      have htm : t ≤ m + 1 := by rcases hm1 with h | h <;> omega
      unfold capW
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (ell : ℝ) ^ t ≤ (ell : ℝ) ^ (m + 1) := pow_le_pow_right₀ hellr htm
      rw [pow_succ] at this
      nlinarith [pow_pos (show (0:ℝ) < ell by linarith) m]
    by_cases h1 : m + 1 = s
    · rw [if_pos (Or.inl h1), if_pos h1]
      have := hb (Or.inl h1)
      have h0 : (0 : ℝ) ≤ (if m + 1 = s' then (ell : ℝ) / (W * (ell : ℝ) ^ t) else 0) := by
        split_ifs <;> positivity
      linarith
    · by_cases h2 : m + 1 = s'
      · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2, zero_add]; exact hb (Or.inr h2)
      · rw [if_neg (by tauto), if_neg h1, if_neg h2]; simp
  have htot : ∑ m ∈ Finset.range k, (if m + 1 = s ∨ m + 1 = s' then 1 / capW W ell m else 0)
      ≤ 2 * ((ell : ℝ) / (W * (ell : ℝ) ^ t)) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib]
    have e1 : ∀ s0 : ℕ, ∑ m ∈ Finset.range k, (if m + 1 = s0 then (ell : ℝ) / (W * (ell : ℝ) ^ t) else 0)
        ≤ (ell : ℝ) / (W * (ell : ℝ) ^ t) := by
      intro s0
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have hc : ((Finset.range k).filter (fun m => m + 1 = s0)).card ≤ 1 := by
        refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
        simp only [Finset.mem_filter] at ha hb; omega
      have : (((Finset.range k).filter (fun m => m + 1 = s0)).card : ℝ) ≤ 1 := by exact_mod_cast hc
      have hp : 0 ≤ (ell : ℝ) / (W * (ell : ℝ) ^ t) := by positivity
      nlinarith
    linarith [e1 s, e1 s']
  have hdiff : psiW S W ell k x - psiW S W ell k x' = Real.log ell * ∑ m ∈ Finset.range k, (tw S W ell m x - tw S W ell m x') := by
    unfold psiW; rw [Finset.sum_sub_distrib, mul_sub]
  have hmain : |psiW S W ell k x - psiW S W ell k x'| ≤ Real.log ell * (2 * ((ell : ℝ) / (W * (ell : ℝ) ^ t))) := by
    rw [hdiff, abs_mul, abs_of_nonneg hlog]
    exact mul_le_mul_of_nonneg_left (hsum.trans htot) hlog
  -- convert ℓ^{-t} to ℓ^{1-s'} and ℓ^{1-s}
  have hconv : ∀ r : ℕ, r ≤ t + 1 → Real.log ell * (2 * ((ell : ℝ) / (W * (ell : ℝ) ^ t)))
      ≤ (2 * (ell : ℝ) ^ 2 * Real.log ell / W) / (ell : ℝ) ^ r := by
    intro r hr
    have hpos : (0 : ℝ) < ell := by linarith
    have hpr : (ell : ℝ) ^ r ≤ (ell : ℝ) ^ (t + 1) := pow_le_pow_right₀ hellr hr
    rw [pow_succ] at hpr
    have e : Real.log ell * (2 * ((ell : ℝ) / (W * (ell : ℝ) ^ t)))
        = (2 * (ell : ℝ) * Real.log ell / W) / (ell : ℝ) ^ t := by field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : 0 ≤ 2 * (ell : ℝ) * Real.log ell / W := by positivity
    have : 2 * (ell : ℝ) * Real.log ell / W * (ell : ℝ) ^ r ≤ 2 * (ell : ℝ) * Real.log ell / W * ((ell : ℝ) ^ t * ell) :=
      mul_le_mul_of_nonneg_left hpr h0
    have e2 : 2 * (ell : ℝ) ^ 2 * Real.log ell / W * (ell : ℝ) ^ t
        = 2 * (ell : ℝ) * Real.log ell / W * ((ell : ℝ) ^ t * ell) := by ring
    linarith
  exact ⟨hmain.trans (hconv s' (by omega)), hmain.trans (hconv s (by omega))⟩

/-- **oscillation of `ψ` on a stratum**: two sites of stratum `j ≥ 1` at ℓ¹-distance `d` have
`|ψ(x) − ψ(y)| ≤ ln ℓ · d / (W ℓ^{j−1})`. -/
theorem psiW_osc {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) {W : ℕ} (hW : 1 ≤ W)
    (hell : 1 ≤ ell) (hWR : W ≤ R * M * ell) {j : ℕ} {x y : PeriodicLatticeSite L}
    (hx : strat S k x = j) (hy : strat S k y = j) :
    |psiW S W ell k x - psiW S W ell k y| ≤ Real.log ell * ((pdist x y : ℝ) / capW W ell (j - 1)) := by
  have hlog : 0 ≤ Real.log ell := Real.log_nonneg (by exact_mod_cast hell)
  have hdiff : psiW S W ell k x - psiW S W ell k y = Real.log ell * ∑ m ∈ Finset.range k, (tw S W ell m x - tw S W ell m y) := by
    unfold psiW; rw [Finset.sum_sub_distrib, mul_sub]
  rw [hdiff, abs_mul, abs_of_nonneg hlog]
  refine mul_le_mul_of_nonneg_left ?_ hlog
  have hterm : ∀ m ∈ Finset.range k, |tw S W ell m x - tw S W ell m y|
      ≤ if m + 1 = j then (pdist x y : ℝ) / capW W ell (j - 1) else 0 := by
    intro m hm
    have hm' := Finset.mem_range.mp hm
    split_ifs with h
    · have := tw_lip S hW hell m x y
      rwa [show j - 1 = m by omega]
    · have h1 := tw_of_strat hA hW hell hWR hm' x
      have h2 := tw_of_strat hA hW hell hWR hm' y
      rcases le_or_gt j m with hj | hj
      · rw [h1.1 (by omega), h2.1 (by omega)]; simp
      · rw [h1.2 (by omega), h2.2 (by omega)]; simp
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.range k).filter (fun m => m + 1 = j)).card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
    simp only [Finset.mem_filter] at ha hb; omega
  have : (((Finset.range k).filter (fun m => m + 1 = j)).card : ℝ) ≤ 1 := by exact_mod_cast hc
  have hp : 0 ≤ (pdist x y : ℝ) / capW W ell (j - 1) := div_nonneg (Nat.cast_nonneg _) (capW_pos hW hell _).le
  nlinarith

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.capW_pos
#print axioms AdalyFormal.M1IMS.dcap_le
#print axioms AdalyFormal.M1IMS.dcap_nonneg
#print axioms AdalyFormal.M1IMS.dcap_lip
#print axioms AdalyFormal.M1IMS.dcap_off
#print axioms AdalyFormal.M1IMS.dcap_deep
#print axioms AdalyFormal.M1IMS.tw_nonneg
#print axioms AdalyFormal.M1IMS.tw_le_one
#print axioms AdalyFormal.M1IMS.tw_lip
#print axioms AdalyFormal.M1IMS.tw_of_strat
#print axioms AdalyFormal.M1IMS.psiW_bounds
#print axioms AdalyFormal.M1IMS.tw_eq_of_adj
#print axioms AdalyFormal.M1IMS.psiW_lip
#print axioms AdalyFormal.M1IMS.psiW_osc
#print axioms AdalyFormal.M1IMS.capW
#print axioms AdalyFormal.M1IMS.dcap
#print axioms AdalyFormal.M1IMS.tw
#print axioms AdalyFormal.M1IMS.psiW
