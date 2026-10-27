import DY2
import DW1

/-!
# DY5a -- the CT weight on a read ball, and the unit-bond rows of `H₁in` (M1 D-layer lane, clause 2, 2026-10-14)

* `stratWeight_near` : two sites of stratum `≥ j` at distance `≤ D ℓ^j` differ in `stratWeight` by `≤ D`;
* `phiC_near` : two sites of `Ω₀` with stratum in `[j, j+2]` at distance `≤ D ℓ^j` differ in `phiC θ c` by `≤ 4θD`;
* `ball_strat` : a site read by a level-`n ≥ 1` row lies in `Ω₀` with stratum in `[n−1, n+1]`;
* **`ball_osc`** : on the read ball of a level-`n ≥ 1` row, `|phiC θ c (e.1) − phiC θ c (b.1)| ≤ 32 θ ℓ`;
* **`tau_adj_single`** : `τ*(δ_e v)` is the single top-level row `(k, ι e)` (or `0` when `ι e` is no constraint bond).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_shift_le pdist_self rhoT rhoT_le)
open AdalyFormal.IngredientFamilyR2 (geomOf bondsLam BIdx FSp tauExt unitBondEmb)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.M1 (strat bstrat strat_le om_anti le_strat_of_mem mem_of_le_strat stratWeight wTerm wTerm_dom
  inf'_lip inf'_eq_of_dom)
open AdalyFormal.M1DStrat.DQ (row_anchor mem_prev strat_le_of_near room_prev room_next)

variable {L : PeriodicLatticeExtent}

/-! ## 1. the weight near a site -/

theorem stratWeight_near {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hell : 2 ≤ ell)
    (c : PeriodicLatticeSite L) {j : ℕ} {x y : PeriodicLatticeSite L} (hx : j ≤ strat S k x) (hy : j ≤ strat S k y)
    (Dd : ℝ) (hxy : (pdist x y : ℝ) ≤ Dd * (ell : ℝ) ^ j) :
    |stratWeight S ell M R k c x - stratWeight S ell M R k c y| ≤ Dd := by
  set s := strat S k c
  have hell1 : 1 ≤ ell := by omega
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have hD0 : 0 ≤ Dd := by
    have hp : (0 : ℝ) < (ell : ℝ) ^ j := by have := one_le_pow₀ (n := j) hellr; positivity
    by_contra h; push Not at h
    have : Dd * (ell : ℝ) ^ j < 0 := mul_neg_of_neg_of_pos h hp
    have : (0 : ℝ) ≤ pdist x y := by positivity
    linarith
  have slope : ∀ m, j ≤ m → |wTerm R M ell s m c x - wTerm R M ell s m c y| ≤ Dd := by
    intro m hm
    refine (AdalyFormal.M1DStrat.wTerm_lip_pd R M ell s m hell1 c x y).trans ?_
    have hp : (0 : ℝ) < (ell : ℝ) ^ m := by have := one_le_pow₀ (n := m) hellr; positivity
    rw [div_le_iff₀ hp]
    have : (ell : ℝ) ^ j ≤ (ell : ℝ) ^ m := pow_le_pow_right₀ hellr hm
    nlinarith
  by_cases hjs : j ≤ s + 1
  · unfold stratWeight
    exact inf'_lip _ _ _ _ _ (fun m hm => slope m (le_trans hjs (Finset.mem_Icc.mp hm).1))
  · push Not at hjs
    have hjk : j ≤ k := hx.trans (strat_le S k x)
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
    rw [inf'_eq_of_dom _ J _ hJne hJI _ (hdomz x hx), inf'_eq_of_dom _ J _ hJne hJI _ (hdomz y hy)]
    exact inf'_lip _ _ _ _ _ (fun m hm => slope m (Finset.mem_Icc.mp hm).1)

theorem phiC_near {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hell : 2 ≤ ell) {θ : ℝ} (hθ : 0 ≤ θ) (c : PeriodicLatticeSite L) {j : ℕ} {x y : PeriodicLatticeSite L}
    (hx0 : x ∈ S.Om 0) (hy0 : y ∈ S.Om 0) (hxl : j ≤ strat S k x) (hxu : strat S k x ≤ j + 2)
    (hyl : j ≤ strat S k y) (hyu : strat S k y ≤ j + 2) (Dd : ℝ) (hxy : (pdist x y : ℝ) ≤ Dd * (ell : ℝ) ^ j) :
    |phiC S ell M R k θ c x - phiC S ell M R k θ c y| ≤ 4 * θ * Dd := by
  have hV := stratWeight_near hA hell c hxl hyl Dd hxy
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hRM : (0 : ℝ) < (R : ℝ) * M := by positivity
  have hD0 : 0 ≤ Dd := le_trans (abs_nonneg _) hV
  have hU : |∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i x - ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i y|
      ≤ 3 * (Dd / ((R : ℝ) * M)) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ i ∈ Finset.Icc 1 (strat S k c), |uT S ell M R i x - uT S ell M R i y|
        ≤ if i ∈ Finset.Icc (j + 1) (j + 3) then Dd / ((R : ℝ) * M) else 0 := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      have hik : i ≤ k := hi.2.trans (strat_le S k c)
      by_cases hij : i ∈ Finset.Icc (j + 1) (j + 3)
      · rw [if_pos hij]
        rw [Finset.mem_Icc] at hij
        refine (uT_lip S ell M R i x y).trans ?_
        have hp : (0 : ℝ) < (R : ℝ) * M * (ell : ℝ) ^ (i - 1) := by have := one_le_pow₀ (n := i - 1) hellr; positivity
        rw [div_le_div_iff₀ hp hRM]
        have h1 : (ell : ℝ) ^ j ≤ (ell : ℝ) ^ (i - 1) := pow_le_pow_right₀ hellr (by omega)
        have : (pdist x y : ℝ) * ((R : ℝ) * M) ≤ Dd * (ell : ℝ) ^ j * ((R : ℝ) * M) :=
          mul_le_mul_of_nonneg_right hxy hRM.le
        have : Dd * (ell : ℝ) ^ j * ((R : ℝ) * M) ≤ Dd * ((R : ℝ) * M * (ell : ℝ) ^ (i - 1)) := by
          have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hD0 hRM.le)
          nlinarith
        linarith
      · rw [if_neg hij]
        rw [Finset.mem_Icc] at hij
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
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.Icc 1 (strat S k c)).filter (fun i => i ∈ Finset.Icc (j + 1) (j + 3))).card ≤ 3 := by
      refine (Finset.card_le_card (fun i hi => ?_)).trans (by simp : (Finset.Icc (j + 1) (j + 3)).card ≤ 3)
      exact (Finset.mem_filter.mp hi).2
    have hc' : (((Finset.Icc 1 (strat S k c)).filter (fun i => i ∈ Finset.Icc (j + 1) (j + 3))).card : ℝ) ≤ 3 := by
      exact_mod_cast hc
    exact mul_le_mul_of_nonneg_right hc' (by positivity)
  unfold phiC
  have e : θ * stratWeight S ell M R k c x + θ * ((R : ℝ) * M) * ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i x
      - (θ * stratWeight S ell M R k c y + θ * ((R : ℝ) * M) * ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i y)
      = θ * (stratWeight S ell M R k c x - stratWeight S ell M R k c y)
        + θ * ((R : ℝ) * M) * (∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i x
          - ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i y) := by ring
  rw [e]
  have h1 : |θ * (stratWeight S ell M R k c x - stratWeight S ell M R k c y)| ≤ θ * Dd := by
    rw [abs_mul, abs_of_nonneg hθ]; exact mul_le_mul_of_nonneg_left hV hθ
  have h2 : |θ * ((R : ℝ) * M) * (∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i x
      - ∑ i ∈ Finset.Icc 1 (strat S k c), uT S ell M R i y)| ≤ θ * (3 * Dd) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have : θ * ((R : ℝ) * M) * (3 * (Dd / ((R : ℝ) * M))) = θ * (3 * Dd) := by field_simp
    rw [← this]; exact mul_le_mul_of_nonneg_left hU (by positivity)
  have := (abs_add_le _ _).trans (add_le_add h1 h2)
  linarith

/-! ## 2. the read ball -/

section ballw
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
  (hA : Admissible ell M R k S) (hell2 : 2 ≤ ell) (hroom : 18 * ell ≤ R * M)
include hA hell2 hroom

theorem ball_strat {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k) {b : Bond (scaleUp ell k Lu)}
    (hb : b ∈ bondsLam (geomOf ell k S) n) (z : PeriodicLatticeSite (scaleUp ell k Lu)) (hz : pdist b.1 z ≤ rhoT ell n) :
    z ∈ S.Om 0 ∧ n - 1 ≤ strat S k z ∧ strat S k z ≤ n + 1 := by
  obtain ⟨y, hy, hy', hby, -⟩ := row_anchor ell k S hb
  have hR1 := room_prev hell2 hroom hn1 (n := n)
  have hR2 := room_next hell2 hroom n
  have hzy : pdist z y ≤ rhoT ell n + ell ^ n := by
    have := pdist_triangle z b.1 y
    rw [pdist_comm z b.1] at this
    omega
  have h1 : pdist z y ≤ R * M * ell ^ (n - 1) := by omega
  have hm := mem_prev hA hn1 hnk hy h1
  refine ⟨om_anti hA (Nat.zero_le _) hm, le_strat_of_mem (by omega) hm, ?_⟩
  have hyz : pdist y z ≤ R * (M * ell ^ (n + 1)) := by rw [pdist_comm]; omega
  exact strat_le_of_near hA hnk hy hy' hyz

/-- **the CT weight on a read ball** -/
theorem ball_osc (hR : 1 ≤ R) (hM : 1 ≤ M) {θ : ℝ} (hθ : 0 ≤ θ) (c : PeriodicLatticeSite (scaleUp ell k Lu))
    (p : BIdx (geomOf ell k S)) (hp1 : 1 ≤ (p.1 : ℕ)) (e : Bond (scaleUp ell k Lu))
    (he : e.1 ∈ Ball p.2.1.1 (rhoT ell p.1)) :
    |phiC S ell M R k θ c e.1 - phiC S ell M R k θ c p.2.1.1| ≤ 32 * θ * ell := by
  have hnk : (p.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  set n : ℕ := (p.1 : ℕ) with hn
  have hb : p.2.1 ∈ bondsLam (geomOf ell k S) n := p.2.2
  have hze : pdist p.2.1.1 e.1 ≤ rhoT ell n := he
  have hzb : pdist p.2.1.1 p.2.1.1 ≤ rhoT ell n := by rw [pdist_self]; exact Nat.zero_le _
  obtain ⟨he0, hel, heu⟩ := ball_strat hA hell2 hroom hp1 hnk hb e.1 hze
  obtain ⟨hb0, hbl, hbu⟩ := ball_strat hA hell2 hroom hp1 hnk hb p.2.1.1 hzb
  have hT := rhoT_le ell hell2 n
  have hd : (pdist e.1 p.2.1.1 : ℝ) ≤ (8 * ell : ℝ) * (ell : ℝ) ^ (n - 1) := by
    have h1 : pdist e.1 p.2.1.1 ≤ 8 * ell ^ n := by rw [pdist_comm]; omega
    have h2 : (8 * ell ^ n : ℕ) = 8 * ell * ell ^ (n - 1) := by
      rw [Nat.mul_assoc, ← pow_succ']; congr 2; omega
    have h3 : pdist e.1 p.2.1.1 ≤ 8 * ell * ell ^ (n - 1) := h2 ▸ h1
    exact_mod_cast h3
  have h := phiC_near hA hR hM hell2 hθ c he0 hb0 hel (by omega) hbl (by omega) (8 * ell) hd
  linarith

end ballw

/-! ## 3. the adjoint of the unit-bond projection on a single bond -/

theorem inner_single_left_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (i : ι) (v : F) (y : PiLp 2 (fun _ : ι => F)) :
    ⟪(WithLp.toLp 2 (Pi.single i v) : PiLp 2 (fun _ : ι => F)), y⟫ = ⟪v, y i⟫ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · intro h; exact absurd (Finset.mem_univ i) h

open Classical in
theorem tau_adj_single (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (e : Bond Lu) (v : SuTwo) :
    ContinuousLinearMap.adjoint (tauExt ell k Lu hell S) (WithLp.toLp 2 (Pi.single e v) : BondFnL2 Lu)
      = if hb : unitBondEmb ell k Lu hell e ∈ bondsLam (geomOf ell k S) k
        then (WithLp.toLp 2 (Pi.single ⟨Fin.last k, ⟨unitBondEmb ell k Lu hell e, hb⟩⟩ v) : FSp (geomOf ell k S))
        else 0 := by
  apply ext_inner_right ℝ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left, inner_single_left_pi]
  have ht : (tauExt ell k Lu hell S f) e = if hb : unitBondEmb ell k Lu hell e ∈ bondsLam (geomOf ell k S) k
      then WithLp.ofLp f ⟨Fin.last k, ⟨unitBondEmb ell k Lu hell e, hb⟩⟩ else 0 := rfl
  rw [ht]
  split_ifs with hb
  · rw [inner_single_left_pi]
  · simp

#print axioms stratWeight_near
#print axioms phiC_near
#print axioms ball_strat
#print axioms ball_osc
#print axioms inner_single_left_pi
#print axioms tau_adj_single

end AdalyFormal.M1DStrat
