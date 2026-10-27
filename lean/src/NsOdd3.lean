import NsOdd2

/-!
# NsOdd3 -- the first blocked level of the staggered layer for ODD `ell`, at EVERY base (truncated blocks included) (lane ncwdh_strong_20261017)

`phi1o L c ell t` = `fld A0 A1` with (all functions of the coordinate values; `cnt_μ(v) = min ell (N_μ - v)`, `N_μ = L μ + 1`)
* `A0 z₀ z₁ z₂ = t (-1)^{z₁} D(z₀) a(z₁,z₂)`, `a = cnt₂(z₂) ⌊cnt₁(z₁)/2⌋ / ell²`, `D(v) = [v = c] - [(v+ell) mod N₀ = c]`;
* `A1 z₀ z₁ z₂ = t (-1)^{z₁} ([z₀ = c] + E(z₀) p(z₁,z₂))`, `p = cnt₂(z₂) (cnt₁(z₁) mod 2) / ell³`, `E(v) = [c < v + ell ∧ v ≤ c] - ell [v = c]`.
`blockAng_stag_odd` : `blockAngG 1 ell (stagφ c t) z μ = phi1o .. (z, μ)` for every base `z`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

/-! ## sums over truncated blocks with three independent factors -/

theorem sum_fin_window_abs (N y ell : ℕ) (g : ℕ → ℝ) :
    ∑ a : Fin N, (if y ≤ a.val ∧ a.val < y + ell then g (a.val - y) else 0) = ∑ n ∈ Finset.range (min ell (N - y)), g n :=
  sum_fin_window N y ell g

theorem sum_block_gen (z : PeriodicLatticeSite L) (ell : ℕ) (g0 g1 g2 : ℕ → ℝ) :
    ∑ x ∈ stepBlockOf z 1 ell, g0 ((x 0).val - (z 0).val) * g1 ((x 1).val - (z 1).val) * g2 ((x 2).val - (z 2).val) =
      (∑ n ∈ Finset.range (min ell (L 0 + 1 - (z 0).val)), g0 n) * (∑ n ∈ Finset.range (min ell (L 1 + 1 - (z 1).val)), g1 n) *
        ∑ n ∈ Finset.range (min ell (L 2 + 1 - (z 2).val)), g2 n := by
  classical
  have hmem : ∀ x : PeriodicLatticeSite L, x ∈ stepBlockOf z 1 ell ↔
      ∀ μ : Fin 3, (z μ).val ≤ (x μ).val ∧ (x μ).val < (z μ).val + ell := by
    intro x
    rw [mem_stepBlockOf]
    constructor
    · intro h μ; have := h μ; exact ⟨this.1, by simpa using this.2.1⟩
    · intro h μ; have := h μ; exact ⟨this.1, by simpa using this.2, one_dvd _⟩
  let F : (i : Fin 3) → Fin (L i + 1) → ℝ := fun i a =>
    if (z i).val ≤ a.val ∧ a.val < (z i).val + ell then
      (if i = 0 then g0 (a.val - (z i).val) else if i = 1 then g1 (a.val - (z i).val) else g2 (a.val - (z i).val)) else 0
  have hpt : ∀ x : PeriodicLatticeSite L,
      (if x ∈ stepBlockOf z 1 ell then g0 ((x 0).val - (z 0).val) * g1 ((x 1).val - (z 1).val) * g2 ((x 2).val - (z 2).val) else 0) =
      ∏ i : Fin 3, F i (x i) := by
    intro x
    rw [Fin.prod_univ_three]
    simp only [F]
    by_cases h : x ∈ stepBlockOf z 1 ell
    · have h' := (hmem x).mp h
      rw [if_pos h]
      simp [h' 0, h' 1, h' 2]
    · rw [if_neg h]
      have : ¬ (∀ μ : Fin 3, (z μ).val ≤ (x μ).val ∧ (x μ).val < (z μ).val + ell) := fun h2 => h ((hmem x).mpr h2)
      push Not at this
      obtain ⟨μ, hμ⟩ := this
      have hnot : ¬ ((z μ).val ≤ (x μ).val ∧ (x μ).val < (z μ).val + ell) := fun h3 => by
        have := hμ h3.1; omega
      fin_cases μ <;> simp_all
  have h1 : ∑ x ∈ stepBlockOf z 1 ell, g0 ((x 0).val - (z 0).val) * g1 ((x 1).val - (z 1).val) * g2 ((x 2).val - (z 2).val) =
      ∑ x : PeriodicLatticeSite L, ∏ i : Fin 3, F i (x i) := by
    rw [← Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, ← Fintype.prod_sum F, Fin.prod_univ_three]
  have e0 : ∑ a : Fin (L 0 + 1), F 0 a = ∑ n ∈ Finset.range (min ell (L 0 + 1 - (z 0).val)), g0 n := by
    have := sum_fin_window (L 0 + 1) (z 0).val ell g0
    simp only [F, if_true]
    exact this
  have e1 : ∑ a : Fin (L 1 + 1), F 1 a = ∑ n ∈ Finset.range (min ell (L 1 + 1 - (z 1).val)), g1 n := by
    have := sum_fin_window (L 1 + 1) (z 1).val ell g1
    simp only [F, if_neg (show ¬ ((1 : Fin 3) = 0) by decide), if_true]
    exact this
  have e2 : ∑ a : Fin (L 2 + 1), F 2 a = ∑ n ∈ Finset.range (min ell (L 2 + 1 - (z 2).val)), g2 n := by
    have := sum_fin_window (L 2 + 1) (z 2).val ell g2
    simp only [F, if_neg (show ¬ ((2 : Fin 3) = 0) by decide), if_neg (show ¬ ((2 : Fin 3) = 1) by decide)]
    exact this
  rw [e0, e1, e2]

/-! ## alternating sums -/

/-- `[n odd]` -/
def altN (n : ℕ) : ℝ := if n % 2 = 0 then 0 else 1
/-- `(-1)^n` -/
def pmN (n : ℕ) : ℝ := if n % 2 = 0 then 1 else -1

theorem sum_altN (m : ℕ) : ∑ n ∈ Finset.range m, (2 * altN n - 1) = -((m % 2 : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    unfold altN
    by_cases h : m % 2 = 0
    · have h2 : (m + 1) % 2 = 1 := by omega
      simp [h, h2] <;> norm_num
    · have h1 : m % 2 = 1 := by omega
      have h2 : (m + 1) % 2 = 0 := by omega
      simp [h1, h2] <;> norm_num

theorem sum_pmN (m : ℕ) : ∑ n ∈ Finset.range m, pmN n = ((m % 2 : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    unfold pmN
    by_cases h : m % 2 = 0
    · have h2 : (m + 1) % 2 = 1 := by omega
      simp [h, h2]
    · have h1 : m % 2 = 1 := by omega
      have h2 : (m + 1) % 2 = 0 := by omega
      simp [h1, h2]

/-! ## the closed form -/

/-- `E(v) = [c < v + ell ∧ v ≤ c] - ell [v = c]` -/
noncomputable def Efun (c ell v : ℕ) : ℝ := (if c < v + ell ∧ v ≤ c then 1 else 0) - (ell : ℝ) * (if v = c then 1 else 0)

noncomputable def aAmp (L : PeriodicLatticeExtent) (ell : ℕ) (z1 z2 : ℕ) : ℝ :=
  (((min ell (L 2 + 1 - z2)) * ((min ell (L 1 + 1 - z1)) / 2) : ℕ) : ℝ) / (ell : ℝ) ^ 2

noncomputable def pAmp (L : PeriodicLatticeExtent) (ell : ℕ) (z1 z2 : ℕ) : ℝ :=
  (((min ell (L 2 + 1 - z2)) * ((min ell (L 1 + 1 - z1)) % 2) : ℕ) : ℝ) / (ell : ℝ) ^ 3

noncomputable def phi1o (L : PeriodicLatticeExtent) (c ell : ℕ) (t : ℝ) : PeriodicLatticeEdge L → ℝ :=
  fld (fun z0 z1 z2 => t * sgnNat z1 * (Dfun c ell (L 0 + 1) z0 * aAmp L ell z1 z2))
      (fun z0 z1 z2 => t * sgnNat z1 * ((if z0 = c then 1 else 0) + Efun c ell z0 * pAmp L ell z1 z2))

/-! ## the closed form of `blockAngG 1 ell (stagφ c t)` -/

/-- direction 0: the same as for even `ell` (no parity input). -/
theorem blockAng_stag_dir0 (c : ℕ) (t : ℝ) (ell : ℕ) (hell : 0 < ell) (z : PeriodicLatticeSite L) :
    ((ell : ℝ) ^ 3)⁻¹ * ∑ x ∈ stepBlockOf z 1 ell, stagPhi c t 0 ell z x = Dfun c ell (L 0 + 1) (z 0).val * Ubg ell t z := by
  simp only [stagPhi, if_true]
  have hn1 : ∀ x ∈ stepBlockOf z 1 ell, ((x 1 - (Function.update z 2 (x 2)) 1).val) / 1 = ((x 1).val - (z 1).val) := by
    intro x hx
    have e1 : (Function.update z 2 (x 2)) 1 = z 1 := by simp [Function.update_of_ne]
    have h := mem_stepBlockOf.mp hx 1
    have hle : z 1 ≤ x 1 := by rw [Fin.le_def]; exact h.1
    rw [e1, Fin.coe_sub_iff_le.mpr hle, Nat.div_one]
  have h1 : ∀ x ∈ stepBlockOf z 1 ell,
      t * (∑ j ∈ Finset.range (((x 1 - (Function.update z 2 (x 2)) 1).val) / 1), sgnNat ((z 1).val + j)) *
        ((if (z 0).val = c then 1 else 0) - (if ((z 0).val + ell) % (L 0 + 1) = c then 1 else 0))
      = t * Dfun c ell (L 0 + 1) (z 0).val *
        (fun n => if n % 2 = 0 then (0 : ℝ) else sgnNat (z 1).val) (((x 1).val - (z 1).val)) := by
    intro x hx
    rw [hn1 x hx, altsum]
    simp only [Dfun]; ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, sum_block_one z ell (fun n => if n % 2 = 0 then (0 : ℝ) else sgnNat (z 1).val),
    sum_odd_even']
  unfold Ubg
  ring

/-- direction 1 (ODD `ell`): the block-sum of the stride-1 loop angles plus the straight segment, with the exact truncation counts. -/
theorem blockAng_stag_dir1 (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (c : ℕ) (t : ℝ) (z : PeriodicLatticeSite L) :
    ((ell : ℝ) ^ 3)⁻¹ * ∑ x ∈ stepBlockOf z 1 ell, stagPhiO c t 1 ell z x + pathAng c t 1 z (List.replicate ell 1) =
      t * sgnNat (z 1).val * ((if (z 0).val = c then 1 else 0) +
        ((((min ell (L 2 + 1 - (z 2).val)) * ((min ell (L 1 + 1 - (z 1).val)) % 2) : ℕ) : ℝ) / (ell : ℝ) ^ 3) *
          ((if (z 0).val ≤ c ∧ c < (z 0).val + min ell (L 0 + 1 - (z 0).val) then 1 else 0)
            - ((min ell (L 0 + 1 - (z 0).val) : ℕ) : ℝ) * (if (z 0).val = c then 1 else 0))) := by
  have hell : 0 < ell := by omega
  have hz : pathAng c t 1 z (List.replicate ell 1) = if (z 0).val = c then t * sgnNat (z 1).val else 0 := by
    rw [pathAng_rep_one hN]; simp only [one_mul]; rw [altsum]; simp [show ¬ ell % 2 = 0 by omega]
  have hterm : ∀ x ∈ stepBlockOf z 1 ell, stagPhiO c t 1 ell z x =
      t * sgnNat (z 1).val * ((if (z 0).val = c then 1 else 0) *
          ((fun _ => (1 : ℝ)) ((x 0).val - (z 0).val) * (2 * altN ((x 1).val - (z 1).val) - 1) * (fun _ => (1 : ℝ)) ((x 2).val - (z 2).val))
        + (fun m => if (z 0).val ≤ c ∧ m = c - (z 0).val then (1 : ℝ) else 0) ((x 0).val - (z 0).val) * pmN ((x 1).val - (z 1).val) *
          (fun _ => (1 : ℝ)) ((x 2).val - (z 2).val)) := by
    intro x hx
    have e1 : (Function.update z 2 (x 2)) 1 = z 1 := by simp [Function.update_of_ne]
    have h := mem_stepBlockOf.mp hx 1
    have h0 := mem_stepBlockOf.mp hx 0
    have hle : z 1 ≤ x 1 := by rw [Fin.le_def]; exact h.1
    have hn : ((x 1 - (Function.update z 2 (x 2)) 1).val) / 1 = (x 1).val - (z 1).val := by
      rw [e1, Fin.coe_sub_iff_le.mpr hle, Nat.div_one]
    have hx1 : (x 1).val = (z 1).val + ((x 1).val - (z 1).val) := by have := h.1; omega
    have hS := altsum (z 1).val ((x 1).val - (z 1).val)
    have hsg := sgnNat_add_parity (z 1).val ((x 1).val - (z 1).val)
    rw [← hx1] at hsg
    have hx0 : ((x 0).val = c) ↔ ((z 0).val ≤ c ∧ (x 0).val - (z 0).val = c - (z 0).val) := by
      have := h0.1; constructor
      · intro hh; refine ⟨by omega, by omega⟩
      · rintro ⟨h1, h2⟩; omega
    simp only [stagPhiO, if_true, hn, hS, hsg, altN, pmN, ← hx0]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_block_gen z ell (fun _ => (1 : ℝ)) (fun n => 2 * altN n - 1) (fun _ => (1 : ℝ)),
    sum_block_gen z ell (fun m => if (z 0).val ≤ c ∧ m = c - (z 0).val then (1 : ℝ) else 0) pmN (fun _ => (1 : ℝ))]
  rw [hz]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, sum_altN, sum_pmN]
  have hsum0 : ∑ n ∈ Finset.range (min ell (L 0 + 1 - (z 0).val)), (if (z 0).val ≤ c ∧ n = c - (z 0).val then (1 : ℝ) else 0)
      = if (z 0).val ≤ c ∧ c < (z 0).val + min ell (L 0 + 1 - (z 0).val) then 1 else 0 := by
    by_cases hc : (z 0).val ≤ c
    · simp only [hc, true_and]
      rw [Finset.sum_ite_eq' (Finset.range (min ell (L 0 + 1 - (z 0).val))) (c - (z 0).val) (fun _ => (1 : ℝ))]
      by_cases hlt : c - (z 0).val < min ell (L 0 + 1 - (z 0).val)
      · rw [if_pos (Finset.mem_range.mpr hlt), if_pos (by omega)]
      · rw [if_neg (by simpa using hlt), if_neg (by omega)]
    · simp [hc]
  rw [hsum0]
  have hell' : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  push_cast
  by_cases hc0 : (z 0).val = c
  · simp only [hc0, if_true, true_and]
    field_simp
    ring
  · simp only [hc0, if_false]
    field_simp
    ring

theorem dfun_ne_zero_le {c ell N0 z0 : ℕ} (hc1 : ell ≤ c) (hc2 : c + ell ≤ N0) (hz : z0 < N0)
    (hD : Dfun c ell N0 z0 ≠ 0) : z0 ≤ c := by
  unfold Dfun at hD
  by_cases h1 : z0 = c
  · omega
  · have h2 : (z0 + ell) % N0 = c := by
      by_contra h2
      apply hD
      rw [if_neg h1, if_neg h2]; norm_num
    by_cases h3 : z0 + ell < N0
    · rw [Nat.mod_eq_of_lt h3] at h2; omega
    · push Not at h3
      have h4 : (z0 + ell) % N0 = (z0 + ell - N0) % N0 := Nat.mod_eq_sub_mod h3
      rw [h4, Nat.mod_eq_of_lt (by omega)] at h2
      omega

/-- **the first blocked level of the staggered layer for ODD `ell`, at every base**. -/
theorem blockAng_stag_odd (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (c : ℕ) (t : ℝ) (hc1 : ell ≤ c) (hc2 : c + ell ≤ L 0 + 1)
    (z : PeriodicLatticeSite L) (μ : Fin 3) :
    blockAngG 1 ell (stagφ c t) z μ = phi1o L c ell t (z, μ) := by
  have hell : 0 < ell := by omega
  have hell' : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  unfold blockAngG
  simp only [loopAngG_stagφ_odd hN hO, pathAngG_stagφ]
  have key : μ = 0 ∨ μ = 1 ∨ μ = 2 := by fin_cases μ <;> simp
  rcases key with rfl | rfl | rfl
  · simp only [stagPhiO, if_neg (show ¬ ((0 : Fin 3) = 1) by decide)]
    rw [blockAng_stag_dir0 c t ell hell z, pathAng_rep_ne c t 1 0 (by decide), add_zero]
    unfold phi1o fld
    simp only [if_true]
    by_cases hD : Dfun c ell (L 0 + 1) (z 0).val = 0
    · rw [hD]; ring
    · have hle := dfun_ne_zero_le hc1 hc2 (z 0).isLt hD
      have hcnt : min ell (L 0 + 1 - (z 0).val) = ell := by omega
      unfold Ubg aAmp
      rw [hcnt]
      push_cast
      field_simp
  · have := blockAng_stag_dir1 hN hO c t z
    rw [this]
    unfold phi1o fld Efun pAmp
    simp only [if_neg (show ¬ ((1 : Fin 3) = 0) by decide), if_true]
    by_cases hz0 : (z 0).val ≤ c
    · have hcnt : min ell (L 0 + 1 - (z 0).val) = ell := by omega
      rw [hcnt]
      have hiff : ((z 0).val ≤ c ∧ c < (z 0).val + ell) ↔ (c < (z 0).val + ell ∧ (z 0).val ≤ c) := and_comm
      simp only [hiff]
      ring
    · have hne : ¬ (z 0).val = c := by omega
      simp [hz0, hne]
  · simp only [stagPhiO, if_neg (show ¬ ((2 : Fin 3) = 1) by decide), stagPhi, if_neg (show ¬ ((2 : Fin 3) = 0) by decide)]
    rw [pathAng_rep_ne c t 1 2 (by decide)]
    unfold phi1o fld
    simp

end AdalyFormal.CoverOmega
