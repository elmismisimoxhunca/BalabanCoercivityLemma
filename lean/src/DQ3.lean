import DQ2
import ZR8DataA

/-!
# DQ3 -- the level-`n` cut-off of the M1 field and the geometry of level-`n` rows (sub-builder DQ, 2026-10-13)

* `distOm S n x` = `ℓ¹`-distance from `x` to `Ω_n` (`sInf`); 1-Lipschitz along every shift when `Ω_n ≠ ∅`.
* `chiN S n r0 w` = `clamp(1 − (distOm − r0)/w)` if `Ω_n ≠ ∅`, else `0`: values in `[0,1]`, `1/w`-Lipschitz, `= 1` where
  `distOm ≤ r0`, and `≠ 0` only within `distOm < r0 + w`.
* Admissible-tower geometry (collar, clause 5): a site within `R M ℓ^{n-1}` of `Ω_n` lies in `Ω_{n-1}` (`mem_prev`); a site within
  `R M ℓ^{n+1}` of a point of `Ω_n \ Ω_{n+1}` has stratum `≤ n+1` (`strat_le_of_near`); every level-`n` row of `geomOf` has an
  anchor `y ∈ Ω_n \ Ω_{n+1}` within `ℓⁿ` of its base (`row_anchor`) and an `ℓⁿ`-aligned base (`row_base_aligned`).
* `goodN` : with `r0 = 2ρ_T(n) + ℓⁿ`, `w = ℓ^{n-1}`, `18ℓ ≤ RM`: where `chiN ≠ 0`, every bond based within distance `1` has
  `bstrat ≥ n−1`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1DStrat.DQ

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (pdist bigSide Admissible Tower scaleUp)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_shift_le pdist_self pdist_coarseShift_le rhoT
  rhoT_le)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.IngredientFamilyR2 (bondsLam geomOf)
open AdalyFormal.M1 (strat bstrat strat_le om_anti le_strat_of_mem mem_of_le_strat strat_close collar le_bstrat_of_mem)

variable {L : PeriodicLatticeExtent}

/-! ## 1. distance to `Ω_n` -/

/-- `ℓ¹`-distance to `Ω_n` (`0` if `Ω_n = ∅`). -/
noncomputable def distOm (S : Tower L) (n : ℕ) (x : PeriodicLatticeSite L) : ℕ :=
  sInf {d : ℕ | ∃ y ∈ S.Om n, pdist x y ≤ d}

theorem distOm_le {S : Tower L} {n : ℕ} {x y : PeriodicLatticeSite L} (hy : y ∈ S.Om n) :
    distOm S n x ≤ pdist x y :=
  Nat.sInf_le ⟨y, hy, le_rfl⟩

theorem distOm_spec {S : Tower L} {n : ℕ} (x : PeriodicLatticeSite L) {y0 : PeriodicLatticeSite L} (hy0 : y0 ∈ S.Om n) :
    ∃ y ∈ S.Om n, pdist x y ≤ distOm S n x :=
  Nat.sInf_mem (s := {d : ℕ | ∃ y ∈ S.Om n, pdist x y ≤ d}) ⟨_, y0, hy0, le_rfl⟩

theorem distOm_shift_le {S : Tower L} {n : ℕ} {y0 : PeriodicLatticeSite L} (hy0 : y0 ∈ S.Om n)
    (x : PeriodicLatticeSite L) (μ : Fin 3) : distOm S n (periodicLatticeShift x μ) ≤ distOm S n x + 1 := by
  obtain ⟨y, hy, hd⟩ := distOm_spec x hy0
  have h1 := pdist_shift_le x μ
  rw [pdist_comm] at h1
  have h2 := pdist_triangle (periodicLatticeShift x μ) x y
  have h3 := distOm_le (x := periodicLatticeShift x μ) hy
  omega

theorem distOm_le_shift {S : Tower L} {n : ℕ} {y0 : PeriodicLatticeSite L} (hy0 : y0 ∈ S.Om n)
    (x : PeriodicLatticeSite L) (μ : Fin 3) : distOm S n x ≤ distOm S n (periodicLatticeShift x μ) + 1 := by
  obtain ⟨y, hy, hd⟩ := distOm_spec (periodicLatticeShift x μ) hy0
  have h1 := pdist_shift_le x μ
  have h2 := pdist_triangle x (periodicLatticeShift x μ) y
  have h3 := distOm_le (x := x) hy
  omega

/-! ## 2. the cut-off -/

theorem clamp_lip (a b : ℝ) : |min 1 (max 0 a) - min 1 (max 0 b)| ≤ |a - b| := by
  have h1 := le_abs_self (a - b)
  have h2 := neg_abs_le (a - b)
  rw [abs_le]
  constructor <;> simp only [min_def, max_def] <;> split_ifs <;> linarith

/-- the clamped cut-off profile -/
noncomputable def chiC (S : Tower L) (n : ℕ) (r0 w : ℝ) (x : PeriodicLatticeSite L) : ℝ :=
  min 1 (max 0 (1 - ((distOm S n x : ℝ) - r0) / w))

open Classical in
/-- the level-`n` cut-off (`0` if `Ω_n = ∅`) -/
noncomputable def chiN (S : Tower L) (n : ℕ) (r0 w : ℝ) (x : PeriodicLatticeSite L) : ℝ :=
  if ∃ y, y ∈ S.Om n then chiC S n r0 w x else 0

theorem chiC_nonneg (S : Tower L) (n : ℕ) (r0 w : ℝ) (x : PeriodicLatticeSite L) : 0 ≤ chiC S n r0 w x :=
  le_min zero_le_one (le_max_left _ _)

theorem chiC_le_one (S : Tower L) (n : ℕ) (r0 w : ℝ) (x : PeriodicLatticeSite L) : chiC S n r0 w x ≤ 1 :=
  min_le_left _ _

theorem chiN_nonneg (S : Tower L) (n : ℕ) (r0 w : ℝ) (x : PeriodicLatticeSite L) : 0 ≤ chiN S n r0 w x := by
  unfold chiN; split_ifs
  · exact chiC_nonneg S n r0 w x
  · exact le_rfl

theorem chiN_le_one (S : Tower L) (n : ℕ) (r0 w : ℝ) (x : PeriodicLatticeSite L) : chiN S n r0 w x ≤ 1 := by
  unfold chiN; split_ifs
  · exact chiC_le_one S n r0 w x
  · exact zero_le_one

theorem chiN_lip (S : Tower L) (n : ℕ) (r0 w : ℝ) (hw : 0 < w) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    |chiN S n r0 w (periodicLatticeShift x μ) - chiN S n r0 w x| ≤ 1 / w := by
  unfold chiN
  split_ifs with hne
  · obtain ⟨y0, hy0⟩ := hne
    unfold chiC
    refine (clamp_lip _ _).trans ?_
    have h1 := distOm_shift_le hy0 x μ
    have h2 := distOm_le_shift hy0 x μ
    have h1' : (distOm S n (periodicLatticeShift x μ) : ℝ) ≤ distOm S n x + 1 := by exact_mod_cast h1
    have h2' : (distOm S n x : ℝ) ≤ distOm S n (periodicLatticeShift x μ) + 1 := by exact_mod_cast h2
    have e : 1 - ((distOm S n (periodicLatticeShift x μ) : ℝ) - r0) / w - (1 - ((distOm S n x : ℝ) - r0) / w)
        = ((distOm S n x : ℝ) - distOm S n (periodicLatticeShift x μ)) / w := by field_simp; ring
    rw [e, abs_div, abs_of_pos hw]
    exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) hw.le
  · rw [sub_self, abs_zero]; positivity

theorem chiN_eq_one (S : Tower L) (n : ℕ) (r0 w : ℝ) (hw : 0 < w) {x y : PeriodicLatticeSite L} (hy : y ∈ S.Om n)
    (hd : (pdist x y : ℝ) ≤ r0) : chiN S n r0 w x = 1 := by
  unfold chiN
  rw [if_pos ⟨y, hy⟩]
  unfold chiC
  have h1 : (distOm S n x : ℝ) ≤ r0 := le_trans (by exact_mod_cast distOm_le hy) hd
  have h2 : 1 ≤ 1 - ((distOm S n x : ℝ) - r0) / w := by
    have : ((distOm S n x : ℝ) - r0) / w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le
    linarith
  rw [max_eq_right (by linarith), min_eq_left h2]

theorem chiN_ne_zero (S : Tower L) (n : ℕ) (r0 w : ℝ) (hw : 0 < w) {x : PeriodicLatticeSite L}
    (h : chiN S n r0 w x ≠ 0) : ∃ y ∈ S.Om n, (pdist x y : ℝ) < r0 + w := by
  unfold chiN at h
  split_ifs at h with hne
  · obtain ⟨y0, hy0⟩ := hne
    obtain ⟨y, hy, hd⟩ := distOm_spec x hy0
    refine ⟨y, hy, ?_⟩
    have hd' : (pdist x y : ℝ) ≤ distOm S n x := by exact_mod_cast hd
    by_contra hge
    push Not at hge
    apply h
    unfold chiC
    have : 1 - ((distOm S n x : ℝ) - r0) / w ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hw]; linarith
    rw [max_eq_left this, min_eq_right zero_le_one]
  · exact absurd rfl h

/-! ## 3. geometry of an admissible tower -/

variable {ell M R k : ℕ} {S : Tower L}

/-- within `R M ℓ^{n-1}` of `Ω_n` one is in `Ω_{n-1}` (collar) -/
theorem mem_prev (hA : Admissible ell M R k S) {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k)
    {y z : PeriodicLatticeSite L} (hy : y ∈ S.Om n) (hd : pdist z y ≤ R * M * ell ^ (n - 1)) : z ∈ S.Om (n - 1) := by
  by_contra hz
  have h := collar hA (j := n - 1) (by omega) hz (by rw [show n - 1 + 1 = n by omega]; exact hy)
  unfold bigSide at h
  rw [← Nat.mul_assoc] at h
  omega

/-- a bond with both endpoints within `R M ℓ^{n-1}` of `Ω_n` has `bstrat ≥ n − 1` -/
theorem bstrat_ge_prev (hA : Admissible ell M R k S) {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k)
    {y : PeriodicLatticeSite L} (hy : y ∈ S.Om n) (e : Bond L) (h1 : pdist e.1 y ≤ R * M * ell ^ (n - 1))
    (h2 : pdist (periodicLatticeShift e.1 e.2) y ≤ R * M * ell ^ (n - 1)) : n - 1 ≤ bstrat S k e := by
  rcases Nat.eq_zero_or_pos (n - 1) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · exact le_bstrat_of_mem (by omega) e (mem_prev hA hn1 hnk hy h1) (mem_prev hA hn1 hnk hy h2)

/-- within `R M ℓ^{n+1}` of a point of `Ω_n \ Ω_{n+1}` the stratum is `≤ n + 1` -/
theorem strat_le_of_near (hA : Admissible ell M R k S) {n : ℕ} (hnk : n ≤ k) {y z : PeriodicLatticeSite L}
    (hy : y ∈ S.Om n) (hy' : y ∉ S.Om (n + 1)) (hd : pdist y z ≤ R * (M * ell ^ (n + 1))) : strat S k z ≤ n + 1 := by
  have hy0 : y ∈ S.Om 0 := om_anti hA (Nat.zero_le n) hy
  have hs : strat S k y = n := by
    refine le_antisymm ?_ (le_strat_of_mem hnk hy)
    by_contra h
    push Not at h
    exact hy' (mem_of_le_strat hA hy0 (show n + 1 ≤ strat S k y by omega))
  have := strat_close hA (x := y) (y := z) (by rw [hs]; unfold bigSide; exact hd)
  omega

/-- every level-`n` row has an anchor in `Ω_n \ Ω_{n+1}` within `ℓⁿ` of its base -/
theorem row_anchor (ell k : ℕ) (S : Tower L) {n : ℕ} {b : Bond L} (hb : b ∈ bondsLam (geomOf ell k S) n) :
    ∃ y : PeriodicLatticeSite L, y ∈ S.Om n ∧ y ∉ S.Om (n + 1) ∧ pdist b.1 y ≤ ell ^ n ∧ (∀ μ, ell ^ n ∣ (y μ).val) := by
  rcases hb.1 with h | h
  · exact ⟨b.1, h.2.1, h.2.2, by rw [pdist_self]; exact Nat.zero_le _, h.1⟩
  · exact ⟨_, h.2.1, h.2.2, pdist_coarseShift_le b.1 (ell ^ n) b.2, h.1⟩

/-- the base of a level-`n` row is `ℓⁿ`-aligned -/
theorem row_base_aligned (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    {n : ℕ} (hnk : n ≤ k) {b : Bond (scaleUp ell k Lu)} (hb : b ∈ bondsLam (geomOf ell k S) n) :
    b.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ n) := by
  rw [mem_CoarseLattice]
  intro ν
  rcases hb.1 with h | h
  · exact Nat.mod_eq_zero_of_dvd (h.1 ν)
  · have hz := h.1 ν
    by_cases hν : ν = b.2
    · rw [hν] at hz ⊢
      have hz' : ell ^ n ∣ ((coarseShift b.1 (ell ^ n) b.2) b.2).val := hz
      rw [coarseShift_val_eq] at hz'
      have hN : ell ^ n ∣ scaleUp ell k Lu b.2 + 1 := AdalyFormal.BondComposite.hdvd_scaleUp ell k Lu hell n hnk b.2
      have h1 := (Nat.dvd_mod_iff hN).mp hz'
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add_self_right.mp h1)
    · have hz' : ell ^ n ∣ ((coarseShift b.1 (ell ^ n) b.2) ν).val := hz
      rw [coarseShift_apply_ne b.1 (ell ^ n) b.2 ν hν] at hz'
      exact Nat.mod_eq_zero_of_dvd hz'

/-- the room arithmetic: `2 + 2ρ_T(n) + ℓⁿ + ℓ^{n-1} ≤ R M ℓ^{n-1}` when `18ℓ ≤ RM` -/
theorem room_prev (hell : 2 ≤ ell) (hroom : 18 * ell ≤ R * M) {n : ℕ} (hn1 : 1 ≤ n) :
    2 + 2 * rhoT ell n + ell ^ n + ell ^ (n - 1) ≤ R * M * ell ^ (n - 1) := by
  have hT := rhoT_le ell hell n
  have hp : ell ^ n = ell ^ (n - 1) * ell := by rw [← pow_succ]; congr 1; omega
  have hq : ell ^ (n - 1) ≤ ell ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  have h18 : 18 * ell ^ n ≤ R * M * ell ^ (n - 1) := by
    rw [hp]
    have := Nat.mul_le_mul_right (ell ^ (n - 1)) hroom
    nlinarith
  omega

/-- the room arithmetic upward: `ℓⁿ + ρ_T(n) ≤ R M ℓ^{n+1}` -/
theorem room_next (hell : 2 ≤ ell) (hroom : 18 * ell ≤ R * M) (n : ℕ) :
    ell ^ n + rhoT ell n ≤ R * (M * ell ^ (n + 1)) := by
  have hT := rhoT_le ell hell n
  have h1 : 18 * ell ^ (n + 1) ≤ R * M * ell ^ (n + 1) := Nat.mul_le_mul_right _ (le_trans (by omega) hroom)
  have h2 : ell ^ n ≤ ell ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [← Nat.mul_assoc]
  omega

/-- **where the level-`n` cut-off is nonzero, every bond based within distance `1` has `bstrat ≥ n − 1`** -/
theorem goodN (hA : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 18 * ell ≤ R * M) {n : ℕ} (hn1 : 1 ≤ n)
    (hnk : n ≤ k) {x : PeriodicLatticeSite L}
    (hx : chiN S n ((2 * rhoT ell n + ell ^ n : ℕ) : ℝ) ((ell : ℝ) ^ (n - 1)) x ≠ 0)
    (e : Bond L) (he : pdist x e.1 ≤ 1) : n - 1 ≤ bstrat S k e := by
  have hw : (0 : ℝ) < (ell : ℝ) ^ (n - 1) := by positivity
  obtain ⟨y, hy, hd⟩ := chiN_ne_zero S n _ _ hw hx
  have hd' : pdist x y < 2 * rhoT ell n + ell ^ n + ell ^ (n - 1) := by
    have : (pdist x y : ℝ) < ((2 * rhoT ell n + ell ^ n + ell ^ (n - 1) : ℕ) : ℝ) := by push_cast at hd ⊢; linarith
    exact_mod_cast this
  have hR := room_prev hell hroom hn1 (n := n)
  have hR' : 2 + 2 * rhoT ell n + ell ^ n + ell ^ (n - 1) ≤ R * M * ell ^ (n - 1) := hR
  have h1 : pdist e.1 y ≤ R * M * ell ^ (n - 1) := by
    have := pdist_triangle e.1 x y
    rw [pdist_comm e.1 x] at this
    omega
  have h2 : pdist (periodicLatticeShift e.1 e.2) y ≤ R * M * ell ^ (n - 1) := by
    have := pdist_triangle (periodicLatticeShift e.1 e.2) e.1 y
    have h3 := pdist_shift_le e.1 e.2
    rw [pdist_comm] at h3
    have := pdist_triangle e.1 x y
    rw [pdist_comm e.1 x] at this
    omega
  exact bstrat_ge_prev hA hn1 hnk hy e h1 h2

#print axioms distOm
#print axioms chiC
#print axioms chiN
#print axioms distOm_le
#print axioms distOm_spec
#print axioms distOm_shift_le
#print axioms distOm_le_shift
#print axioms clamp_lip
#print axioms chiC_nonneg
#print axioms chiC_le_one
#print axioms chiN_nonneg
#print axioms chiN_le_one
#print axioms chiN_lip
#print axioms chiN_eq_one
#print axioms chiN_ne_zero
#print axioms mem_prev
#print axioms bstrat_ge_prev
#print axioms strat_le_of_near
#print axioms row_anchor
#print axioms row_base_aligned
#print axioms room_prev
#print axioms room_next
#print axioms goodN

end AdalyFormal.M1DStrat.DQ
