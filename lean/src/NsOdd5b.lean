import NsOdd4
import NsOdd5a

/-!
# NsOdd5b -- amplitude facts for `phi1o`, telescoping of `Dfun`, alternating sums of `pAmp` along stride-`ell` progressions (lane ncwdh_strong_20261017)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

/-- `phi1o` is the shape field with `D = Dfun`, `T = [· = c]`, `Ef = Efun`, `a = aAmp`, `p = pAmp`. -/
theorem phi1o_eq_shape (c ell : ℕ) (t : ℝ) :
    (phi1o L c ell t : PeriodicLatticeEdge L → ℝ) =
      shapeFld t (fun v => Dfun c ell (L 0 + 1) v) (fun v => if v = c then 1 else 0) (Efun c ell) (aAmp L ell) (pAmp L ell) := rfl

/-! ## telescoping -/

theorem Dsum_tel (c ell N0 : ℕ) (v n : ℕ) (hN0 : 0 < N0) :
    ∑ i ∈ Finset.range n, Dfun c ell N0 ((v + ell * i) % N0) =
      (if v % N0 = c then (1 : ℝ) else 0) - (if (v + ell * n) % N0 = c then (1 : ℝ) else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold Dfun
    have : ((v + ell * n) % N0 + ell) % N0 = (v + ell * (n + 1)) % N0 := by
      rw [Nat.mod_add_mod]; congr 1; ring
    rw [this]
    ring

/-! ## amplitudes -/

noncomputable def mAmp (L : PeriodicLatticeExtent) (ell v : ℕ) : ℝ := (((min ell (L 1 + 1 - v)) % 2 : ℕ) : ℝ)
noncomputable def uAmp (L : PeriodicLatticeExtent) (ell z2 : ℕ) : ℝ := ((min ell (L 2 + 1 - z2) : ℕ) : ℝ) / (ell : ℝ) ^ 3

theorem pAmp_eq (ell z1 z2 : ℕ) : pAmp L ell z1 z2 = uAmp L ell z2 * mAmp L ell z1 := by
  unfold pAmp uAmp mAmp
  push_cast
  ring

theorem mAmp_nonneg (ell v : ℕ) : 0 ≤ mAmp L ell v := Nat.cast_nonneg _

theorem mAmp_le_one (ell v : ℕ) : mAmp L ell v ≤ 1 := by
  unfold mAmp
  have : (min ell (L 1 + 1 - v)) % 2 ≤ 1 := by omega
  exact_mod_cast this

theorem mAmp_eq_one {ell v : ℕ} (hO : ell % 2 = 1) (hv : v + ell ≤ L 1 + 1) : mAmp L ell v = 1 := by
  unfold mAmp
  have : min ell (L 1 + 1 - v) = ell := by omega
  rw [this, hO]; norm_num

theorem uAmp_nonneg (ell z2 : ℕ) : 0 ≤ uAmp L ell z2 := by
  unfold uAmp; positivity

theorem uAmp_le {ell : ℕ} (hell : 0 < ell) (z2 : ℕ) : uAmp L ell z2 ≤ 1 / (ell : ℝ) ^ 2 := by
  unfold uAmp
  have hl : (0 : ℝ) < ell := by exact_mod_cast hell
  have h1 : ((min ell (L 2 + 1 - z2) : ℕ) : ℝ) ≤ ell := by exact_mod_cast Nat.min_le_left _ _
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (ell : ℝ), mul_pos hl hl]

theorem aAmp_nonneg (ell z1 z2 : ℕ) : 0 ≤ aAmp L ell z1 z2 := by
  unfold aAmp; positivity

theorem aAmp_le {ell : ℕ} (hO : ell % 2 = 1) (hell : 0 < ell) (z1 z2 : ℕ) : aAmp L ell z1 z2 ≤ ((ell : ℝ) - 1) / (2 * ell) := by
  unfold aAmp
  have hl : (0 : ℝ) < ell := by exact_mod_cast hell
  have h2 : (min ell (L 2 + 1 - z2)) ≤ ell := Nat.min_le_left _ _
  have h1 : (min ell (L 1 + 1 - z1)) / 2 ≤ (ell - 1) / 2 := by
    have : min ell (L 1 + 1 - z1) ≤ ell := Nat.min_le_left _ _
    omega
  have h3 : (min ell (L 2 + 1 - z2)) * ((min ell (L 1 + 1 - z1)) / 2) ≤ ell * ((ell - 1) / 2) := Nat.mul_le_mul h2 h1
  have h4 : (2 : ℕ) * ((ell - 1) / 2) = ell - 1 := by omega
  have h5 : (((min ell (L 2 + 1 - z2)) * ((min ell (L 1 + 1 - z1)) / 2) : ℕ) : ℝ) ≤ (ell : ℝ) * (((ell - 1 : ℕ) : ℝ) / 2) := by
    have h6 : ((((min ell (L 2 + 1 - z2)) * ((min ell (L 1 + 1 - z1)) / 2) : ℕ)) : ℝ) ≤ ((ell * ((ell - 1) / 2) : ℕ) : ℝ) := by exact_mod_cast h3
    have h7 : (((ell - 1) / 2 : ℕ) : ℝ) = ((ell - 1 : ℕ) : ℝ) / 2 := by
      have : (2 : ℝ) * (((ell - 1) / 2 : ℕ) : ℝ) = ((ell - 1 : ℕ) : ℝ) := by exact_mod_cast h4
      linarith
    push_cast at h6 ⊢
    rw [h7] at h6
    linarith
  have h8 : ((ell - 1 : ℕ) : ℝ) = (ell : ℝ) - 1 := by
    have : 1 ≤ ell := hell
    push_cast [Nat.cast_sub this]; ring
  rw [h8] at h5
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h5, hl]

theorem Efun_abs_le {c ell : ℕ} (hell : 2 ≤ ell) (v : ℕ) : |Efun c ell v| ≤ (ell : ℝ) - 1 := by
  unfold Efun
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  by_cases h1 : v = c
  · subst h1
    rw [if_pos ⟨by omega, le_refl _⟩, if_pos rfl]
    rw [abs_le]; constructor <;> linarith
  · rw [if_neg h1]
    split_ifs
    · simp; linarith
    · simp; linarith

theorem Efun_ne_zero {c ell v : ℕ} (hell : 0 < ell) (h : Efun c ell v ≠ 0) : v ≤ c ∧ c < v + ell := by
  unfold Efun at h
  by_contra hc
  apply h
  by_cases h1 : v = c
  · subst h1; exfalso; apply hc; omega
  · rw [if_neg h1, if_neg (by tauto)]; ring

/-! ## alternating sums of `pAmp` along stride-`ell` progressions -/

theorem altP_bound {ell : ℕ} (hO : ell % 2 = 1) (hell : 0 < ell) (hN : ell * ell + ell < L 1 + 1) (b n z2 : ℕ) (hn : n ≤ ell) :
    |∑ j ∈ Finset.range n, pmN j * pAmp L ell ((b + ell * j) % (L 1 + 1)) z2| ≤ 2 / (ell : ℝ) ^ 2 := by
  have hl : (0 : ℝ) < ell := by exact_mod_cast hell
  have hform : ∑ j ∈ Finset.range n, pmN j * pAmp L ell ((b + ell * j) % (L 1 + 1)) z2 =
      uAmp L ell z2 * ∑ j ∈ Finset.range n, pmN j * mAmp L ell ((b + ell * j) % (L 1 + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pAmp_eq]; ring
  have hone : ∀ j j', j < n → j' < n → mAmp L ell ((b + ell * j) % (L 1 + 1)) < 1 → mAmp L ell ((b + ell * j') % (L 1 + 1)) < 1 → j = j' := by
    intro j j' hj hj' h1 h2
    have c1 : L 1 + 1 - ell < (b + ell * j) % (L 1 + 1) := by
      by_contra hc
      push Not at hc
      have := mAmp_eq_one (L := L) hO (v := (b + ell * j) % (L 1 + 1)) (by omega)
      linarith
    have c2 : L 1 + 1 - ell < (b + ell * j') % (L 1 + 1) := by
      by_contra hc
      push Not at hc
      have := mAmp_eq_one (L := L) hO (v := (b + ell * j') % (L 1 + 1)) (by omega)
      linarith
    exact seam_once (L 1 + 1) ell b hell hN n hn j j' hj hj' c1 c2
  have hs := alt_sum_one_dev n (fun j => mAmp L ell ((b + ell * j) % (L 1 + 1))) (fun j => mAmp_nonneg ell _) (fun j => mAmp_le_one ell _) hone
  rw [hform, abs_mul, abs_of_nonneg (uAmp_nonneg ell z2)]
  calc uAmp L ell z2 * |∑ j ∈ Finset.range n, pmN j * mAmp L ell ((b + ell * j) % (L 1 + 1))|
      ≤ (1 / (ell : ℝ) ^ 2) * 2 := by
        apply mul_le_mul (uAmp_le hell z2) hs (abs_nonneg _) (by positivity)
    _ = 2 / (ell : ℝ) ^ 2 := by ring

end AdalyFormal.CoverOmega
