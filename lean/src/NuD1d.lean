import NuD1c
import NsCvO15

/-!
# NuD1d -- the tower of the direction-0 staggered family: `bg1` in the class, temporal at coarse sites, `RegTower2`, unit-level `RegBg2` (lane ncwdh_ell2_20261018)

Hypotheses (all hold for the nested instance at `ell = 2`, `xs = neC0 2 M R`): `ell` even, `2 ∣ N₁`, `ell ≤ xs`, `xs + ell ≤ N₀`, `ell² ≤ N₀`, `|t| < π/2`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2 (unitBg embY embY_val)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq UbarTower UbarTower_succ UbarTower_zero)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

section
variable [CfData]
variable {L : PeriodicLatticeExtent}

/-- the transverse profile of the first blocked level (the `x₀`-count frozen at `ell`). -/
noncomputable def u1s (ell : ℕ) (t : ℝ) (a1 a2 : ℕ) : ℝ :=
  (sgnNat a1 * t) *
    (1 - 2 * (((ell : ℝ) * ((min ell (L 2 + 1 - a2) : ℕ) : ℝ) * (((min ell (L 1 + 1 - a1)) / 2 : ℕ) : ℝ))) / (ell : ℝ) ^ 3)

theorem Sw0_ne_zero_cnt0 {ell xs v : ℕ} (hxs1 : ell ≤ xs) (hxs2 : xs + ell ≤ L 0 + 1) (hv : v < L 0 + 1)
    (h : Sw0 xs ell (L 0 + 1) v ≠ 0) : min ell (L 0 + 1 - v) = ell := by
  unfold Sw0 at h
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hi' := Finset.mem_range.mp hi
  have hx : (v + i) % (L 0 + 1) = xs := by
    by_contra hh; apply hne; unfold D0; rw [if_neg hh]
  rcases Nat.lt_or_ge (v + i) (L 0 + 1) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hx; omega
  · have : (v + i) % (L 0 + 1) = v + i - (L 0 + 1) := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    omega

theorem u1s_abs_le {ell : ℕ} (hell : 0 < ell) (t : ℝ) (a1 a2 : ℕ) : |u1s (L := L) ell t a1 a2| ≤ |t| := by
  unfold u1s
  have hl : (0 : ℝ) < ell := by exact_mod_cast hell
  have h2 : (((min ell (L 2 + 1 - a2) : ℕ)) : ℝ) ≤ ell := by exact_mod_cast min_le_left _ _
  have h1 : ((((min ell (L 1 + 1 - a1)) / 2 : ℕ)) : ℝ) ≤ (ell : ℝ) / 2 := by
    have : (min ell (L 1 + 1 - a1)) / 2 ≤ ell / 2 := Nat.div_le_div_right (min_le_left _ _)
    calc ((((min ell (L 1 + 1 - a1)) / 2 : ℕ)) : ℝ) ≤ ((ell / 2 : ℕ) : ℝ) := by exact_mod_cast this
      _ ≤ (ell : ℝ) / 2 := Nat.cast_div_le
  have hc2 : (0 : ℝ) ≤ (((min ell (L 2 + 1 - a2) : ℕ)) : ℝ) := Nat.cast_nonneg _
  have hc1 : (0 : ℝ) ≤ ((((min ell (L 1 + 1 - a1)) / 2 : ℕ)) : ℝ) := Nat.cast_nonneg _
  have hf : 0 ≤ 2 * (((ell : ℝ) * ((min ell (L 2 + 1 - a2) : ℕ) : ℝ) * (((min ell (L 1 + 1 - a1)) / 2 : ℕ) : ℝ))) / (ell : ℝ) ^ 3 := by
    positivity
  have hf1 : 2 * (((ell : ℝ) * ((min ell (L 2 + 1 - a2) : ℕ) : ℝ) * (((min ell (L 1 + 1 - a1)) / 2 : ℕ) : ℝ))) / (ell : ℝ) ^ 3 ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (ell : ℝ) * ((min ell (L 2 + 1 - a2) : ℕ) : ℝ) * (((min ell (L 1 + 1 - a1)) / 2 : ℕ) : ℝ) ≤ (ell : ℝ) * ell * ((ell : ℝ) / 2) := by
      gcongr
    nlinarith
  have hs := sgnNat_abs_le a1
  rw [abs_mul, abs_mul]
  have habs : |1 - 2 * (((ell : ℝ) * ((min ell (L 2 + 1 - a2) : ℕ) : ℝ) * (((min ell (L 1 + 1 - a1)) / 2 : ℕ) : ℝ))) / (ell : ℝ) ^ 3| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  calc |sgnNat a1| * |t| * |1 - 2 * (((ell : ℝ) * ((min ell (L 2 + 1 - a2) : ℕ) : ℝ) * (((min ell (L 1 + 1 - a1)) / 2 : ℕ) : ℝ))) / (ell : ℝ) ^ 3|
      ≤ 1 * |t| * 1 := by gcongr
    _ = |t| := by ring

theorem bg1_isUTemp_stag0 {ell : ℕ} (hell : 0 < ell) (hN0 : ell ≤ L 0 + 1) (hN : 2 ∣ L 1 + 1) (hE : 2 ∣ ell)
    {xs : ℕ} (hxs1 : ell ≤ xs) (hxs2 : xs + ell ≤ L 0 + 1) (t : ℝ) (ht : |t| < Real.pi / 2) :
    IsUTemp (Sw0 xs ell (L 0 + 1)) (u1s (L := L) ell t)
      (stridedBlockedGauge su2LogExp 1 ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) := by
  intro z
  refine ⟨?_, ?_, ?_⟩
  · rw [bg1_stag0_all hell hN0 hN hE xs t ht z 0, if_pos rfl]
    congr 1
    by_cases hD : Sw0 xs ell (L 0 + 1) (z 0).val = 0
    · rw [hD, zero_mul, zero_mul]
    · congr 1
      unfold Ubg0 u1s
      rw [Sw0_ne_zero_cnt0 hxs1 hxs2 (z 0).isLt hD]
  · rw [bg1_stag0_all hell hN0 hN hE xs t ht z 1, if_neg (by decide)]; exact cartan_zero
  · rw [bg1_stag0_all hell hN0 hN hE xs t ht z 2, if_neg (by decide)]; exact cartan_zero

theorem hSw0_windows {ell : ℕ} (xs : ℕ) (hNN : ell * ell ≤ L 0 + 1) :
    ∀ (a m : ℕ), m ≤ ell → |∑ j ∈ Finset.range m, Sw0 xs ell (L 0 + 1) ((a + ell * j) % (L 0 + 1))| ≤ 1 := by
  intro a m hm
  have := sum_Sw0_le_one xs ell (L 0 + 1) a m (le_trans (Nat.mul_le_mul_right ell hm) hNN)
  rw [abs_of_nonneg this.1]; exact this.2

theorem regBg2_level1_stag0 {ell : ℕ} (hell : 0 < ell) (hN0 : ell ≤ L 0 + 1) (hN : 2 ∣ L 1 + 1) (hE : 2 ∣ ell)
    {xs : ℕ} (hxs1 : ell ≤ xs) (hxs2 : xs + ell ≤ L 0 + 1) (hNN : ell * ell ≤ L 0 + 1) (t : ℝ) (ht : |t| < Real.pi / 2) :
    RegBg2 ell ell (stridedBlockedGauge su2LogExp 1 ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) :=
  regBg2_of_uTemp hell (bg1_isUTemp_stag0 hell hN0 hN hE hxs1 hxs2 t ht) (u1s_abs_le hell t) (by linarith)
    (hSw0_windows xs hNN)

/-- at every stride-`ell` coarse site the first blocked level is trivial (the blocks are full and the staggered signs cancel). -/
theorem bg1_temporal_stag0 {ell : ℕ} (hell : 0 < ell) (hN0 : ell ≤ L 0 + 1) (hN : 2 ∣ L 1 + 1) (hE : 2 ∣ ell)
    (hdiv : ∀ μ, ell ∣ L μ + 1) {xs : ℕ} (hxs1 : ell ≤ xs) (hxs2 : xs + ell ≤ L 0 + 1) (t : ℝ) (ht : |t| < Real.pi / 2) :
    IsTemporal ell (stridedBlockedGauge su2LogExp 1 ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)) (fun _ => 0) := by
  intro y hy
  have hV := bg1_isUTemp_stag0 hell hN0 hN hE hxs1 hxs2 t ht y
  refine ⟨?_, hV.2.1, hV.2.2⟩
  rw [hV.1]
  congr 1
  have hf1 := crs_fit hdiv hy 1
  have hf2 := crs_fit hdiv hy 2
  have m1 : min ell (L 1 + 1 - (y 1).val) = ell := by omega
  have m2 : min ell (L 2 + 1 - (y 2).val) = ell := by omega
  unfold u1s
  rw [m1, m2]
  obtain ⟨m, hm⟩ := hE
  have hell' : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have hh : ((ell / 2 : ℕ) : ℝ) = (ell : ℝ) / 2 := by rw [hm, show 2 * m / 2 = m by omega]; push_cast; ring
  rw [hh]
  have : 1 - 2 * ((ell : ℝ) * (ell : ℝ) * ((ell : ℝ) / 2)) / (ell : ℝ) ^ 3 = 0 := by field_simp; ring
  rw [this]; simp

theorem bg2_temporal_stag0 {ell : ℕ} (hell : 0 < ell) (hN0 : ell ≤ L 0 + 1) (hN : 2 ∣ L 1 + 1) (hE : 2 ∣ ell)
    (hdiv : ∀ μ, ell ∣ L μ + 1) {xs : ℕ} (hxs1 : ell ≤ xs) (hxs2 : xs + ell ≤ L 0 + 1) (t : ℝ) (ht : |t| < Real.pi / 2) :
    IsTemporal (ell * ell)
      (stridedBlockedGauge su2LogExp ell ell (stridedBlockedGauge su2LogExp 1 ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L)))
      (fun _ => 0) := by
  have := blocked_temporal (ell := ell) hdiv (bg1_temporal_stag0 hell hN0 hN hE hdiv hxs1 hxs2 t ht)
  simpa using this

end

section
variable [CfData]
variable {ell : ℕ} {Lu : PeriodicLatticeExtent}

theorem scaleUp_dvd2 (hell : 0 < ell) : ∀ μ, ell ∣ scaleUp ell 2 Lu μ + 1 := fun μ => by
  rw [scaleUp_succ ell 2 Lu hell]; exact Dvd.dvd.mul_left (dvd_pow_self ell (by norm_num)) _

theorem unit_temporal_stag0 (hell : 0 < ell) (hE : 2 ∣ ell) {xs : ℕ} (t : ℝ) (ht : |t| < Real.pi / 2)
    (hxs1 : ell ≤ xs) (hxs2 : xs + ell ≤ scaleUp ell 2 Lu 0 + 1) (hNN : ell ≤ scaleUp ell 2 Lu 0 + 1) :
    IsTemporal 1 (unitBg ell 2 Lu hell (UbarTower su2LogExp ell (stag0Cfg (L := scaleUp ell 2 Lu) xs t : PeriodicLinkConfiguration SU2 (scaleUp ell 2 Lu)) 2))
      (fun _ => 0) := by
  have hdiv := scaleUp_dvd2 (Lu := Lu) hell
  have hN : 2 ∣ scaleUp ell 2 Lu 1 + 1 := dvd_trans hE (hdiv 1)
  have h2 := bg2_temporal_stag0 hell hNN hN hE hdiv hxs1 hxs2 t ht
  intro y _
  have hy : Crs (ell * ell) (embY ell 2 Lu hell y) := by
    intro μ
    rw [embY_val, pow_two]
    exact dvd_mul_right (ell * ell) _
  obtain ⟨a0, a1, a2⟩ := h2 _ hy
  simp only [UbarTower_succ, UbarTower_zero, pow_zero, pow_one] at *
  refine ⟨?_, ?_, ?_⟩
  · show stridedBlockedGauge su2LogExp ell ell (stridedBlockedGauge su2LogExp 1 ell (stag0Cfg xs t)) (embY ell 2 Lu hell y, 0) = _
    rw [a0]
  · exact a1
  · exact a2

theorem stag0_unit_regBg2 (hell : 0 < ell) (hE : 2 ∣ ell) {xs : ℕ} (t : ℝ) (ht : |t| < Real.pi / 2)
    (hxs1 : ell ≤ xs) (hxs2 : xs + ell ≤ scaleUp ell 2 Lu 0 + 1) (hNN : ell ≤ scaleUp ell 2 Lu 0 + 1) :
    RegBg2 1 ell (unitBg ell 2 Lu hell (UbarTower su2LogExp ell (stag0Cfg (L := scaleUp ell 2 Lu) xs t : PeriodicLinkConfiguration SU2 (scaleUp ell 2 Lu)) 2)) := by
  have hV := unit_temporal_stag0 (Lu := Lu) hell hE t ht hxs1 hxs2 hNN
  apply regBg2_of_ne_negOne
  intro cc x hx
  obtain ⟨y, μ⟩ := cc
  rw [loopVar_temporal (fun μ => one_dvd _) hV (fun μ => one_dvd _) μ hx]
  exact negOne_ne_one

theorem stag0_regTower (hell : 0 < ell) (hE : 2 ∣ ell) {xs : ℕ} (t : ℝ) (ht : |t| < Real.pi / 2)
    (hxs1 : ell ≤ xs) (hxs2 : xs + ell ≤ scaleUp ell 2 Lu 0 + 1) (hNN : ell * ell ≤ scaleUp ell 2 Lu 0 + 1) :
    RegTower2 ell (UbarTower su2LogExp ell (stag0Cfg (L := scaleUp ell 2 Lu) xs t : PeriodicLinkConfiguration SU2 (scaleUp ell 2 Lu))) 2 := by
  have hdiv := scaleUp_dvd2 (Lu := Lu) hell
  have hN : 2 ∣ scaleUp ell 2 Lu 1 + 1 := dvd_trans hE (hdiv 1)
  have hN0 : ell ≤ scaleUp ell 2 Lu 0 + 1 := le_trans (Nat.le_mul_self ell) hNN
  intro j hj
  have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl
  · simpa [UbarTower_zero] using regBg2_level0_stag0 hN0 xs t ht
  · simpa [UbarTower_succ, UbarTower_zero] using regBg2_level1_stag0 hell hN0 hN hE hxs1 hxs2 hNN t ht

end

end AdalyFormal.NcwdhTwo
