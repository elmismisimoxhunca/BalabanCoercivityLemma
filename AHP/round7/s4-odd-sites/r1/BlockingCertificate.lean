import SoA3
import SoPar

/-!
# Round 7 S-4: the genuine odd-scale sites-only cell

The local body below is copied verbatim from CaT2d, with only the namespace
changed. `body_eq_frozen` checks the identity. All goals retain WellDefG as
an antecedent, NOT as a conclusion and NOT merely the Ginv guard.
Goal2 is pointwise failure at every odd scale, stronger than `¬ Goal1`.
Goal4 is pointwise failure at ell = 13, stronger than `¬ Goal3`.
These are targets, not asserted theorems.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.Round7.S4OddSites

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.CoverStrong (InstIneqWDH)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open MXQ.AllC
open NcwdhFam

/-- Verbatim body from frozen CaT2d.lean. -/
def FamilyTorusSitesConstAt (c ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            CovSitesF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S ∧
              PerCubeRegularF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneqWDH ell k (by omega) a Lu γ₀ S Lam U

theorem body_eq_frozen (c ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) :
    FamilyTorusSitesConstAt c ell hell a =
      CovAssume.FamilyTorusSitesConstAt c ell hell a := rfl

/-- Positive, every odd ell >= 3, every factor c >= 10, every a > 0. -/
def Goal1 : Prop :=
  ∀ (c ell : ℕ), 10 ≤ c → (hell : 3 ≤ ell) → ell % 2 = 1 →
    ∀ (a : ℝ), 0 < a → FamilyTorusSitesConstAt c ell (by omega) a

/-- Negative at each parameter triple; not just the negation of Goal1. -/
def Goal2 : Prop :=
  ∀ (c ell : ℕ), 10 ≤ c → (hell : 3 ≤ ell) → ell % 2 = 1 →
    ∀ (a : ℝ), 0 < a → ¬ FamilyTorusSitesConstAt c ell (by omega) a

/-- Fixed odd scale in the recorded CMP109 range, still every c >= 10, a > 0. -/
def Goal3 : Prop :=
  ∀ (c : ℕ), 10 ≤ c → ∀ (a : ℝ), 0 < a →
    FamilyTorusSitesConstAt c 13 (by norm_num) a

/-- Negative counterpart at ell = 13; no divisibility or width restriction. -/
def Goal4 : Prop :=
  ∀ (c : ℕ), 10 ≤ c → ∀ (a : ℝ), 0 < a →
    ¬ FamilyTorusSitesConstAt c 13 (by norm_num) a

theorem goal1_implies_goal3 : Goal1 → Goal3 := by
  intro h c hc a ha
  exact h c 13 hc (by norm_num) (by norm_num) a ha

theorem goal2_implies_goal4 : Goal2 → Goal4 := by
  intro h c hc a ha
  exact h c 13 hc (by norm_num) (by norm_num) a ha

theorem goal3_goal4_incompatible : Goal3 → Goal4 → False := by
  intro hp hn
  exact hn 10 (by norm_num) 1 (by norm_num) (hp 10 (by norm_num) 1 (by norm_num))

theorem goal1_goal2_incompatible : Goal1 → Goal2 → False := by
  intro hp hn
  exact goal3_goal4_incompatible (goal1_implies_goal3 hp) (goal2_implies_goal4 hn)

#check Goal1
#check Goal2
#check Goal3
#check Goal4
#check CovAssume.FamilyTorusSitesConstAt
#check NcwdhFam.CovSitesF
#check NcwdhFam.PerCubeRegularF
#check AdalyFormal.CoverStrong.InstIneqWDH
#check AdalyFormal.SitesOnly.main_neg_S
#check AdalyFormal.SitesOnly.sites_not_imp_plaq_S
#check AdalyFormal.SitesOnly.no_uniform_step_blockzero_odd
#print axioms FamilyTorusSitesConstAt
#print axioms body_eq_frozen
#print axioms Goal1
#print axioms Goal2
#print axioms Goal3
#print axioms Goal4
#print axioms goal1_implies_goal3
#print axioms goal2_implies_goal4
#print axioms goal3_goal4_incompatible
#print axioms goal1_goal2_incompatible

end AdalyFormal.Round7.S4OddSites

namespace AdalyFormal.Round7.S4OddSites.Partial

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.CoverJacobi
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SitesOnly
open AdalyFormal.NcwdhTwo
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.NoCover (perCube_one)
open MXQ.AllC
open NcwdhFam

/-- Alternating pairs followed by one zero, with period ell. -/
def oddProfile (ell x : ℕ) : ℤ :=
  if x % ell + 1 = ell then 0 else (-1) ^ (x % ell)

theorem alternating_even_sum (n : ℕ) :
    (∑ i ∈ range (2 * n), (-1 : ℤ) ^ i) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      sum_range_succ, sum_range_succ, ih, pow_succ]
    ring

theorem oddProfile_periodic (ell x : ℕ) :
    oddProfile ell (x + ell) = oddProfile ell x := by
  simp [oddProfile]

theorem oddProfile_aligned (ell q i : ℕ) :
    oddProfile ell (q * ell + i) = oddProfile ell i := by
  simp [oddProfile]

theorem oddProfile_sum (ell : ℕ) (hodd : ell % 2 = 1) :
    (∑ i ∈ range ell, oddProfile ell i) = 0 := by
  obtain ⟨n, hn⟩ : ∃ n, ell = 2 * n + 1 := ⟨ell / 2, by omega⟩
  subst ell
  rw [sum_range_succ]
  have hlast : oddProfile (2 * n + 1) (2 * n) = 0 := by
    simp [oddProfile, Nat.mod_eq_of_lt (by omega : 2 * n < 2 * n + 1)]
  have hinside : (∑ i ∈ range (2 * n), oddProfile (2 * n + 1) i) =
      ∑ i ∈ range (2 * n), (-1 : ℤ) ^ i := by
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    simp [oddProfile, Nat.mod_eq_of_lt (by omega : i < 2 * n + 1),
      show i ≠ 2 * n by omega]
  rw [hlast, hinside, alternating_even_sum, add_zero]

theorem oddProfile_block_sum (ell q : ℕ) (hodd : ell % 2 = 1) :
    (∑ i ∈ range ell, ∑ _j ∈ range ell, oddProfile ell (q * ell + i)) = 0 := by
  simp_rw [oddProfile_aligned]
  simp only [sum_const, card_range, nsmul_eq_mul]
  rw [← mul_sum, oddProfile_sum ell hodd, mul_zero]

theorem oddProfile_first_step (ell : ℕ) (hell : 3 ≤ ell) :
    oddProfile ell 1 - oddProfile ell 0 = -2 := by
  norm_num [oddProfile, Nat.mod_eq_of_lt (by omega : 1 < ell),
    show 1 + 1 ≠ ell by omega, show 0 + 1 ≠ ell by omega]

theorem oddProfile_seam_step (ell : ℕ) (hell : 3 ≤ ell) :
    oddProfile ell ell - oddProfile ell (ell - 1) = 1 := by
  have hlast : ell - 1 + 1 = ell := by omega
  simp [oddProfile, Nat.mod_eq_of_lt (by omega : ell - 1 < ell),
    hlast, show 0 + 1 ≠ ell by omega]

/-- No fixed-magnitude integer step model can describe this profile. -/
theorem oddProfile_not_const_step (ell : ℕ) (hell : 3 ≤ ell) :
    ¬ ∃ d : ℕ, ∀ x : ℕ,
      oddProfile ell (x + 1) = oddProfile ell x + (d : ℤ) ∨
      oddProfile ell (x + 1) = oddProfile ell x - (d : ℤ) := by
  rintro ⟨d, hd⟩
  have hfirst := hd 0
  have hseam := hd (ell - 1)
  have e1 := oddProfile_first_step ell hell
  have e2 := oddProfile_seam_step ell hell
  rw [show ell - 1 + 1 = ell by omega] at hseam
  simp only [zero_add] at hfirst
  rcases hfirst with hfirst | hfirst <;>
    rcases hseam with hseam | hseam <;> omega

/-- Arbitrary Cartan phases on the hidden direction-0 slice, identity elsewhere. -/
noncomputable def sliceCfg {L : PeriodicLatticeExtent} (C : ℕ) (f : ℕ → ℝ) : LinkCfg L :=
  fun e => if (e.1 0).val = C ∧ e.2 = 0 then cartan (f (e.1 1).val) else 1

/-- A genuine gauge field for the variable-step profile. -/
noncomputable def oddCfg {L : PeriodicLatticeExtent} (ell C : ℕ) (t : ℝ) : LinkCfg L :=
  sliceCfg C (fun x => t * (oddProfile ell x : ℝ))

#print axioms oddProfile
#print axioms alternating_even_sum
#print axioms oddProfile_periodic
#print axioms oddProfile_aligned
#print axioms oddProfile_sum
#print axioms oddProfile_block_sum
#print axioms oddProfile_first_step
#print axioms oddProfile_seam_step
#print axioms oddProfile_not_const_step
#print axioms sliceCfg
#print axioms oddCfg
end AdalyFormal.Round7.S4OddSites.Partial

/-! New round-1 extension. The pin and prior partial proof are copied above. -/
namespace AdalyFormal.Round7.S4OddSites.R1

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.NcwdhTwo
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.SitesOnly
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar UbarTower UbarTower_succ UbarTower_zero)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Round7.S4OddSites.Partial
open MXQ.AllC
open NcwdhFam

/-- The new profile is bounded without any parity premise. -/
theorem oddProfile_abs_le (ell x : ℕ) : |(oddProfile ell x : ℝ)| ≤ 1 := by
  unfold oddProfile
  split_ifs
  · norm_num
  · push_cast
    rw [abs_pow]
    norm_num

/-- Periodicity survives the actual torus wrap when its side is a multiple of ell. -/
theorem oddProfile_mod_shift (ell N x : ℕ) (hN : ell ∣ N) :
    oddProfile ell ((x + ell) % N) = oddProfile ell x := by
  unfold oddProfile
  rw [Nat.mod_mod_of_dvd _ hN, Nat.add_mod_right]

/-- Real block sum at every aligned base, not just the origin. -/
theorem oddProfile_real_sum (ell x : ℕ) (hodd : ell % 2 = 1) (hx : ell ∣ x) :
    (∑ n ∈ range ell, (oddProfile ell (x + n) : ℝ)) = 0 := by
  obtain ⟨q, rfl⟩ := hx
  simp_rw [Nat.mul_comm ell q, oddProfile_aligned]
  exact_mod_cast oddProfile_sum ell hodd

/-- The actual slice configuration belongs to the frozen temporal-profile class. -/
theorem sliceCfg_isUTemp [CfData] {L : PeriodicLatticeExtent} (C : ℕ) (f : ℕ → ℝ) :
    IsUTemp (D0 C) (fun x _ => f x) (sliceCfg (L := L) C f) := by
  intro z
  constructor
  · by_cases h : (z 0).val = C
    · simp [sliceCfg, D0, h]
    · simp [sliceCfg, D0, h, cartan_zero]
  · constructor <;> simp [sliceCfg]

/-- No principal-log branch is crossed at level zero in the open interval. -/
theorem oddCfg_regBg2_level0 [CfData] {L : PeriodicLatticeExtent} {ell : ℕ}
    (hN0 : ell ≤ L 0 + 1) (C : ℕ) (t : ℝ) (ht : |t| < Real.pi / 2) :
    RegBg2 1 ell (oddCfg (L := L) ell C t) := by
  apply regBg2_of_uTemp one_pos (sliceCfg_isUTemp C (fun x => t * (oddProfile ell x : ℝ)))
    (B := |t|)
  · intro x _
    rw [abs_mul]
    calc |t| * |(oddProfile ell x : ℝ)| ≤ |t| * 1 := by
           gcongr
           exact oddProfile_abs_le ell x
      _ = |t| := mul_one _
  · linarith
  · exact hD0_stride_one hN0 C

/-- Actual principal-log blocking, not just integer cancellation: on every
aligned coarse site the first blocked gauge is exactly the identity. -/
theorem oddCfg_bg1_temporal [CfData] {L : PeriodicLatticeExtent} {ell : ℕ}
    (hell : 0 < ell) (hodd : ell % 2 = 1) (hdiv : ∀ μ, ell ∣ L μ + 1)
    (hN0 : ell ≤ L 0 + 1) (C : ℕ) (t : ℝ) (ht : |t| < Real.pi / 2) :
    IsTemporal ell (stridedBlockedGauge su2LogExp 1 ell
      (oddCfg (L := L) ell C t)) (fun _ => 0) := by
  let f : ℕ → ℝ := fun x => t * (oddProfile ell x : ℝ)
  let u : ℕ → ℕ → ℝ := fun x _ => f x
  have hV : IsUTemp (D0 C) u (oddCfg (L := L) ell C t) := sliceCfg_isUTemp C f
  have hu : ∀ x y, |u x y| ≤ |t| := by
    intro x y
    dsimp [u, f]
    rw [abs_mul]
    calc |t| * |(oddProfile ell x : ℝ)| ≤ |t| * 1 := by
           gcongr
           exact oddProfile_abs_le ell x
      _ = |t| := mul_one _
  have hper : ∀ x, f ((x + ell) % (L 1 + 1)) = f x := by
    intro x
    dsimp [f]
    rw [oddProfile_mod_shift ell _ x (hdiv 1)]
  intro z hz
  have hcount : ∀ μ, min ell (L μ + 1 - (z μ).val) = ell := by
    intro μ
    have := crs_fit hdiv hz μ
    omega
  have hsum : (∑ n ∈ range ell, f ((z 1).val + n)) = 0 := by
    dsimp [f]
    rw [← mul_sum, oddProfile_real_sum ell (z 1).val hodd (hz 1), mul_zero]
  have hcb : ∀ μ : Fin 3,
      coarseBondVar 1 ell (oddCfg (L := L) ell C t) (z, μ) =
        cartan (if μ = 0 then Sw0 C ell (L 0 + 1) (z 0).val * f (z 1).val else 0) := by
    intro μ
    unfold coarseBondVar
    rw [hol_uTemp hV]
    congr 1
    by_cases hμ : μ = 0
    · subst hμ
      simp only [if_true]
      rw [uAng_rep_zero, ← sum_mul]
      simp only [Sw0, u, one_mul]
    · simp only [hμ, if_false]
      exact uAng_rep_ne 1 _ _ μ hμ ell z
  have hformula : ∀ μ : Fin 3,
      stridedBlockedGauge su2LogExp 1 ell (oddCfg (L := L) ell C t) (z, μ) =
        cartan ((((ell : ℝ) ^ 3)⁻¹ * ∑ x ∈ stepBlockOf z 1 ell,
          uPhi 1 ell (D0 C) u z μ x) +
            if μ = 0 then Sw0 C ell (L 0 + 1) (z 0).val * f (z 1).val else 0) := by
    intro μ
    exact blocked_cartan 1 ell _ (z, μ) _ _
      (fun x hx => ⟨loopVar_uPhi hV z μ hx,
        uPhi_abs_lt one_pos hu (by linarith) (hD0_stride_one hN0 C) z μ hx⟩)
      (hcb μ)
  have hzero : ∀ μ : Fin 3,
      stridedBlockedGauge su2LogExp 1 ell (oddCfg (L := L) ell C t) (z, μ) = 1 := by
    intro μ
    rw [hformula]
    apply Eq.trans _ cartan_zero
    congr 1
    fin_cases μ
    · simp only [uPhi, Fin.zero_eta, if_true, one_mul]
      change ((ell : ℝ) ^ 3)⁻¹ * (∑ x ∈ stepBlockOf z 1 ell,
        Sw0 C ell (L 0 + 1) (z 0).val * (f (x 1).val - f (z 1).val)) +
          Sw0 C ell (L 0 + 1) (z 0).val * f (z 1).val = 0
      have hterms : ∀ x ∈ stepBlockOf z 1 ell,
          f (x 1).val - f (z 1).val =
            (fun n => f ((z 1).val + n) - f (z 1).val) ((x 1).val - (z 1).val) := by
        intro x hx
        have := (mem_stepBlockOf.mp hx 1).1
        dsimp only
        rw [show (z 1).val + ((x 1).val - (z 1).val) = (x 1).val by omega]
      simp_rw [← mul_sum]
      rw [sum_congr rfl hterms,
        sum_block_one z ell (fun n => f ((z 1).val + n) - f (z 1).val),
        hcount 0, hcount 2, hcount 1,
        sum_sub_distrib, hsum]
      simp only [sum_const, card_range, nsmul_eq_mul]
      have hl : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
      field_simp
      <;> ring
    · simp only [uPhi, if_neg (show (1 : Fin 3) ≠ 0 by decide), if_true, one_mul]
      have hs : ∑ x ∈ stepBlockOf z 1 ell,
          (∑ j ∈ range ((x 0 - z 0).val / 1), D0 C (((z 0).val + j) % (L 0 + 1))) *
            (u (x 1).val (x 2).val - u (((x 1).val + ell) % (L 1 + 1)) (x 2).val) = 0 := by
        apply sum_eq_zero
        intro x _
        dsimp [u]
        rw [hper, sub_self, mul_zero]
      rw [hs]
      simp
    · simp [uPhi, u]
  exact ⟨by simpa [cartan_zero] using hzero 0, hzero 1, hzero 2⟩

/-- The second blocking remains temporal with zero angles, at every odd scale. -/
theorem oddCfg_bg2_temporal [CfData] {L : PeriodicLatticeExtent} {ell : ℕ}
    (hell : 0 < ell) (hodd : ell % 2 = 1) (hdiv : ∀ μ, ell ∣ L μ + 1)
    (hN0 : ell ≤ L 0 + 1) (C : ℕ) (t : ℝ) (ht : |t| < Real.pi / 2) :
    IsTemporal (ell * ell) (stridedBlockedGauge su2LogExp ell ell
      (stridedBlockedGauge su2LogExp 1 ell (oddCfg (L := L) ell C t))) (fun _ => 0) := by
  simpa using blocked_temporal (ell := ell) hdiv
    (oddCfg_bg1_temporal hell hodd hdiv hN0 C t ht)

/-- Exact unit-background identity, including nonzero parameters in the interval. -/
theorem oddCfg_unitBg_temporal [CfData] {ell : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) (hodd : ell % 2 = 1) (C : ℕ)
    (hN0 : ell ≤ scaleUp ell 2 Lu 0 + 1) (t : ℝ) (ht : |t| < Real.pi / 2) :
    IsTemporal 1 (unitBg ell 2 Lu hell
      (UbarTower su2LogExp ell (oddCfg (L := scaleUp ell 2 Lu) ell C t) 2))
      (fun _ => 0) := by
  have h2 := oddCfg_bg2_temporal hell hodd (scaleUp_dvd2 (Lu := Lu) hell) hN0 C t ht
  intro y _
  have hy : Crs (ell * ell) (embY ell 2 Lu hell y) := by
    intro μ
    rw [embY_val, pow_two]
    exact dvd_mul_right (ell * ell) _
  obtain ⟨a0, a1, a2⟩ := h2 _ hy
  simp only [UbarTower_succ, UbarTower_zero, pow_zero, pow_one] at *
  exact ⟨a0, a1, a2⟩

/-- The H0 part of the full inverse guard now holds throughout the open path.
The other four carrier/coarse inverse conditions are NOT concluded. -/
theorem oddCfg_H0_bijective [CfData] {ell M R C : ℕ} (hell : 2 ≤ ell)
    (hodd : ell % 2 = 1) (hdvd : ell ∣ M) (hM : 0 < M)
    (t a : ℝ) (ht : |t| < Real.pi / 2) :
    Function.Bijective (H0 (neLam M R)
      (gparams ell 2 (neLu M R) (by omega) (neS ell M R)
        (oddCfg ell C t) a (neLam M R)).Q1) := by
  have hell0 : 0 < ell := by omega
  have hN0 : ell ≤ scaleUp ell 2 (neLu M R) 0 + 1 := by
    rw [IngredientFamilyR2.scaleUp_succ _ _ _ hell0]
    have := Nat.le_mul_self ell
    have := Nat.le_mul_of_pos_left (ell ^ 2) (Nat.succ_pos (neLu M R 0))
    nlinarith
  exact H0_temporal_bijective hell0 (unit_hdiv hdvd hM) (neLam M R)
    (oddCfg_unitBg_temporal hell0 hodd C hN0 t ht) (by simp)

#print axioms oddProfile_abs_le
#print axioms oddProfile_mod_shift
#print axioms oddProfile_real_sum
#print axioms sliceCfg_isUTemp
#print axioms oddCfg_regBg2_level0
#print axioms oddCfg_bg1_temporal
#print axioms oddCfg_bg2_temporal
#print axioms oddCfg_unitBg_temporal
#print axioms oddCfg_H0_bijective

end AdalyFormal.Round7.S4OddSites.R1
