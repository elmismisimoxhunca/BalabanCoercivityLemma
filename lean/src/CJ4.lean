import CJ3
import ZR8Data

/-!
# CJ4 -- THE READ ROWS OF THE r8 STATEMENT ARE GENUINE JETS, for every `U` in the printed class

Hypotheses (the r8 locality hypotheses plus the class): `2 ≤ ell`, `1 ≤ k`, room `17 ell ≤ R M`, `Admissible ell M R k S`,
`TorusOK ell M Lu`, `ClassCoupled ell M c k S α₀ η U` with `η = ell^{-k}`, and the explicit smallness `ClassSmall ell (c M α₀)`
(`a ≤ 1`, `6(4π+4) ell^6 a < r0`, `4·10⁶ (4π+4) ell^6 a ≤ 1`; satisfiable: `classSmall_exists`).

* `classRows_QlinB` (bond sector, levels `1 ≤ j ≤ k`, rows `b ∈ bondsLam j`): `Genuine` -- component `b` of the printed
  composite (3.13) is `C^∞` at `0`, its derivative is row `b` of `QlinCompL` (the jet `QlinB` reads) and its second derivative
  is row `b` of `D2CompL` (so `C2CompL`, read by `C2rawB`, is `½ D²`).  Every intermediate row read (`ReadRow`) is analytic
  (`classRows_read`), hence not junk (`classRows_read_not_junk`).
* `classRows_unit` (unit level, rows `c` with `CRowIn ell Λ c`, read by `Q1jet`/`C2tilde`): the component
  `qStepComp 1 ell (unitBg … Ū^k) (c₋, c.2)` is `C^∞` at `0` (`HasFDerivAt` form `classRows_unit_hasFDerivAt`; not junk
  `classRows_unit_not_junk`).

Mechanism (no gauge is ever chosen): each needed block loop of `Ū^l` is a strided ladder; its plaquettes are bounded by
fine plaquettes in a ball (`CJ3.loop_small`); the ball lies in `Ω_{j-1}` (room + `Admissible` collar), where every fine
plaquette sits in ONE class cube of index `≥ j - 2` (`CoversPlaqOm0c`) and is bounded by its chart (`CJ3.plaq_small_class`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.ClassJets

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (pdist pcd Tower Admissible towerBj DescribedAt IsClassCube CubeBond HT bigSide scaleUp TorusOK
  LambdaOK LamPrime CRowIn)
open AdalyFormal.StatementLane2 (ClassCoupled PerCubeRegular2 CoversPlaqOm0c)
open AdalyFormal.StatementLaneG (LambdaOK2)
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CurvBlock (dv pw ladS ladPlaqs pathBonds off Box GoodPl curv_tower_na_loc loopVar_eq_ladS ladS_le
  mem_ladPlaqs ladPlaqs_aligned dv_conj dv_inv dv_one dv_nonneg)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarTowerSU2)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

/-! ## 0. the smallness of `a = c M α₀` -/

/-- the explicit smallness used (all constants exact; `r0` is the chart radius of `CJ1`). -/
def ClassSmall (ell : ℕ) (a : ℝ) : Prop :=
  0 ≤ a ∧ a ≤ 1 ∧ 6 * (4 * Real.pi + 4) * (ell : ℝ) ^ 6 * a < r0 ∧ 4000000 * (4 * Real.pi + 4) * (ell : ℝ) ^ 6 * a ≤ 1

/-- `ClassSmall` holds for all small `a ≥ 0` (non-vacuity; the headline's `a₀` is chosen after `ell`). -/
theorem classSmall_exists (ell : ℕ) : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 ≤ a → a ≤ a₀ → ClassSmall ell a := by
  set K : ℝ := (4 * Real.pi + 4) * ((ell : ℝ) ^ 6 + 1) with hK
  have hK0 : 0 < K := by have := Real.pi_pos; positivity
  have hr := r0_pos
  refine ⟨min 1 (min (r0 / (7 * K)) (1 / (4000001 * K))), by positivity, fun a ha0 ha => ?_⟩
  have h1 : a ≤ 1 := le_trans ha (min_le_left _ _)
  have h2 : a ≤ r0 / (7 * K) := le_trans ha (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : a ≤ 1 / (4000001 * K) := le_trans ha (le_trans (min_le_right _ _) (min_le_right _ _))
  have hpe : (0 : ℝ) ≤ (ell : ℝ) ^ 6 := by positivity
  have hpi : (0 : ℝ) < 4 * Real.pi + 4 := by have := Real.pi_pos; positivity
  have hle : (4 * Real.pi + 4) * (ell : ℝ) ^ 6 ≤ K := by rw [hK]; nlinarith
  refine ⟨ha0, h1, ?_, ?_⟩
  · have : 7 * K * a ≤ r0 := by rw [le_div_iff₀ (by positivity)] at h2; linarith
    have hKa : (4 * Real.pi + 4) * (ell : ℝ) ^ 6 * a ≤ K * a := mul_le_mul_of_nonneg_right hle ha0
    by_cases hz : a = 0
    · subst hz; simp; exact hr
    · have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hz)
      have : 0 < K * a := by positivity
      nlinarith
  · have : 4000001 * K * a ≤ 1 := by rw [le_div_iff₀ (by positivity)] at h3; linarith
    have hKa : (4 * Real.pi + 4) * (ell : ℝ) ^ 6 * a ≤ K * a := mul_le_mul_of_nonneg_right hle ha0
    nlinarith [mul_nonneg hK0.le ha0]

theorem pow_ratio_le (ell : ℕ) (hell : 1 ≤ ell) (C : ℝ) (hC : 0 ≤ C) {l m d : ℕ} (h : l ≤ m + d) :
    ((ell : ℝ) ^ 2) ^ l * (C / ((ell : ℝ) ^ 2) ^ m) ≤ ((ell : ℝ) ^ 2) ^ d * C := by
  have hellR : (1 : ℝ) ≤ (ell : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hell)
  have hm : (0 : ℝ) < ((ell : ℝ) ^ 2) ^ m := by positivity
  have hl : ((ell : ℝ) ^ 2) ^ l ≤ ((ell : ℝ) ^ 2) ^ (m + d) := pow_le_pow_right₀ hellR h
  rw [pow_add] at hl
  rw [mul_div_assoc', div_le_iff₀ hm]
  calc ((ell : ℝ) ^ 2) ^ l * C ≤ (((ell : ℝ) ^ 2) ^ m * ((ell : ℝ) ^ 2) ^ d) * C := mul_le_mul_of_nonneg_right hl hC
    _ = ((ell : ℝ) ^ 2) ^ d * C * ((ell : ℝ) ^ 2) ^ m := by ring

/-! ## 1. torus and geometry facts -/

theorem scaleUp_succ (ell k : ℕ) (hell : 0 < ell) (Lu : PeriodicLatticeExtent) (μ : Fin 3) :
    scaleUp ell k Lu μ + 1 = (Lu μ + 1) * ell ^ k := by
  unfold scaleUp
  have : 1 ≤ (Lu μ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

theorem scaleUp_dvd (ell k : ℕ) (hell : 0 < ell) (Lu : PeriodicLatticeExtent) {l : ℕ} (hl : l ≤ k) (μ : Fin 3) :
    ell ^ l ∣ scaleUp ell k Lu μ + 1 := by
  rw [scaleUp_succ ell k hell]
  exact Dvd.dvd.mul_left (Nat.pow_dvd_pow ell hl) _

theorem scaleUp_big (ell k : ℕ) (hell : 2 ≤ ell) (Lu : PeriodicLatticeExtent) (hT : ∀ μ : Fin 3, ell < Lu μ + 1)
    {l : ℕ} (hl : l ≤ k) (μ : Fin 3) : 2 * ell ^ l < scaleUp ell k Lu μ + 1 := by
  rw [scaleUp_succ ell k (by omega)]
  have h1 : ell ^ l ≤ ell ^ k := Nat.pow_le_pow_right (by omega) hl
  have h2 := hT μ
  have hp : 0 < ell ^ k := pow_pos (by omega) k
  nlinarith

variable {L : PeriodicLatticeExtent}

/-- rows of `bondsLam j` are `ell^j`-aligned and within `ell^j` of a point of `Ω_j`. -/
theorem bondsLam_facts {ell k : ℕ} {S : Tower L} {j : ℕ} (hd : ∀ ρ : Fin 3, ell ^ j ∣ L ρ + 1) {b : Bond L}
    (hb : b ∈ bondsLam (geomOf ell k S) j) :
    b.1 ∈ CoarseLattice L (ell ^ j) ∧ ∃ y0 ∈ S.Om j, pdist y0 b.1 ≤ ell ^ j := by
  rcases hb.1 with h | h
  · refine ⟨?_, b.1, h.2.1, by rw [pdist_self]; exact Nat.zero_le _⟩
    rw [mem_CoarseLattice]; intro ν; exact Nat.mod_eq_zero_of_dvd (h.1 ν)
  · refine ⟨?_, _, h.2.1, by rw [pdist_comm]; exact pdist_coarseShift_le _ _ _⟩
    rw [mem_CoarseLattice]; intro ν
    have hν := h.1 ν
    by_cases hνμ : ν = b.2
    · subst hνμ
      rw [coarseShift_val_eq] at hν
      have h1 : ell ^ j ∣ (b.1 b.2).val + ell ^ j := (Nat.dvd_mod_iff (hd b.2)).mp hν
      exact Nat.mod_eq_zero_of_dvd ((Nat.dvd_add_left (dvd_refl _)).mp h1)
    · rw [coarseShift_apply_ne _ _ _ _ hνμ] at hν
      exact Nat.mod_eq_zero_of_dvd hν

theorem rhoT_gap (ell : ℕ) (hell : 2 ≤ ell) (i : ℕ) :
    ∀ j, i ≤ j → rhoT ell j + 8 * ell ^ i ≤ rhoT ell i + 8 * ell ^ j := by
  intro j hij
  induction j with
  | zero => have : i = 0 := by omega
            subst this; omega
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with e | e
      · rw [e]
      · have := ih (by omega)
        rw [rhoT_succ, pow_succ]
        have : 8 * ell ^ j ≤ 4 * (ell ^ j * ell) := by nlinarith [pow_pos (show 0 < ell by omega) j]
        nlinarith

/-- **the read region of a level-`l` row read by `b ∈ bondsLam j` lies (with its plaquettes) in `Ω_{j-1}`.** -/
theorem read_region {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hd : ∀ ρ : Fin 3, ell ^ j ∣ L ρ + 1)
    {b : Bond L} (hb : b ∈ bondsLam (geomOf ell k S) j) {l : ℕ} {e : PeriodicLatticeEdge L} (hr : ReadRow ell j b l e) :
    ∀ z ∈ Ball e.1 (4 * (ell ^ l * ell) + 2 * rhoT ell l), Ball z 2 ⊆ S.Om (j - 1) := by
  intro z hz
  obtain ⟨-, y0, hy0, hdy⟩ := bondsLam_facts hd hb
  have hy0' : y0 ∈ S.Om ((j - 1) + 1) := by rw [Nat.sub_add_cancel hj1]; exact hy0
  have hball := admissible_ball hS (j := j - 1) (by omega) hy0'
  refine le_trans (Ball_sub (y' := z) (d := pdist y0 z) le_rfl ?_) hball
  -- distances
  have h1 := pdist_triangle y0 b.1 e.1
  have h2 := pdist_triangle y0 e.1 z
  have hbe := hr.2.2
  have hzz : pdist e.1 z ≤ 4 * (ell ^ l * ell) + 2 * rhoT ell l := hz
  have hlj : l + 1 ≤ j := hr.1
  have hgap := rhoT_gap ell hell (l + 1) j hlj
  have hrl := rhoT_le ell hell l
  have hmono : rhoT ell (l + 1) ≤ rhoT ell j := rhoT_mono ell hlj
  have hpl : ell ^ (l + 1) = ell ^ l * ell := pow_succ ell l
  have hpl2 : 16 * ell ^ l ≤ 8 * (ell ^ l * ell) := by nlinarith [pow_pos (show 0 < ell by omega) l]
  have hplj : ell ^ (l + 1) ≤ ell ^ j := Nat.pow_le_pow_right (by omega) hlj
  have hroomj : 17 * ell ^ j ≤ R * (M * ell ^ (j - 1)) := by
    have e1 : ell ^ j = ell * ell ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
    rw [e1]
    have := Nat.mul_le_mul_right (ell ^ (j - 1)) hroom
    calc 17 * (ell * ell ^ (j - 1)) = 17 * ell * ell ^ (j - 1) := by ring
      _ ≤ R * M * ell ^ (j - 1) := this
      _ = R * (M * ell ^ (j - 1)) := by ring
  show pdist y0 z + 2 ≤ R * bigSide M ell (j - 1)
  unfold bigSide
  omega

/-! ## 2. the bond sector: rows of `QlinB`, `C2rawB` -/

/-- every row read by `b ∈ bondsLam j` is analytic. -/
theorem classRows_read {ell M R k c : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ}
    {U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)}
    (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S) (hT : TorusOK ell M Lu)
    (hU : ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hsm : ClassSmall ell ((c : ℝ) * M * α₀))
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {b : Bond (scaleUp ell k Lu)} (hb : b ∈ bondsLam (geomOf ell k S) j)
    {l : ℕ} {e : PeriodicLatticeEdge (scaleUp ell k Lu)} (hr : ReadRow ell j b l e) :
    ContDiffAt ℝ ⊤ (qStepComp (ell ^ l) ell (bgTower (geomOf ell k S) U l) e) 0 := by
  have hell0 : 0 < ell := by omega
  obtain ⟨ha0, ha1, hthr, hsmall⟩ := hsm
  set a : ℝ := (c : ℝ) * M * α₀ with ha
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hlk : l ≤ k := by have := hr.1; omega
  have hdj : ∀ ρ : Fin 3, ell ^ j ∣ scaleUp ell k Lu ρ + 1 := scaleUp_dvd ell k hell0 Lu hjk
  set q0 : ℝ := (4 * Real.pi + 4) * a / (((ell : ℝ) ^ 2) ^ (j - 1 - 1)) with hq0
  have hpi : (0 : ℝ) < 4 * Real.pi + 4 := by have := Real.pi_pos; positivity
  have hq0n : 0 ≤ q0 := by positivity
  have hX : ((ell : ℝ) ^ 2) ^ l * q0 ≤ ((ell : ℝ) ^ 2) ^ 1 * ((4 * Real.pi + 4) * a) := by
    rw [hq0]; exact pow_ratio_le ell (by omega) _ (by positivity) (by have := hr.1; omega)
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have he6 : (ell : ℝ) ^ 2 * ((ell : ℝ) ^ 2) ^ 1 ≤ (ell : ℝ) ^ 6 := by
    rw [pow_one, ← pow_add]; exact pow_le_pow_right₀ hellR (by norm_num)
  have hX6 : (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ l * q0) ≤ (ell : ℝ) ^ 6 * ((4 * Real.pi + 4) * a) := by
    calc (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ l * q0) ≤ (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ 1 * ((4 * Real.pi + 4) * a)) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = ((ell : ℝ) ^ 2 * ((ell : ℝ) ^ 2) ^ 1) * ((4 * Real.pi + 4) * a) := by ring
      _ ≤ (ell : ℝ) ^ 6 * ((4 * Real.pi + 4) * a) := mul_le_mul_of_nonneg_right he6 (by positivity)
  have he : e.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) := by
    have h := hr.2.1
    rw [mem_CoarseLattice] at h ⊢
    intro ν
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow ell (by omega)) (Nat.dvd_of_mod_eq_zero (h ν)))
  refine qStepComp_contDiffAt_of_row _ _ _ _ ?_
  refine regRow_of_plaq ell hell U q0 hq0n l (scaleUp_dvd ell k hell0 Lu hlk) (scaleUp_big ell k hell Lu hT.2.1 hlk)
    ?_ ?_ e he ?_
  · nlinarith
  · nlinarith
  · intro z hz ν μ
    have := plaq_small_class (L := scaleUp ell k Lu) (by omega) hη hS hU ha0 ha1 z
      (read_region hS hell hroom hj1 hjk hdj hb hr z hz) ν μ
    exact this

/-- **THE BOND-SECTOR ROWS ARE GENUINE** (first and second order), for every `U` in the class. -/
theorem classRows_QlinB {ell M R k c : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ}
    {U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)}
    (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S) (hT : TorusOK ell M Lu)
    (hU : ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hsm : ClassSmall ell ((c : ℝ) * M * α₀))
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {b : Bond (scaleUp ell k Lu)} (hb : b ∈ bondsLam (geomOf ell k S) j) :
    Genuine ell (bgTower (geomOf ell k S) U) j b := by
  have hell0 : 0 < ell := by omega
  exact comp_genuine ell hell0 (bgTower (geomOf ell k S) U) k (scaleUp_dvd ell k hell0 Lu le_rfl) j hjk b
    (bondsLam_facts (scaleUp_dvd ell k hell0 Lu hjk) hb).1
    (fun l e hr => classRows_read hell hroom hS hT hU hsm hj1 hjk hb hr)

/-- the companion of `AuditR8.QlinStepL_row_junk`: its hypothesis fails at every row read by the bond sector. -/
theorem classRows_read_not_junk {ell M R k c : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ}
    {U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)}
    (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S) (hT : TorusOK ell M Lu)
    (hU : ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hsm : ClassSmall ell ((c : ℝ) * M * α₀))
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {b : Bond (scaleUp ell k Lu)} (hb : b ∈ bondsLam (geomOf ell k S) j)
    {l : ℕ} {e : PeriodicLatticeEdge (scaleUp ell k Lu)} (hr : ReadRow ell j b l e) :
    ¬ ¬ DifferentiableAt ℝ (qStepComp (ell ^ l) ell (bgTower (geomOf ell k S) U l) e) 0 :=
  fun h => h ((classRows_read hell hroom hS hT hU hsm hj1 hjk hb hr).differentiableAt (by simp))

#print axioms read_region
#print axioms classSmall_exists
#print axioms classRows_read
#print axioms classRows_QlinB
#print axioms classRows_read_not_junk

end AdalyFormal.ClassJets
