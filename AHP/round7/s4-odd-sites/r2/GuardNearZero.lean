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


/-!
# Variable-step odd profile and actual sites-covered class family

No headline is proved here. The profile is 1,-1,...,1,-1,0 repeated with
odd period ell. Its aligned sums vanish; its steps have two magnitudes.
The class witness uses the frozen uncovered-slice geometry, not a toy tower.
No blocking identity, nonzero-parameter inverse guard, or negative full form
is asserted. The full guard is proved only at the flat parameter zero.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

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

/-- Generalization of SoD0: the hidden-slice profile can be arbitrary. -/
theorem sliceCfg_class [CfData] {ell M R c : ℕ} (hell : 2 ≤ ell)
    (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c)
    (f : ℕ → ℝ) {α₀ : ℝ} (hα : 0 < α₀) :
    PerCubeRegular2 ell M c 2 (neS ell M R) α₀ ((ell : ℝ) ^ 2)⁻¹
      (sliceCfg (L := scaleUp ell 2 (neLu M R)) (soC ell M R c) f) := by
  have hell0 : 0 < ell := by omega
  have hη : (0 : ℝ) < ((ell : ℝ) ^ 2)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  refine perCube_congr' (perCube_one hell0 hM (by omega) hα hη) (fun e he => ?_)
  obtain ⟨sites, j, hq, hb⟩ := he
  by_cases h0 : (e.1 0).val = soC ell M R c ∧ e.2 = 0
  · obtain ⟨hx, he2⟩ := h0
    exfalso
    have hb' := hb
    obtain ⟨e1, e2⟩ := e
    simp only at hx he2
    subst he2
    exact so_bond_uncovered hell hM hR hrel (by omega) e1 hx sites j hq hb'
  · simp [sliceCfg, h0]

/-- Exact holonomy of the actual background; weights are not spatially constant. -/
theorem sliceCfg_holonomy_01 {L : PeriodicLatticeExtent} (C : ℕ) (f : ℕ → ℝ)
    (x : PeriodicLatticeSite L)
    (h : ((0 : Fin 3), (1 : Fin 3)).1 < ((0 : Fin 3), (1 : Fin 3)).2) :
    holonomyElem (sliceCfg (L := L) C f) (x, ⟨((0 : Fin 3), (1 : Fin 3)), h⟩) =
      cartan (if (x 0).val = C then
        f (x 1).val - f ((periodicLatticeShift x 1) 1).val else 0) := by
  letI : CfData := ⟨10, by norm_num⟩
  unfold holonomyElem periodicPlaquetteHolonomy sliceCfg
  have e : (periodicLatticeShift x 1) 0 = x 0 := by simp [periodicLatticeShift]
  by_cases h2 : (x 0).val = C
  · simp [e, h2, cartan_inv, cartan_mul, ← sub_eq_add_neg]
  · simp [e, h2, cartan_zero]

/-- The existing geometry has a nonempty odd-scale arithmetic window. -/
abbrev thinWidth : CfData := ⟨19, by norm_num⟩

theorem arithmetic_window (ell : ℕ) (hell : 3 ≤ ell) :
    10 ≤ 9 * ell + 1 ∧ ell * (19 - 1) = 2 * ((9 * ell + 1) - 1) := by
  constructor
  · omega
  · simp only [Nat.add_sub_cancel, show (19 : ℕ) - 1 = 18 by norm_num]
    ring

/-- At arbitrary large scales and radii, this actual family has site coverage,
no plaquette coverage, and regularity for every positive cap and every angle.
The factor is 9 ell + 1 here, not every factor in the pinned goals. -/
theorem oddCfg_cofinal_class (ell : ℕ) (hell : 3 ≤ ell) (m₁ R₁ : ℕ) :
    letI : CfData := thinWidth
    ∃ m : ℕ, m₁ ≤ m ∧ 1 ≤ m ∧ ∃ R : ℕ, R₁ ≤ R ∧
      TorusOK ell (ell ^ m) (neLu (ell ^ m) R) ∧
      Admissible ell (ell ^ m) R 2 (neS ell (ell ^ m) R) ∧
      LambdaOK2 ell (ell ^ m) R 2 (neS ell (ell ^ m) R) (neLam (ell ^ m) R) ∧
      CovSitesF ell (ell ^ m)
        (constFam (9 * ell + 1) (scaleUp ell 2 (neLu (ell ^ m) R))) 2 (neS ell (ell ^ m) R) ∧
      ¬ CovPlaqF ell (ell ^ m)
        (constFam (9 * ell + 1) (scaleUp ell 2 (neLu (ell ^ m) R))) 2 (neS ell (ell ^ m) R) ∧
      ∀ a₀ : ℝ, 0 < a₀ → ∃ α₀ : ℝ, 0 < α₀ ∧
        ((9 * ell + 1 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
        ∀ t : ℝ, PerCubeRegularF ell (ell ^ m)
          (constFam (9 * ell + 1) (scaleUp ell 2 (neLu (ell ^ m) R)))
          2 (neS ell (ell ^ m) R) α₀ ((ell : ℝ) ^ 2)⁻¹
          (oddCfg ell (soC ell (ell ^ m) R (9 * ell + 1)) t) := by
  letI : CfData := thinWidth
  let m := max m₁ 1
  let R := max R₁ (9 * ell + 1)
  have hm : m₁ ≤ m := le_max_left _ _
  have hm1 : 1 ≤ m := le_max_right _ _
  have hRR : R₁ ≤ R := le_max_left _ _
  have hRc : 9 * ell + 1 ≤ R := le_max_right _ _
  have hR : 1 ≤ R := by omega
  have hell2 : 2 ≤ ell := by omega
  have hell0 : 0 < ell := by omega
  have hM : 0 < ell ^ m := pow_pos hell0 _
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega)
  have hc := (arithmetic_window ell hell).1
  have hrel : SoRel ell (9 * ell + 1) := (arithmetic_window ell hell).2
  obtain ⟨hcs, hnp⟩ := sites_not_imp_plaq_S hell2 hM hR hrel hc hRc
  refine ⟨m, hm, hm1, R, hRR, torusOK_ne_two hell2 hdvd hM,
    ne_admissible_two hell2 hM hR, lambdaOK2_ne_two hell2 hdvd hM hR, hcs, hnp, ?_⟩
  intro a₀ ha₀
  have hcR : (0 : ℝ) < ((9 * ell + 1 : ℕ) : ℝ) := by positivity
  have hMR : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by exact_mod_cast hM
  let α₀ := a₀ / (((9 * ell + 1 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ))
  have hα : 0 < α₀ := by positivity
  refine ⟨α₀, hα, ?_, ?_⟩
  · dsimp [α₀]
    rw [mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)]
  · intro t
    exact perCubeRegularF_constFam_iff.mpr
      (sliceCfg_class hell2 hM hR hrel hc (fun x => t * (oddProfile ell x : ℝ)) hα)

/-- The zero member is exactly the genuine flat background. -/
theorem oddCfg_zero {L : PeriodicLatticeExtent} (ell C : ℕ) :
    oddCfg (L := L) ell C 0 = flatCfg := by
  letI : CfData := ⟨10, by norm_num⟩
  funext e
  simp [oddCfg, sliceCfg, cartan_zero, flatCfg]

/-- Flat-point guard non-vacuity works at odd scales too; it is NOT a guard
certificate at a nonzero parameter or a whole-path analyticity theorem. -/
theorem oddCfg_zero_wellDefG [CfData] {ell M R C : ℕ} (hell : 2 ≤ ell)
    (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) {a : ℝ} (ha : 0 < a) :
    GenP.WellDefG (gparams ell 2 (neLu M R) (by omega) (neS ell M R)
      (oddCfg ell C 0) a (neLam M R)) := by
  let P := gparams ell 2 (neLu M R) (by omega) (neS ell M R)
    (oddCfg ell C 0) a (neLam M R)
  have hU : P.U = flatCfg := oddCfg_zero ell C
  have hunitBg : P.unitBgU = flatCfg := by
    unfold IngrBParams.unitBgU
    rw [show bgTower P.G P.U P.k = flatCfg by
      unfold bgTower
      rw [hU]
      exact Ubar_flat P.ell P.k]
    rfl
  have hH : Function.Bijective (H0 P.Lam P.Q1) := by
    unfold IngrBParams.Q1
    rw [hunitBg]
    exact H0_flat_bijective (by omega) (unit_hdiv hdvd hM) (neLam M R)
  have hu : UnitsFour P := by
    have hz : oddCfg (L := scaleUp ell 2 (neLu M R)) ell C 0 = stag0Cfg C 0 := by
      rw [oddCfg_zero, stag0Cfg_zero]
      rfl
    dsimp [P]
    rw [hz]
    exact SitesOnly.unitsFour_flat_two hell hdvd hM hR a ha
  have hd : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)) :=
    delpA_unit (geomOf ell 2 (neS ell M R)) (oddCfg ell C 0) ha hell
      (out_nested_two hell hM hR)
  exact ⟨⟨hH, hu.1, hu.2.1⟩, hd, hu.2.2.1, hu.2.2.2⟩

/-- The purely geometric proof route would need this eventual upgrade. -/
def EventualCoverageUpgrade (ell c : ℕ) : Prop :=
  ∃ m₁ R₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R →
    ∀ k : ℕ, 1 ≤ k → ∀ Lu : PeriodicLatticeExtent, TorusOK ell (ell ^ m) Lu →
      ∀ S : Tower (scaleUp ell k Lu), Admissible ell (ell ^ m) R k S →
        CovSitesF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S →
          CovPlaqF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S

/-- A proof from Total cannot merely recover the missing coverage by large radii.
This does not exclude an analytic or guard-sensitive positive proof. -/
theorem no_eventual_geometric_upgrade (ell : ℕ) (hell : 3 ≤ ell) :
    ¬ EventualCoverageUpgrade ell (9 * ell + 1) := by
  rintro ⟨m₁, R₁, h⟩
  letI : CfData := thinWidth
  obtain ⟨m, hm, _hm1, R, hR, hT, hA, _hL, hcs, hnp, _hreg⟩ :=
    oddCfg_cofinal_class ell hell m₁ R₁
  exact hnp (h m hm R hR 2 (by norm_num) (neLu (ell ^ m) R) hT
    (neS ell (ell ^ m) R) hA hcs)

/-- Exact holonomy weight, before any Hessian or constrained-inverse reduction. -/
theorem oddCfg_holCos_01 {L : PeriodicLatticeExtent} (ell C : ℕ) (t : ℝ)
    (x : PeriodicLatticeSite L) (hx : (x 0).val = C)
    (h : ((0 : Fin 3), (1 : Fin 3)).1 < ((0 : Fin 3), (1 : Fin 3)).2) :
    holCos (oddCfg (L := L) ell C t) (x, ⟨((0 : Fin 3), (1 : Fin 3)), h⟩) =
      Real.cos (t * ((oddProfile ell (x 1).val : ℝ) -
        (oddProfile ell ((periodicLatticeShift x 1) 1).val : ℝ))) := by
  letI : CfData := ⟨10, by norm_num⟩
  have he := sliceCfg_holonomy_01 C (fun y => t * (oddProfile ell y : ℝ)) x h
  rw [if_pos hx] at he
  have hw := holCos_of_eq_cartan he
  simpa only [oddCfg, mul_sub] using hw

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
#print axioms sliceCfg_class
#print axioms sliceCfg_holonomy_01
#print axioms thinWidth
#print axioms arithmetic_window
#print axioms oddCfg_cofinal_class
#print axioms oddCfg_zero
#print axioms oddCfg_zero_wellDefG
#print axioms EventualCoverageUpgrade
#print axioms no_eventual_geometric_upgrade
#print axioms oddCfg_holCos_01

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


namespace AdalyFormal.Round7.S4OddSites.R2

open Finset Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.CoverOmega.Struct
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NcwdhTwo
open AdalyFormal.SitesOnly
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge UbarTower UbarTower_succ UbarTower_zero)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Round7.S4OddSites.Partial
open AdalyFormal.Round7.S4OddSites.R1
open MXQ.AllC
open NcwdhFam

/-- Exact unit background, not an inverse certificate. -/
theorem oddCfg_unitBg_eq_flat [CfData] {ell : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) (hodd : ell % 2 = 1) (C : ℕ)
    (hN0 : ell ≤ scaleUp ell 2 Lu 0 + 1) (t : ℝ) (ht : |t| < Real.pi / 2) :
    unitBg ell 2 Lu hell
      (UbarTower su2LogExp ell (oddCfg (L := scaleUp ell 2 Lu) ell C t) 2) = flatCfg := by
  have h := oddCfg_unitBg_temporal hell hodd C hN0 t ht
  funext e
  obtain ⟨x, μ⟩ := e
  obtain ⟨h0, h1, h2⟩ := h x (fun _ => one_dvd _)
  fin_cases μ
  · simpa [flatCfg, cartan_zero] using h0
  · exact h1
  · exact h2

/-- Generic linear Cartan family representation of the actual profile. -/
def oddAngles {L : PeriodicLatticeExtent} (ell C : ℕ) : PeriodicLatticeEdge L → ℝ :=
  fun e => if (e.1 0).val = C ∧ e.2 = 0 then (oddProfile ell (e.1 1).val : ℝ) else 0

theorem oddCfg_eq_cartanOf {L : PeriodicLatticeExtent} (ell C : ℕ) (t : ℝ) :
    oddCfg (L := L) ell C t = cartanOf (t • oddAngles ell C) := by
  funext e
  simp only [oddCfg, sliceCfg, cartanOf, oddAngles, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp [cartan_zero]

theorem blockAngG_smul' {L : PeriodicLatticeExtent} (s ell : ℕ) (t : ℝ)
    (θ : PeriodicLatticeEdge L → ℝ) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    blockAngG s ell (t • θ) x μ = t * blockAngG s ell θ x μ := by
  simp only [blockAngG, loopAngG_smul, pathAngG_smul, ← Finset.mul_sum]
  ring

/-- Only a neighbourhood of zero is claimed; its size may depend on the torus. -/
theorem cartan_loops_near_zero {L : PeriodicLatticeExtent} (s ell : ℕ)
    (θ : PeriodicLatticeEdge L → ℝ) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ c : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf c.1 s ell,
      |loopAngG s ell (t • θ) c.1 c.2 x| < Real.pi := by
  rw [Filter.eventually_all]
  intro c
  rw [Filter.eventually_all_finset]
  intro x _hx
  simp only [loopAngG_smul]
  exact ((continuous_id.mul continuous_const).abs.continuousAt (x := (0 : ℝ))).eventually
    (gt_mem_nhds (by simpa using Real.pi_pos))

/-- The actual first blocked family is analytic at zero, without an evenness premise. -/
theorem cartan_bg1_ana_zero [CfData] {L : PeriodicLatticeExtent} (ell : ℕ)
    (θ : PeriodicLatticeEdge L → ℝ) :
    AnaFam (fun t : ℝ => UbarTower su2LogExp ell (cartanOf (t • θ)) 1) 0 := by
  intro e
  have he : (fun t : ℝ => ((UbarTower su2LogExp ell (cartanOf (t • θ)) 1 e : SU2) : M2))
      =ᶠ[𝓝 0] (fun t : ℝ => ((cartan (t * blockAngG 1 ell θ e.1 e.2) : SU2) : M2)) := by
    filter_upwards [cartan_loops_near_zero 1 ell θ] with t ht
    simp only [UbarTower_succ, UbarTower_zero, pow_zero]
    rw [sbg_cartanOf 1 ell _ e.1 e.2 (ht e), blockAngG_smul']
  exact (SGat_cartan (contDiffAt_id.mul contDiffAt_const)).congr_of_eventuallyEq he

/-- Actual level-zero and level-one jet regularity and analyticity at zero. -/
theorem oddCfg_towerOK_zero [CfData] {ell : ℕ} {Lu : PeriodicLatticeExtent}
    (S : Tower (scaleUp ell 2 Lu)) (C : ℕ) :
    TowerOK (geomOf ell 2 S) (fun t => oddCfg ell C t) 0 := by
  constructor
  · intro j hj
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · simp only [bgTower, UbarTower_zero, oddCfg_eq_cartanOf]
      exact AnaFam_cartanOf _ (fun e => contDiffAt_id.mul contDiffAt_const)
    · simp only [bgTower, oddCfg_eq_cartanOf]
      exact cartan_bg1_ana_zero ell (oddAngles ell C)
  · intro j _hj
    rw [oddCfg_zero]
    have he : bgTower (geomOf ell 2 S) flatCfg j = flatCfg := by
      exact Ubar_flat ell j
    rw [he]
    exact RegBg2_of_RegBg (RegBg_flat (ell ^ j) ell)

/-- Full inverse guard for genuinely nonzero parameters near zero. This is local
in the chosen finite geometry, not a certificate near a spectral crossing. -/
theorem oddCfg_wellDefG_near_zero [CfData] {ell M R C : ℕ} (hell : 2 ≤ ell)
    (hodd : ell % 2 = 1) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R)
    {a : ℝ} (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      GenP.WellDefG (gparams ell 2 (neLu M R) (by omega) (neS ell M R)
        (oddCfg ell C t) a (neLam M R)) := by
  let F := fun t : ℝ => DstructP (gparams ell 2 (neLu M R) (by omega)
    (neS ell M R) (oddCfg ell C t) a (neLam M R))
  have hT := oddCfg_towerOK_zero (neS ell M R) C
  have hU : LinkEA (fun t => oddCfg (L := scaleUp ell 2 (neLu M R)) ell C t) 0 :=
    LinkEA_of_AnaFam (hT.1 0 (by norm_num))
  have hJ := JfOf_analytic hU (plaqIn (geomOf ell 2 (neS ell M R)).Om0)
  have hout := out_nested_two hell hM hR
  have hF : AnalyticAt ℝ F 0 :=
    DstructG_analytic (geomOf ell 2 (neS ell M R)) (fun t => oddCfg ell C t)
      hT (le_refl 2) ha hell hout _ hJ
  have hW0 := oddCfg_zero_wellDefG (C := C) hell hdvd hM hR ha
  have hU0 : UnitsFour (gparams ell 2 (neLu M R) (by omega) (neS ell M R)
      (oddCfg ell C 0) a (neLam M R)) :=
    ⟨hW0.1.2.1, hW0.1.2.2, hW0.2.2.1, hW0.2.2.2⟩
  have hF0 : F 0 ≠ 0 := (DstructP_ne_iff _ hout).mpr
    ⟨gOf_ne_zero_two hell hM hR _, hU0⟩
  have hnz : ∀ᶠ t in 𝓝 0, F t ≠ 0 := hF.continuousAt.eventually_ne hF0
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| < Real.pi / 2 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using half_pos Real.pi_pos)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp (hnz.and hsmall)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have ht' := hδ' (by simpa [Real.dist_eq] using ht)
  have hu := ((DstructP_ne_iff _ hout).mp ht'.1).2
  have hH := oddCfg_H0_bijective hell hodd hdvd hM t a ht'.2
  exact ⟨⟨hH, hu.1, hu.2.1⟩,
    delpA_unit (geomOf ell 2 (neS ell M R)) (oddCfg ell C t) ha hell hout,
    hu.2.2.1, hu.2.2.2⟩

#print axioms oddCfg_unitBg_eq_flat
#print axioms oddAngles
#print axioms oddCfg_eq_cartanOf
#print axioms blockAngG_smul'
#print axioms cartan_loops_near_zero
#print axioms cartan_bg1_ana_zero
#print axioms oddCfg_towerOK_zero
#print axioms oddCfg_wellDefG_near_zero

end AdalyFormal.Round7.S4OddSites.R2
