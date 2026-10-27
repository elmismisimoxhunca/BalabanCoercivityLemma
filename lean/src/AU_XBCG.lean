import AU_BCG
import AC_SK1
import AC_BLC8
import AU_BLC6
import AC_Base
import AC_OG8
import BallCharts

/-!
# AU_XBCG -- `ClassFamX`, `BallChartsGX` (lane allc_20261016, uniform-in-c route, constants before `fc`)

`ClassFamX ell Cs Q P` : the shape of `ClassFamAC ell fc Cs Q P`, with the thresholds `m1`, `R1`, the constants `c : Cs` and the smallness `s` chosen BEFORE the cube factor `fc >= 10`.
`ballChartsGX : BallChartsGX` : proved from `ball_chart_zeroAC` (j = 0) and `ball_chart_posU` (j >= 1; vertex scale `b_{j-2}`), `m1 = 5`, `R1 = 45 ell + 30`;
`C = ell^2 CC(ell^2, ell^m) + 56 ell^m`.
`ballChartsX_of_G` : the RegionChart form (copy of `ballCharts0_of_G`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false

namespace AdalyFormal.M2Skel

open AdalyFormal.AllC
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp OnLambdaTildeIn TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled OnLambdaT)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- the common shape of the open inputs, thresholds `m1`, `R1` BEFORE the cube factor. -/
def ClassFamX (ell : ℕ) (Cs : Type)
    (Q : ℕ → ℕ → Cs → Prop)
    (P : ∀ (M R k : ℕ) (Lu : PeriodicLatticeExtent), Cs → Tower (scaleUp ell k Lu) → Set (PeriodicLatticeSite Lu) →
      LinkCfg (scaleUp ell k Lu) → ℝ → Prop) : Prop :=
  ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → ∃ c : Cs, Q (ell ^ m) R c ∧ ∃ s : ℝ, 0 < s ∧ ∀ fc : ℕ, 10 ≤ fc →
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupledH ell (ell ^ m) fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) fc k S e → U e = 1) →
      P (ell ^ m) R k Lu c S Lam U α₀

end AdalyFormal.M2Skel

namespace AdalyFormal.AllC

section t0
open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2 AdalyFormal.M2GlueGeo
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.M2BallCharts
open AdalyFormal.M2Skel (ClassFamX)
open AdalyFormal.OneGap

def BallChartsGX : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamX ell ℝ (fun _ _ C => 1 ≤ C) (fun M _ k _ C S Lam U α₀ =>
      BallChartsAtG ell M k S U C α₀ ((ell : ℝ) ^ k)⁻¹)

def BallChartsX : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFamX ell ℝ (fun _ _ C => 1 ≤ C) (fun M _ k _ C S Lam U α₀ =>
      BallChartsAt ell M k S U C α₀ ((ell : ℝ) ^ k)⁻¹)

theorem ballChartsGX : BallChartsGX := by
  intro ell hell
  refine ⟨5, fun m hm => ⟨45 * ell + 30, fun R hR => ?_⟩⟩
  have hM32 : 32 ≤ ell ^ m := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      _ ≤ ell ^ m := Nat.pow_le_pow_left hell m
  have hM0 : 0 < ell ^ m := by omega
  have hMr : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by exact_mod_cast hM0
  obtain ⟨-, -, -, -, -, -, c7, c8⟩ := consts_nonneg (ell ^ 2) (ell ^ m)
  have hell0 : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hCC : 1 ≤ CC (ell ^ 2) (ell ^ m) := by unfold CC; linarith
  refine ⟨(ell : ℝ) ^ 2 * CC (ell ^ 2) (ell ^ m) + 56 * ((ell ^ m : ℕ) : ℝ), ?_,
    min (Xthr (ell ^ 2) (ell ^ m)) (1 / 2), lt_min (Xthr_pos (ell ^ 2) (ell ^ m) hM0) (by norm_num), ?_⟩
  · have : (1 : ℝ) ≤ (ell : ℝ) ^ 2 := one_le_pow₀ hl1
    nlinarith
  intro fc hfc
  haveI : CubeFactor fc := ⟨hfc⟩
  intro k hk Lu α₀ hα hsα hT S hS Lam hLam U hcc hU1 j hjk w hw r hr7 hnw hin hout hsm
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  set X : ℝ := (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hcast : (((12 : ℕ) : ℝ)) = (12 : ℝ) := by norm_num
  have hl2 : (1 : ℝ) ≤ (ell : ℝ) ^ 2 := one_le_pow₀ hl1
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · -- j = 0
    subst hj0
    have hr7' : r ≤ 7 * ell ^ m := by simpa using hr7
    have hin' : ∀ x ∈ Ball w r, x ∈ S.Om 0 := hin
    obtain ⟨g, hg⟩ := ball_chart_zeroAC (R := R) hcc.1 (by omega) hr7' hnw hin' hη hα.le hcc.2
      (hsα.trans (min_le_right _ _))
    have h56 : 0 ≤ (ell : ℝ) ^ 2 * CC (ell ^ 2) (ell ^ m) := by positivity
    refine ⟨g, hg.mono subset_rfl ?_ ?_⟩
    · simp only [Nat.zero_sub, pow_zero, inv_one, mul_one, hcast]
      rw [← hXdef]; nlinarith
    · simp only [Nat.zero_sub, pow_zero, inv_one, one_pow, mul_one, hcast]
      rw [← hXdef]; nlinarith
  · -- j ≥ 1
    obtain ⟨x0, hx0, hwx⟩ := hw
    obtain ⟨g, hg⟩ := ball_chart_posU hS hcc.1 hell (by omega) hj1 hjk hx0 hwx hr7 hnw hR hη hα.le hcc.2
      (hsα.trans (min_le_left _ _))
    have hu := u_comp (ell := ell) (j := j) (by omega) hj1
    have hu0 : 0 ≤ ((ell : ℝ) ^ (j - 1))⁻¹ := by positivity
    have hu0' : 0 ≤ ((ell : ℝ) ^ (j - 2))⁻¹ := by positivity
    have hCCnn : 0 ≤ CC (ell ^ 2) (ell ^ m) := by linarith
    refine ⟨g, hg.mono subset_rfl ?_ ?_⟩
    · rw [hcast, ← hXdef]
      have h56 : 0 ≤ 56 * ((ell ^ m : ℕ) : ℝ) := by positivity
      have e1 : CC (ell ^ 2) (ell ^ m) * (X * ((ell : ℝ) ^ (j - 2))⁻¹)
          ≤ CC (ell ^ 2) (ell ^ m) * (X * ((ell : ℝ) * ((ell : ℝ) ^ (j - 1))⁻¹)) := by gcongr
      have e2 : CC (ell ^ 2) (ell ^ m) * (X * ((ell : ℝ) * ((ell : ℝ) ^ (j - 1))⁻¹))
          ≤ (ell : ℝ) ^ 2 * CC (ell ^ 2) (ell ^ m) * (X * ((ell : ℝ) ^ (j - 1))⁻¹) := by
        have hpos : 0 ≤ CC (ell ^ 2) (ell ^ m) * (X * ((ell : ℝ) ^ (j - 1))⁻¹) := by positivity
        nlinarith [mul_nonneg hpos (sub_nonneg.2 (show (ell : ℝ) ≤ (ell : ℝ) ^ 2 by nlinarith))]
      have : 0 ≤ X * ((ell : ℝ) ^ (j - 1))⁻¹ := by positivity
      have e3 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ * ((ell : ℝ) ^ (j - 1))⁻¹ = X * ((ell : ℝ) ^ (j - 1))⁻¹ := rfl
      rw [e3]; nlinarith
    · rw [hcast, ← hXdef]
      have h56 : 0 ≤ 56 * ((ell ^ m : ℕ) : ℝ) := by positivity
      have hu2 : (((ell : ℝ) ^ (j - 2))⁻¹) ^ 2 ≤ ((ell : ℝ) * ((ell : ℝ) ^ (j - 1))⁻¹) ^ 2 :=
        pow_le_pow_left₀ hu0' hu 2
      have e1 : CC (ell ^ 2) (ell ^ m) * (X * (((ell : ℝ) ^ (j - 2))⁻¹) ^ 2)
          ≤ CC (ell ^ 2) (ell ^ m) * (X * ((ell : ℝ) * ((ell : ℝ) ^ (j - 1))⁻¹) ^ 2) := by gcongr
      have e2 : CC (ell ^ 2) (ell ^ m) * (X * ((ell : ℝ) * ((ell : ℝ) ^ (j - 1))⁻¹) ^ 2)
          = (ell : ℝ) ^ 2 * CC (ell ^ 2) (ell ^ m) * (X * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2) := by ring
      have : 0 ≤ X * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2 := by positivity
      have e3 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2 = X * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2 := rfl
      rw [e3]; nlinarith

end t0

end AdalyFormal.AllC


namespace AdalyFormal.AllC
section t1
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK pdist HT CubeBond)
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log)
open AdalyFormal.M2Skel (ClassFamX)
open AdalyFormal.M2Glue2 (GChart chA chA_HT chA_exp frobNorm_chA chA_sub log_le log_lip)
open AdalyFormal.Balaban.Bch2 (frobNorm_smul)
open AdalyFormal.Balaban.RegularityGap (frobNorm_negI_smul)
open AdalyFormal.OneGap
theorem ballChartsX_of_G (hG : BallChartsGX) : BallChartsX := by
  intro ell hell
  obtain ⟨m₁, hm⟩ := hG ell hell
  refine ⟨m₁, fun m hm1 => ?_⟩
  obtain ⟨R₁, hR⟩ := hm m hm1
  refine ⟨R₁, fun R hR1 => ?_⟩
  obtain ⟨C, hC, s, hs, hf⟩ := hR R hR1
  have hpi := Real.pi_pos
  have hC0 : 0 < C := by linarith
  refine ⟨(Real.pi / 2) * C + 1, by nlinarith, min s (1 / C), lt_min hs (by positivity), ?_⟩
  intro fc hfc
  haveI : CubeFactor fc := ⟨hfc⟩
  intro k hk Lu α₀ hα hsα hT S hS Lam hLam U hcc hU1 j hjk w hw r hr7 hnw hin hout hsm
  have hs1 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s := hsα.trans (min_le_left _ _)
  have hs2 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ 1 / C := hsα.trans (min_le_right _ _)
  obtain ⟨g, hg⟩ := hf fc hfc k hk Lu α₀ hα hs1 hT S hS Lam hLam U hcc hU1 j hjk w hw r hr7 hnw hin hout hsm
  have hell0 : 0 < ell := by omega
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  set a0 : ℝ := ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ with ha0
  have ha0pos : 0 < a0 := by
    have : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by
      have : 0 < ell ^ m := pow_pos hell0 m
      exact_mod_cast this
    rw [ha0]; positivity
  have hX : ((ell : ℝ) ^ (j - 1))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ (by exact_mod_cast hell0)
  have hX0 : 0 < ((ell : ℝ) ^ (j - 1))⁻¹ := by positivity
  have hCa : C * a0 ≤ 1 := by
    have : a0 ≤ 1 / C := by
      rw [ha0]
      have e : ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ = (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ := by norm_num
      rw [e]; exact hs2
    rw [le_div_iff₀ hC0] at this; linarith
  refine regionChart_of_gchart (f := 12) (α := ((Real.pi / 2) * C + 1) * α₀) hell0 hη ?_ hg ?_ ?_
  · calc C * (a0 * ((ell : ℝ) ^ (j - 1))⁻¹) ≤ C * (a0 * 1) := by gcongr
      _ ≤ 1 := by linarith
  · have e : (12 : ℕ) * ((ell ^ m : ℕ) : ℝ) * (((Real.pi / 2) * C + 1) * α₀)
        = ((Real.pi / 2) * C + 1) * a0 := by rw [ha0]; ring
    rw [e]
    have : 0 < a0 * ((ell : ℝ) ^ (j - 1))⁻¹ := by positivity
    nlinarith
  · have e : (12 : ℕ) * ((ell ^ m : ℕ) : ℝ) * (((Real.pi / 2) * C + 1) * α₀)
        = ((Real.pi / 2) * C + 1) * a0 := by rw [ha0]; ring
    rw [e]
    have : 0 < a0 * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2 := by positivity
    nlinarith


end t1
end AdalyFormal.AllC

#print axioms AdalyFormal.AllC.ballChartsGX
#print axioms AdalyFormal.AllC.ballChartsX_of_G
