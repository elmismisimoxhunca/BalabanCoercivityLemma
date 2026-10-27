import OG7

/-!
# OG13 -- numerics of the per-row chart hypothesis of W6 (lane m2_onegap_20261015)

`epsC ell ρ j' l` : the GUARDED closeness (`0` for `l ≥ j'`) `ℓ^l ρ/ℓ^{j'-2} + 3π ℓ^{2l} ρ/ℓ^{2(j'-2)}` (`W6.clsEps` is the same expression WITHOUT the guard; its hypotheses
`rhoOf (clsEps j' l) < π/2` for ALL `j', l < k` cannot hold for `k` large, since `clsEps 0 l ~ ℓ^l ρ`; `ChartHyp` reads `ε j' l` only for `l < j'`).
`numerics_epsC` : there is `ρs(ℓ) > 0` such that for `0 ≤ ρ ≤ ρs`, the five numerical premises of `qs_injective_charts` hold for `ε = epsC ell ρ`, with a `k`-free level sum `SstarC ell ρ`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.OneGap

open Finset
open AdalyFormal.NonflatJet (rhoOf r0 r0_pos rhoOf_le)
open AdalyFormal.BondComposite (thetaOf rr)
open AdalyFormal.TowerLoc (Ctheta theta_le geom_le delStar)
open AdalyFormal.W6 (CE CE_pos)
open AdalyFormal.M2W6 (CsrcS CsrcA CsrcT mult0)
open SmallnessBridge.Assemble (loopFactorBound)

noncomputable def epsC (ell : ℕ) (ρ : ℝ) (j' l : ℕ) : ℝ :=
  if l < j' then (ell : ℝ) ^ l * (ρ / (ell : ℝ) ^ (j' - 2)) + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ l * (ρ / (ell : ℝ) ^ (2 * (j' - 2)))) else 0

/-- the `k`-free level-sum bound -/
noncomputable def SstarC (ell : ℕ) (ρ : ℝ) : ℝ := Ctheta * (ell : ℝ) ^ 2 * (2 * ((ell : ℝ) ^ 2 * ((1 + 3 * Real.pi) * ρ)))

theorem epsC_nonneg (ell : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (j' l : ℕ) : 0 ≤ epsC ell ρ j' l := by
  unfold epsC
  have := Real.pi_pos
  split_ifs <;> positivity

theorem pow_le_aux (ell : ℕ) (hell : 1 ≤ ell) {j' l : ℕ} (hl : l < j') :
    (ell : ℝ) ^ l ≤ (ell : ℝ) * (ell : ℝ) ^ (j' - 2) ∧ ((ell : ℝ) ^ 2) ^ l ≤ (ell : ℝ) ^ 2 * (ell : ℝ) ^ (2 * (j' - 2)) := by
  have h1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  constructor
  · calc (ell : ℝ) ^ l ≤ (ell : ℝ) ^ ((j' - 2) + 1) := pow_le_pow_right₀ h1 (by omega)
      _ = (ell : ℝ) * (ell : ℝ) ^ (j' - 2) := by rw [pow_succ]; ring
  · rw [← pow_mul]
    calc (ell : ℝ) ^ (2 * l) ≤ (ell : ℝ) ^ (2 + 2 * (j' - 2)) := pow_le_pow_right₀ h1 (by omega)
      _ = (ell : ℝ) ^ 2 * (ell : ℝ) ^ (2 * (j' - 2)) := by rw [pow_add]

theorem epsC_le (ell : ℕ) (hell : 1 ≤ ell) {ρ : ℝ} (hρ : 0 ≤ ρ) (j' l : ℕ) :
    epsC ell ρ j' l ≤ (ell : ℝ) ^ 2 * ((1 + 3 * Real.pi) * ρ) := by
  unfold epsC
  have hpi := Real.pi_pos
  have h1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  split_ifs with hl
  · obtain ⟨a1, a2⟩ := pow_le_aux ell hell hl
    have hP : (0 : ℝ) < (ell : ℝ) ^ (j' - 2) := by positivity
    have hP2 : (0 : ℝ) < (ell : ℝ) ^ (2 * (j' - 2)) := by positivity
    have e1 : (ell : ℝ) ^ l * (ρ / (ell : ℝ) ^ (j' - 2)) ≤ (ell : ℝ) * ρ := by
      rw [← mul_div_assoc, div_le_iff₀ hP]
      calc (ell : ℝ) ^ l * ρ ≤ ((ell : ℝ) * (ell : ℝ) ^ (j' - 2)) * ρ := mul_le_mul_of_nonneg_right a1 hρ
        _ = (ell : ℝ) * ρ * (ell : ℝ) ^ (j' - 2) := by ring
    have e2 : ((ell : ℝ) ^ 2) ^ l * (ρ / (ell : ℝ) ^ (2 * (j' - 2))) ≤ (ell : ℝ) ^ 2 * ρ := by
      rw [← mul_div_assoc, div_le_iff₀ hP2]
      calc ((ell : ℝ) ^ 2) ^ l * ρ ≤ ((ell : ℝ) ^ 2 * (ell : ℝ) ^ (2 * (j' - 2))) * ρ := mul_le_mul_of_nonneg_right a2 hρ
        _ = (ell : ℝ) ^ 2 * ρ * (ell : ℝ) ^ (2 * (j' - 2)) := by ring
    have h2 : (ell : ℝ) ≤ (ell : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h2 hρ]
  · positivity

theorem sum_epsC (ell : ℕ) (hell2 : 2 ≤ ell) {ρ : ℝ} (hρ : 0 ≤ ρ) (j' : ℕ) :
    ∑ l ∈ range j', epsC ell ρ j' l ≤ 2 * ((ell : ℝ) ^ 2 * ((1 + 3 * Real.pi) * ρ)) := by
  have hpi := Real.pi_pos
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell2
  have hnn : 0 ≤ 2 * ((ell : ℝ) ^ 2 * ((1 + 3 * Real.pi) * ρ)) := by positivity
  rcases Nat.eq_zero_or_pos j' with rfl | hj
  · simp; positivity
  have hP : (0 : ℝ) < (ell : ℝ) ^ (j' - 2) := by positivity
  have hP2 : (0 : ℝ) < (ell : ℝ) ^ (2 * (j' - 2)) := by positivity
  have hsplit : ∑ l ∈ range j', epsC ell ρ j' l
      = (ρ / (ell : ℝ) ^ (j' - 2)) * ∑ l ∈ range j', (ell : ℝ) ^ l
        + 3 * Real.pi * ((ρ / (ell : ℝ) ^ (2 * (j' - 2))) * ∑ l ∈ range j', ((ell : ℝ) ^ 2) ^ l) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    unfold epsC
    rw [if_pos (Finset.mem_range.mp hl)]
    ring
  rw [hsplit]
  have g1 := geom_le (ell : ℝ) hellR j' hj
  have g2 := geom_le (((ell : ℝ) ^ 2)) (by nlinarith) j' hj
  have e2 : ((ell : ℝ) ^ 2) ^ (j' - 1) = (ell : ℝ) ^ (2 * (j' - 1)) := by rw [← pow_mul]
  rw [e2] at g2
  have h1 : (ell : ℝ) ^ (j' - 1) ≤ (ell : ℝ) * (ell : ℝ) ^ (j' - 2) := by
    calc (ell : ℝ) ^ (j' - 1) ≤ (ell : ℝ) ^ ((j' - 2) + 1) := pow_le_pow_right₀ (by linarith) (by omega)
      _ = (ell : ℝ) * (ell : ℝ) ^ (j' - 2) := by rw [pow_succ]; ring
  have h2 : (ell : ℝ) ^ (2 * (j' - 1)) ≤ (ell : ℝ) ^ 2 * (ell : ℝ) ^ (2 * (j' - 2)) := by
    calc (ell : ℝ) ^ (2 * (j' - 1)) ≤ (ell : ℝ) ^ (2 + 2 * (j' - 2)) := pow_le_pow_right₀ (by linarith) (by omega)
      _ = (ell : ℝ) ^ 2 * (ell : ℝ) ^ (2 * (j' - 2)) := by rw [pow_add]
  have a1 : (ρ / (ell : ℝ) ^ (j' - 2)) * ∑ l ∈ range j', (ell : ℝ) ^ l ≤ 2 * ((ell : ℝ) * ρ) := by
    calc _ ≤ (ρ / (ell : ℝ) ^ (j' - 2)) * (2 * ((ell : ℝ) * (ell : ℝ) ^ (j' - 2))) :=
          mul_le_mul_of_nonneg_left (g1.trans (by linarith)) (by positivity)
      _ = 2 * ((ell : ℝ) * ρ) := by field_simp
  have a2 : (ρ / (ell : ℝ) ^ (2 * (j' - 2))) * ∑ l ∈ range j', ((ell : ℝ) ^ 2) ^ l ≤ 2 * ((ell : ℝ) ^ 2 * ρ) := by
    calc _ ≤ (ρ / (ell : ℝ) ^ (2 * (j' - 2))) * (2 * ((ell : ℝ) ^ 2 * (ell : ℝ) ^ (2 * (j' - 2)))) :=
          mul_le_mul_of_nonneg_left (g2.trans (by linarith)) (by positivity)
      _ = 2 * ((ell : ℝ) ^ 2 * ρ) := by field_simp
  have hl2 : (ell : ℝ) ≤ (ell : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hl2 hρ]

theorem sum_theta_epsC (ell : ℕ) (hell2 : 2 ≤ ell) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsm : (ell : ℝ) ^ 2 * ((1 + 3 * Real.pi) * ρ) ≤ 1 / (1000 * (ell : ℝ) ^ 4)) (j' : ℕ) :
    ∑ l ∈ range j', thetaOf ell (epsC ell ρ j' l) ≤ SstarC ell ρ := by
  have hell : 0 < ell := by omega
  have hC : 0 ≤ Ctheta := by unfold Ctheta; positivity
  calc ∑ l ∈ range j', thetaOf ell (epsC ell ρ j' l)
      ≤ ∑ l ∈ range j', Ctheta * (ell : ℝ) ^ 2 * epsC ell ρ j' l :=
        Finset.sum_le_sum (fun l _ => theta_le ell hell _ (epsC_nonneg ell hρ j' l)
          ((epsC_le ell (by omega) hρ j' l).trans hsm))
    _ = Ctheta * (ell : ℝ) ^ 2 * ∑ l ∈ range j', epsC ell ρ j' l := by rw [Finset.mul_sum]
    _ ≤ Ctheta * (ell : ℝ) ^ 2 * (2 * ((ell : ℝ) ^ 2 * ((1 + 3 * Real.pi) * ρ))) :=
        mul_le_mul_of_nonneg_left (sum_epsC ell hell2 hρ j') (by positivity)
    _ = SstarC ell ρ := rfl


theorem rr_pos (ell : ℕ) (hell : 0 < ell) : 0 < rr ell := by
  unfold rr
  have : (0 : ℝ) < ell := by exact_mod_cast hell
  positivity

theorem exists_Sstar_small (ell : ℕ) (hell : 0 < ell) :
    ∃ s : ℝ, 0 < s ∧ ∀ S : ℝ, 0 ≤ S → S ≤ s → 2 * CsrcS ell S * (1 + CsrcA ell S) < 1 := by
  have hrr := rr_pos ell hell
  have hCE := CE_pos
  have hm : 0 ≤ mult0 ell := by unfold mult0; positivity
  set K : ℝ := 54 * mult0 ell * CE * (5 + 162 * mult0 ell * CE) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨rr ell / (K + 1), by positivity, fun S hS0 hS1 => ?_⟩
  set t : ℝ := S / rr ell with ht
  have ht0 : 0 ≤ t := div_nonneg hS0 hrr.le
  have ht1 : t ≤ 1 / (K + 1) := by
    rw [ht, div_le_iff₀ hrr]
    calc S ≤ rr ell / (K + 1) := hS1
      _ = 1 / (K + 1) * rr ell := by ring
  have hK1 : 1 / (K + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have ht1' : t ≤ 1 := ht1.trans hK1
  have hexp : Real.exp t ≤ 3 := by
    have h1 : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.mpr ht1'
    have := Real.exp_one_lt_d9
    linarith
  have hexp0 : 0 < Real.exp t := Real.exp_pos t
  have hdel : delStar ell S ≤ 3 * t := by
    unfold delStar
    rw [← ht]
    nlinarith
  have hdel0 : 0 ≤ delStar ell S := by unfold delStar; rw [← ht]; positivity
  have hS2 : CsrcS ell S ≤ 27 * mult0 ell * CE * t ^ 2 := by
    unfold CsrcS
    have : delStar ell S ^ 2 ≤ 9 * t ^ 2 := by nlinarith
    calc mult0 ell * (3 * delStar ell S ^ 2 * CE) ≤ mult0 ell * (3 * (9 * t ^ 2) * CE) := by gcongr
      _ = 27 * mult0 ell * CE * t ^ 2 := by ring
  have hS0' : 0 ≤ CsrcS ell S := by unfold CsrcS; positivity
  have hT2 : CsrcT ell S ≤ 27 * mult0 ell * CE := by
    unfold CsrcT
    rw [← ht]
    have : Real.exp t ^ 2 ≤ 9 := by nlinarith
    calc mult0 ell * (3 * Real.exp t ^ 2 * CE) ≤ mult0 ell * (3 * 9 * CE) := by gcongr
      _ = 27 * mult0 ell * CE := by ring
  have hA : CsrcA ell S ≤ 4 + 162 * mult0 ell * CE := by
    unfold CsrcA
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    have : CsrcS ell S ≤ 27 * mult0 ell * CE := by
      calc CsrcS ell S ≤ 27 * mult0 ell * CE * t ^ 2 := hS2
        _ ≤ 27 * mult0 ell * CE * 1 := by gcongr
        _ = _ := by ring
    nlinarith
  have hA0 : 0 ≤ CsrcA ell S := by unfold CsrcA CsrcT; positivity
  have hfin : 2 * CsrcS ell S * (1 + CsrcA ell S) ≤ K * t ^ 2 := by
    calc 2 * CsrcS ell S * (1 + CsrcA ell S) ≤ 2 * (27 * mult0 ell * CE * t ^ 2) * (1 + (4 + 162 * mult0 ell * CE)) := by gcongr
      _ = K * t ^ 2 := by rw [hK]; ring
  have : K * t ^ 2 < 1 := by
    have h1 : K * t ^ 2 ≤ K * t := by
      have : t ^ 2 ≤ t := by nlinarith
      exact mul_le_mul_of_nonneg_left this hK0
    have h2 : K * t ≤ K / (K + 1) := by
      calc K * t ≤ K * (1 / (K + 1)) := mul_le_mul_of_nonneg_left ht1 hK0
        _ = K / (K + 1) := by ring
    have h3 : K / (K + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  linarith

theorem numerics_epsC (ell : ℕ) (hell2 : 2 ≤ ell) :
    ∃ ρs : ℝ, 0 < ρs ∧ ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ ρs →
      (∀ j' l : ℕ, rhoOf ell (epsC ell ρ j' l) < Real.pi / 2) ∧
      (∀ j' l : ℕ, Real.pi / 2 * ((loopFactorBound ell : ℝ) * epsC ell ρ j' l) < r0) ∧
      (∀ j' : ℕ, ∑ l ∈ range j', thetaOf ell (epsC ell ρ j' l) ≤ SstarC ell ρ) ∧
      2 * CsrcS ell (SstarC ell ρ) * (1 + CsrcA ell (SstarC ell ρ)) < 1 := by
  have hell : 0 < ell := by omega
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell2
  have hpi := Real.pi_pos
  have hr0 := r0_pos
  have hlfb : (0 : ℝ) ≤ (loopFactorBound ell : ℝ) := Nat.cast_nonneg _
  have hC : 0 < Ctheta := by unfold Ctheta; positivity
  obtain ⟨s, hs, hsm⟩ := exists_Sstar_small ell hell
  set Emax : ℝ := min (min (1 / (1000 * (ell : ℝ) ^ 4)) (r0 / (Real.pi * ((loopFactorBound ell : ℝ) + 1))))
    (s / (2 * Ctheta * (ell : ℝ) ^ 2 + 1)) with hEmax
  have hEpos : 0 < Emax := by
    rw [hEmax]
    exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hq : (0 : ℝ) < (ell : ℝ) ^ 2 * (1 + 3 * Real.pi) := by positivity
  refine ⟨Emax / ((ell : ℝ) ^ 2 * (1 + 3 * Real.pi)), by positivity, fun ρ hρ hρs => ?_⟩
  have hE : (ell : ℝ) ^ 2 * ((1 + 3 * Real.pi) * ρ) ≤ Emax := by
    have := (le_div_iff₀ hq).1 hρs
    nlinarith
  have hE1 : (ell : ℝ) ^ 2 * ((1 + 3 * Real.pi) * ρ) ≤ 1 / (1000 * (ell : ℝ) ^ 4) :=
    hE.trans (by rw [hEmax]; exact (min_le_left _ _).trans (min_le_left _ _))
  have hE2 : (ell : ℝ) ^ 2 * ((1 + 3 * Real.pi) * ρ) ≤ r0 / (Real.pi * ((loopFactorBound ell : ℝ) + 1)) :=
    hE.trans (by rw [hEmax]; exact (min_le_left _ _).trans (min_le_right _ _))
  have hE3 : (ell : ℝ) ^ 2 * ((1 + 3 * Real.pi) * ρ) ≤ s / (2 * Ctheta * (ell : ℝ) ^ 2 + 1) :=
    hE.trans (by rw [hEmax]; exact min_le_right _ _)
  have hE0 : 0 ≤ (ell : ℝ) ^ 2 * ((1 + 3 * Real.pi) * ρ) := by positivity
  refine ⟨fun j' l => ?_, fun j' l => ?_, fun j' => sum_theta_epsC ell hell2 hρ hE1 j', ?_⟩
  · have h0 := epsC_nonneg ell hρ j' l
    have h1 := rhoOf_le (ell := ell) _ h0
    have hle := (epsC_le ell (by omega) hρ j' l).trans hE1
    have hk : epsC ell ρ j' l * (ell : ℝ) ^ 4 ≤ 1 / 1000 := by
      have hpos : (0 : ℝ) < (ell : ℝ) ^ 4 := by positivity
      have := mul_le_mul_of_nonneg_right hle hpos.le
      calc _ ≤ 1 / (1000 * (ell : ℝ) ^ 4) * (ell : ℝ) ^ 4 := this
        _ = 1 / 1000 := by field_simp
    have h4 : (ell : ℝ) ≤ (ell : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((ell : ℝ) - 1), sq_nonneg ((ell : ℝ) ^ 2 - 1)]
    have h5 : (ell : ℝ) * epsC ell ρ j' l ≤ 1 / 1000 := by
      nlinarith [mul_le_mul_of_nonneg_right h4 h0]
    have := Real.pi_gt_three
    nlinarith
  · have h0 := epsC_nonneg ell hρ j' l
    have hle := (epsC_le ell (by omega) hρ j' l).trans hE2
    have hden : 0 < Real.pi * ((loopFactorBound ell : ℝ) + 1) := by positivity
    calc Real.pi / 2 * ((loopFactorBound ell : ℝ) * epsC ell ρ j' l)
        ≤ Real.pi / 2 * ((loopFactorBound ell : ℝ) * (r0 / (Real.pi * ((loopFactorBound ell : ℝ) + 1)))) := by gcongr
      _ = r0 * ((loopFactorBound ell : ℝ) / (2 * ((loopFactorBound ell : ℝ) + 1))) := by field_simp
      _ < r0 * 1 := by
          apply mul_lt_mul_of_pos_left _ hr0
          rw [div_lt_one (by positivity)]; linarith
      _ = r0 := by ring
  · apply hsm
    · unfold SstarC; positivity
    · unfold SstarC
      have h1 : Ctheta * (ell : ℝ) ^ 2 * (2 * ((ell : ℝ) ^ 2 * ((1 + 3 * Real.pi) * ρ)))
          = (2 * Ctheta * (ell : ℝ) ^ 2) * ((ell : ℝ) ^ 2 * ((1 + 3 * Real.pi) * ρ)) := by ring
      rw [h1]
      have h2 := mul_le_mul_of_nonneg_left hE3 (by positivity : (0 : ℝ) ≤ 2 * Ctheta * (ell : ℝ) ^ 2)
      refine h2.trans ?_
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.exists_Sstar_small
#print axioms AdalyFormal.OneGap.numerics_epsC

#print axioms AdalyFormal.OneGap.epsC_le
#print axioms AdalyFormal.OneGap.sum_epsC
#print axioms AdalyFormal.OneGap.sum_theta_epsC
