import OG6

/-!
# OG7 -- F4 from `BallChartsAt`: `interfaceCharts_of_ball` (lane m2_onegap_20261015)
Mirror of `M2Route.interfaceCharts_of_M1` with the global regime replaced by the region chart of `BallChartsAt` on `Ball w (r+1)`, `r = chartRad`.
The chart constant is `12 M (C α₀)` (the region chart is at scale `ℓ^{j-1}`, exactly the `ChartOn` level; no transfer needed).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.OneGap

open AdalyFormal.M2Bridge
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball AgreeAt pdist_comm pdist_shift_le pdist_triangle)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1 (M1Bounds M1Regular bstrat strat StratReads om_anti le_bstrat_of_mem mem_strat_of_pos gsp)
open AdalyFormal.M1W2 (caseB_down)
open AdalyFormal.M2Route (InterfaceCharts ChartOn chartRad)

variable {L : PeriodicLatticeExtent}

theorem interfaceCharts_of_ball {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hM : 0 < M)
    (hell : 2 ≤ ell) (hR4 : (5 + 4) * 1 * ell ≤ R) {d : ℕ} (hdM : d + 64 * ell ^ 2 + 2 ≤ M)
    (hLthick : ∀ σ : Fin 3, 13 * (M * ell ^ k) ≤ L σ + 1)
    {C α₀ η : ℝ} {U : LinkCfg L} (hB : BallChartsAt ell M k S U C α₀ η) :
    InterfaceCharts ell M k d S U η ((12 : ℕ) * M * (C * α₀)) := by
  classical
  intro j w hp hj hB' _hc
  have hZi := caseB_down hS hell one_pos hM hR4 hp hj
  have hjk : j - 1 ≤ k := by have := hp.1; omega
  have hjk' : j ≤ k := hp.1
  set r : ℕ := chartRad ell M 1 5 d j (j - 1) with hr
  have hr6 : r + 1 ≤ (5 + 1) * gsp ell M 1 j := by
    have hpi : ell ^ (j - 1) ≤ ell ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    have hroom : (d + 64 * ell ^ 2 + 2) * ell ^ j ≤ M * ell ^ j := Nat.mul_le_mul_right _ hdM
    have hpj : 1 ≤ ell ^ j := Nat.one_le_pow _ _ (by omega)
    have hy' : r + 1 = 5 * gsp ell M 1 j + d * ell ^ (j - 1) + 64 * ell ^ (j - 1 + 2) + 1 := rfl
    rw [AdalyFormal.M2Route.gsp_one] at hy' ⊢
    have e2 : ell ^ (j - 1 + 2) = ell ^ 2 * ell ^ (j - 1) := by ring
    rw [e2] at hy'
    have h1' : d * ell ^ (j - 1) ≤ d * ell ^ j := Nat.mul_le_mul_left _ hpi
    have h2' : 64 * (ell ^ 2 * ell ^ (j - 1)) ≤ 64 * ell ^ 2 * ell ^ j := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_left _ hpi
    have hbs : bigSide M ell j = M * ell ^ j := rfl
    rw [hbs]
    nlinarith
  have hbs : bigSide M ell j = M * ell ^ j := rfl
  have hr7 : r + 1 ≤ 7 * M * ell ^ j := by
    have := AdalyFormal.M2Route.gsp_one ell M j
    rw [this, hbs] at hr6
    nlinarith [Nat.zero_le (M * ell ^ j)]
  have hin : ∀ x ∈ Ball w (r + 1), x ∈ S.Om (j - 1) := fun x hx => hZi (le_trans hx hr6)
  have hmiss1 : ∀ x ∈ Ball w (r + 1), x ∉ S.Om (j + 1) := fun x hx hxO =>
    hB' ⟨x, le_trans hx hr6, hxO⟩
  have hmiss : ∀ x ∈ Ball w (r + 1), x ∉ S.Om (j + 2) := fun x hx hxO =>
    hmiss1 x hx (om_anti hS (by omega : j + 1 ≤ j + 2) hxO)
  obtain ⟨x₀, hx0j, -, hd0⟩ := hp.anchor one_pos hM (by omega)
  have hanc : ∃ x₁ ∈ S.Om j, pdist w x₁ ≤ 3 * (M * ell ^ j) := by
    refine ⟨x₀, hx0j, ?_⟩
    rw [pdist_comm]
    have := AdalyFormal.M2Route.gsp_one ell M j
    rw [this] at hd0
    exact hd0
  have hnw : ∀ σ : Fin 3, 2 * (r + 1) + 2 ≤ L σ + 1 := by
    intro σ
    have e1 := AdalyFormal.M2Route.gsp_one ell M j
    rw [e1, hbs] at hr6
    have hBj : M * ell ^ j ≤ M * ell ^ k := Nat.mul_le_mul_left M (Nat.pow_le_pow_right (by omega) hjk')
    have hB2 : 2 ≤ M * ell ^ j := by
      have : 2 ≤ ell ^ j := by
        calc 2 ≤ ell := hell
          _ = ell ^ 1 := (pow_one ell).symm
          _ ≤ ell ^ j := Nat.pow_le_pow_right (by omega) hj
      nlinarith
    have := hLthick σ
    omega
  obtain ⟨g, A, hexp, hd⟩ := hB j hjk' w hanc (r + 1) hr7 hnw hin hmiss (Or.inr hmiss1)
  have hcb : ∀ e : Bond L, pdist w e.1 ≤ r → CubeBond (Ball w (r + 1)) e := by
    intro e he
    refine ⟨Nat.le_succ_of_le he, ?_⟩
    have := pdist_triangle w e.1 (periodicLatticeShift e.1 e.2)
    have := pdist_shift_le e.1 e.2
    show pdist w (periodicLatticeShift e.1 e.2) ≤ r + 1
    omega
  refine ⟨g, fun e => if CubeBond (Ball w (r + 1)) e then A e else 0, fun e => ?_, fun e he => ?_, fun e he => ?_,
    fun μ ν x hx hx' => ?_⟩
  · by_cases hc : CubeBond (Ball w (r + 1)) e
    · show HT (if CubeBond (Ball w (r + 1)) e then A e else 0)
      rw [if_pos hc]; exact hd.ht e hc
    · show HT (if CubeBond (Ball w (r + 1)) e then A e else 0)
      rw [if_neg hc]; simp [AdalyFormal.StatementLane.HT]
  · beta_reduce
    rw [if_pos (hcb e he)]; exact hexp e (hcb e he)
  · beta_reduce
    rw [if_pos (hcb e he)]
    exact hd.c1 e (hcb e he)
  · have b0 : CubeBond (Ball w (r + 1)) ((x, ν) : Bond L) := hcb (x, ν) hx
    have b1 : CubeBond (Ball w (r + 1)) ((periodicLatticeShift x μ, ν) : Bond L) := hcb (periodicLatticeShift x μ, ν) hx'
    beta_reduce
    simp only [if_pos b0, if_pos b1]
    exact hd.c2 μ ν x b0 b1

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.interfaceCharts_of_ball
