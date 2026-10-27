import DK2
import DK3
import GCz1
import DLR96

/-!
# DK4 -- **`hKD` at M1**: `Σ_e ‖D̃⁽²⁾(B)(e)‖ ≤ KDfree ℓ · ‖B‖²` on the M1 domain, k-free (KD sub-lane, 2026-10-13)

* `qM1 β = 2β + (4π+2)β²` (plaquette constant), `kapM1 β = β + 3π qM1 β` (bound on the level-`k` background near `Λ`).
* `KDsmall ℓ β` : five explicit k-free inequalities on `β = 12Mα₀` (`β ≤ 1`; NB25's `4·10⁶ℓ² qM1 β ≤ 1`; the unit
  conditions `u1`, `u2` of `UnitSmall` form and DL76's `hKDc`, all at `κ = kapM1 β`).
* `KDsmall_window ℓ` (`ℓ > 0`): `∃ β₀ > 0, ∀ β ∈ [0, β₀], KDsmall ℓ β` (continuity at `β = 0`; DL96 `te2rho`).
  `beta0 ℓ` := that `β₀` (choice), `beta0_pos`, `KDsmall_of_le`.
* **`D2in_l1_M1`** : on `Admissible`, `2 ≤ ℓ`, room `17ℓ ≤ RM`, `TorusOK`, `LambdaOK2`, `M1Regular ℓ M 12 k S α₀ ℓ⁻ᵏ U`,
  `0 ≤ α₀`, `KDsmall ℓ (12Mα₀)`: for every `B`, `Σ_e ‖(gparams … U … Λ).D2in B e‖ ≤ KDfree ℓ ‖B‖²`.
  Route: gauge of `M1Regular` (GCg3 `D2in_gauge`, GCz1), DK2 `chart_bounds` + `tower_near` on the read balls, DK3 `D2in_l1_near`.
* **`D2in_l1_M1'`** : the same with `12Mα₀ ≤ beta0 ℓ` in place of `KDsmall`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DK

open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible pdist scaleUp CRowIn TorusOK)
open AdalyFormal.StatementLaneG (LambdaOK2 gparams)
open AdalyFormal.StatementLaneR8 (Ball pdist_triangle pdist_comm pdist_coarseShift_le lamPrime_sub)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.NonflatJet (rhoOf r0)
open EstimatesLayer.E1E3 (e2Majorant)
open AdalyFormal.DLayer (KDfree)

/-- the plaquette constant of the M1 chart -/
noncomputable def qM1 (β : ℝ) : ℝ := 2 * β + (4 * Real.pi + 2) * β ^ 2

/-- the bound on the level-`k` background on the read balls -/
noncomputable def kapM1 (β : ℝ) : ℝ := β + 3 * Real.pi * qM1 β

theorem qM1_nonneg {β : ℝ} (h : 0 ≤ β) : 0 ≤ qM1 β := by unfold qM1; positivity

theorem kapM1_nonneg {β : ℝ} (h : 0 ≤ β) : 0 ≤ kapM1 β := by
  unfold kapM1; have := qM1_nonneg h; positivity

/-- the k-free smallness of `β = 12Mα₀` -/
structure KDsmall (ell : ℕ) (β : ℝ) : Prop where
  h1 : β ≤ 1
  hcb : 4000000 * (ell : ℝ) ^ 2 * qM1 β ≤ 1
  u1 : kapM1 β ≤ 1 / (1000 * (ell : ℝ) ^ 4)
  u2 : Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * kapM1 β) < r0
  kd : 192 * (8 * (ell : ℝ) * kapM1 β + 8 * e2Majorant (rhoOf ell (kapM1 β))) ≤ 1 / (2 * (ell : ℝ) ^ 3)

theorem KDsmall_window (ell : ℕ) (hell : 0 < ell) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → KDsmall ell β := by
  have hr0 : 0 < r0 := (Classical.choose_spec AdalyFormal.NonflatJet.exists_r0).1
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have tq : Tendsto qM1 (𝓝 0) (𝓝 0) := by
    have hc : Continuous qM1 := by unfold qM1; fun_prop
    have h := hc.tendsto 0
    rwa [show qM1 0 = 0 by simp [qM1]] at h
  have tk : Tendsto kapM1 (𝓝 0) (𝓝 0) := by
    have hc : Continuous kapM1 := by unfold kapM1 qM1; fun_prop
    have h := hc.tendsto 0
    rwa [show kapM1 0 = 0 by simp [kapM1, qM1]] at h
  have te := AdalyFormal.DLayer.te2rho tk ell
  have e1 : ∀ᶠ β in 𝓝 (0 : ℝ), β < 1 := gt_mem_nhds one_pos
  have e2 : ∀ᶠ β in 𝓝 (0 : ℝ), 4000000 * (ell : ℝ) ^ 2 * qM1 β < 1 :=
    (tq.const_mul (4000000 * (ell : ℝ) ^ 2)).eventually (gt_mem_nhds (by rw [mul_zero]; exact one_pos))
  have e3 : ∀ᶠ β in 𝓝 (0 : ℝ), kapM1 β < 1 / (1000 * (ell : ℝ) ^ 4) :=
    tk.eventually (gt_mem_nhds (by positivity))
  have e4 : ∀ᶠ β in 𝓝 (0 : ℝ), Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * kapM1 β) < r0 :=
    ((tk.const_mul (SmallnessBridge.Assemble.loopFactorBound ell : ℝ)).const_mul (Real.pi / 2)).eventually
      (gt_mem_nhds (by rw [mul_zero, mul_zero]; exact hr0))
  have e5 : ∀ᶠ β in 𝓝 (0 : ℝ),
      192 * (8 * (ell : ℝ) * kapM1 β + 8 * e2Majorant (rhoOf ell (kapM1 β))) < 1 / (2 * (ell : ℝ) ^ 3) :=
    (((tk.const_mul (8 * (ell : ℝ))).add (te.const_mul 8)).const_mul 192).eventually
      (gt_mem_nhds (by rw [mul_zero, mul_zero, add_zero, mul_zero]; positivity))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (e1.and (e2.and (e3.and (e4.and e5))))
  refine ⟨ε / 2, by positivity, fun β hβ0 hβ => ?_⟩
  have hd : dist β 0 < ε := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hβ0]; linarith
  obtain ⟨a1, a2, a3, a4, a5⟩ := hball hd
  exact ⟨a1.le, a2.le, a3.le, a4, a5.le⟩

/-- the k-free threshold (any `β₀` of `KDsmall_window`; `1` at the excluded `ℓ = 0`) -/
noncomputable def beta0 (ell : ℕ) : ℝ :=
  if h : 0 < ell then Classical.choose (KDsmall_window ell h) else 1

theorem beta0_pos (ell : ℕ) (hell : 0 < ell) : 0 < beta0 ell := by
  unfold beta0; rw [dif_pos hell]; exact (Classical.choose_spec (KDsmall_window ell hell)).1

theorem KDsmall_of_le (ell : ℕ) (hell : 0 < ell) (β : ℝ) (h0 : 0 ≤ β) (h : β ≤ beta0 ell) : KDsmall ell β := by
  unfold beta0 at h; rw [dif_pos hell] at h
  exact (Classical.choose_spec (KDsmall_window ell hell)).2 β h0 h

/-- **`hKD` at M1.** -/
theorem D2in_l1_M1 (ell M R k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (α₀ : ℝ)
    (hA : Admissible ell M R k S) (hell2 : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hT : TorusOK ell M Lu)
    (hL : LambdaOK2 ell M R k S Lam) (hU : AdalyFormal.M1.M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hα : 0 ≤ α₀) (hsm : KDsmall ell (12 * M * α₀)) (B : BondFnL2 Lu) :
    ∑ e, ‖((gparams ell k Lu hell S U a Lam).D2in B) e‖ ≤ KDfree ell * ‖B‖ ^ 2 := by
  obtain ⟨g, A, hg, hb⟩ := hU
  set P := gparams ell k Lu hell S U a Lam with hP
  set β : ℝ := 12 * M * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  obtain ⟨hlk, hpl⟩ := chart_bounds ell M k hell S α₀ U g A _ rfl hg hb hα hsm.h1
  have hd : ∀ μ, ell ∣ Lu μ + 1 := hT.1
  have hT3 : ∀ μ, 3 ≤ Lu μ + 1 := fun μ => by have := hT.2.1 μ; omega
  set P' := AdalyFormal.GaugeCov.gaugeP P g with hP'
  set u := AdalyFormal.GaugeCov.uOf ell k Lu hell g with hu
  have hnear : ∀ c, CRowIn P'.ell P'.Lam c → ∀ z ∈ Ball c.1.1 (4 * (1 * P'.ell)), ∀ μ : Fin 3,
      frobNorm (((P'.unitBgU (z, μ) : SU2) : M2) - 1) ≤ kapM1 β := by
    intro c hc z hz μ
    have hz' : pdist c.1.1 z ≤ 4 * (1 * ell) := hz
    obtain ⟨y, hy, hyz⟩ : ∃ y ∈ Lam, pdist y z + 17 ≤ R * M := by
      rcases hc with h | h
      · exact ⟨c.1.1, lamPrime_sub hell h, by omega⟩
      · refine ⟨coarseShift c.1.1 ell c.2, lamPrime_sub hell h, ?_⟩
        have h1 : pdist (coarseShift c.1.1 ell c.2) c.1.1 ≤ ell := by
          rw [pdist_comm]; exact pdist_coarseShift_le _ _ _
        have h2 := pdist_triangle (coarseShift c.1.1 ell c.2) c.1.1 z
        omega
    exact tower_near ell M R k Lu hell2 hell S hA Lam hL hT3 (periodicGaugeTransform g U) β (qM1 β)
      (qM1_nonneg hβ0) hlk hpl hsm.hcb hy hyz μ
  have hmain := D2in_l1_near P' hd hell2 (kapM1 β) (kapM1_nonneg hβ0) hnear hsm.u1 hsm.u2 hsm.kd
    (AdalyFormal.GaugeCov.adBL u B)
  have hgauge : P'.D2in (AdalyFormal.GaugeCov.adBL u B) = AdalyFormal.GaugeCov.adBL u (P.D2in B) :=
    AdalyFormal.GaugeCov.D2in_gauge P (periodicGaugeTransform g P.U) u
      (fun B c => AdalyFormal.GaugeCov.Q1_gauge_pt P g B c) (fun B c => AdalyFormal.GaugeCov.C2tilde_gauge_pt P g B c) B
  rw [hgauge, LinearIsometryEquiv.norm_map] at hmain
  have hnorm : ∀ e, ‖(AdalyFormal.GaugeCov.adBL u (P.D2in B)) e‖ = ‖(P.D2in B) e‖ :=
    fun e => AdalyFormal.Balaban.TowerLawCov.norm_RMap _ _
  rw [Finset.sum_congr rfl (fun e _ => hnorm e)] at hmain
  exact hmain

/-- **`hKD` at M1, threshold form**: `12Mα₀ ≤ beta0 ℓ`. -/
theorem D2in_l1_M1' (ell M R k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (α₀ : ℝ)
    (hA : Admissible ell M R k S) (hell2 : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hT : TorusOK ell M Lu)
    (hL : LambdaOK2 ell M R k S Lam) (hU : AdalyFormal.M1.M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hα : 0 ≤ α₀) (hsm : (12 : ℝ) * M * α₀ ≤ beta0 ell) (B : BondFnL2 Lu) :
    ∑ e, ‖((gparams ell k Lu hell S U a Lam).D2in B) e‖ ≤ KDfree ell * ‖B‖ ^ 2 :=
  D2in_l1_M1 ell M R k Lu hell S U a Lam α₀ hA hell2 hroom hT hL hU hα
    (KDsmall_of_le ell hell _ (by positivity) hsm) B

#print axioms qM1
#print axioms kapM1
#print axioms qM1_nonneg
#print axioms kapM1_nonneg
#print axioms KDsmall
#print axioms KDsmall_window
#print axioms beta0
#print axioms beta0_pos
#print axioms KDsmall_of_le
#print axioms D2in_l1_M1
#print axioms D2in_l1_M1'

end AdalyFormal.M1DK
