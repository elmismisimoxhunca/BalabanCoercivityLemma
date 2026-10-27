import OG1
import GG4

/-!
# BallCharts.lean -- `BallChartsG`: the group-level (GChart) form of the single residual statement (lane m2_onegap_20261015)

`BallChartsAtG ell M k S U C α₀ η` : the hypotheses of `BallChartsAt` (a centre `w` within `3 M ℓ^j` of `Ω_j`, a non-wrapping radius `r ≤ 7 M ℓ^j`, `Ball w r ⊆ Ω_{j-1}`, missing `Ω_{j+2}`, small or
missing `Ω_{j+1}`) and the conclusion: ONE gauge `g : site → SU(2)` with `m2_glue2.GChart U g (Ball w r) (C t₁) (C t₂)`, where `t₁ = 12 M α₀ ℓ^{-(j-1)}`, `t₂ = 12 M α₀ ℓ^{-2(j-1)}`
(`s ~ f M α₀ ℓ^{-2i}`, `i = j-1`).  `C = C(ℓ,M,R)` is chosen before `k` (the `ClassFam` shape), `Λ ≠ ∅`.
`BallChartsG` : the statement.   `ballCharts_of_G : BallChartsG → BallCharts` : the bridge (own copy of the `chartOn_of_group` argument on `CubeBond (Ball w r)` instead of `pdist ≤ r`;
constant `C' = (π/2) C + 1`, threshold `s' = min s (1/C)`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.OneGap

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK pdist HT CubeBond)
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log)
open AdalyFormal.M2Skel (ClassFam)
open AdalyFormal.M2Glue2 (GChart chA chA_HT chA_exp frobNorm_chA chA_sub log_le log_lip)
open AdalyFormal.Balaban.Bch2 (frobNorm_smul)
open AdalyFormal.Balaban.RegularityGap (frobNorm_negI_smul)

variable {L : PeriodicLatticeExtent}

/-- the GChart form of `BallChartsAt` -/
def BallChartsAtG (ell M k : ℕ) (S : Tower L) (U : LinkCfg L) (C α₀ η : ℝ) : Prop :=
  ∀ j : ℕ, j ≤ k → ∀ w : PeriodicLatticeSite L, (∃ x₀ ∈ S.Om j, pdist w x₀ ≤ 3 * (M * ell ^ j)) → ∀ r : ℕ, r ≤ 7 * M * ell ^ j →
    (∀ σ : Fin 3, 2 * r + 2 ≤ L σ + 1) →
    (∀ x ∈ Ball w r, x ∈ S.Om (j - 1)) → (∀ x ∈ Ball w r, x ∉ S.Om (j + 2)) →
    (r ≤ 1000 * ell ^ (j + 1) ∨ ∀ x ∈ Ball w r, x ∉ S.Om (j + 1)) →
    ∃ g : PeriodicLatticeSite L → SU2, GChart U g (Ball w r)
      (C * (((12 : ℕ) : ℝ) * M * α₀ * ((ell : ℝ) ^ (j - 1))⁻¹))
      (C * (((12 : ℕ) : ℝ) * M * α₀ * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2))

/-- **BallChartsG**: the residual statement in the gluing lane's vocabulary. -/
def BallChartsG : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFam ell ℝ (fun _ _ C => 1 ≤ C) (fun M _ k _ C S Lam U α₀ =>
      Lam.Nonempty → BallChartsAtG ell M k S U C α₀ ((ell : ℝ) ^ k)⁻¹)

/-- a GChart on a site set is a `RegionChart` on it (no radius loss) -/
theorem regionChart_of_gchart {ell M f : ℕ} {α η : ℝ} {i : ℕ} {D : Set (PeriodicLatticeSite L)} {U : LinkCfg L}
    {g : PeriodicLatticeSite L → SU2} {T1 T2 : ℝ} (hell : 0 < ell) (hη : 0 < η) (hT1 : T1 ≤ 1)
    (h : GChart U g D T1 T2)
    (ha1 : (Real.pi / 2) * T1 < ((f : ℝ) * M * α) * ((ell : ℝ) ^ i)⁻¹)
    (ha2 : (Real.pi / 2) * T2 < ((f : ℝ) * M * α) * (((ell : ℝ) ^ i)⁻¹) ^ 2) :
    RegionChart D ell M f α η i U := by
  obtain ⟨h1, h2⟩ := h
  have hl : (0 : ℝ) < (ell : ℝ) ^ i := by positivity
  have hG1 : ∀ e : Bond L, CubeBond D e → frobNorm (((periodicGaugeTransform g U e : SU2) : M2) - 1) ≤ T1 :=
    fun e he => h1 e.1 e.2 he.1 he.2
  refine ⟨g, fun e => chA η (periodicGaugeTransform g U e), fun e he => ?_, ⟨fun e _ => chA_HT η _, fun e he => ?_, fun μ ν x hx hx' => ?_⟩⟩
  · exact chA_exp hη.ne' _ ((hG1 e he).trans hT1)
  · have hb := hG1 e he
    show frobNorm (chA η (periodicGaugeTransform g U e)) < _
    rw [frobNorm_chA hη]
    have hlog := log_le (hb.trans (hT1.trans (by norm_num)))
    have : η⁻¹ * frobNorm (su2Log (periodicGaugeTransform g U e)) ≤ η⁻¹ * ((Real.pi / 2) * T1) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hη.le)
      have := Real.pi_pos
      calc frobNorm (su2Log (periodicGaugeTransform g U e))
          ≤ (Real.pi / 2) * frobNorm (((periodicGaugeTransform g U e : SU2) : M2) - 1) := hlog
        _ ≤ (Real.pi / 2) * T1 := by gcongr
    refine this.trans_lt ?_
    rw [pow_one, mul_inv, show ((f : ℝ) * M * α) * (((ell : ℝ) ^ i)⁻¹ * η⁻¹) = η⁻¹ * (((f : ℝ) * M * α) * ((ell : ℝ) ^ i)⁻¹) by ring]
    exact mul_lt_mul_of_pos_left ha1 (inv_pos.mpr hη)
  · have hb0 := hG1 (x, ν) hx
    have hb1 := hG1 (periodicLatticeShift x μ, ν) hx'
    have hd := h2 x μ ν hx.1 hx.2 hx'.1 hx'.2
    have hlip := log_lip (hb0.trans (hT1.trans (by norm_num))) (hb1.trans (hT1.trans (by norm_num)))
    show frobNorm ((η⁻¹ : ℝ) • (chA η (periodicGaugeTransform g U (periodicLatticeShift x μ, ν)) - chA η (periodicGaugeTransform g U (x, ν)))) < _
    rw [chA_sub, show ((η⁻¹ : ℝ)) • (((η⁻¹ : ℝ) : ℂ) • ((-Complex.I) • (su2Log (periodicGaugeTransform g U
        (periodicLatticeShift x μ, ν)) - su2Log (periodicGaugeTransform g U (x, ν)))))
        = (η⁻¹ * η⁻¹ : ℝ) • ((-Complex.I) • (su2Log (periodicGaugeTransform g U
        (periodicLatticeShift x μ, ν)) - su2Log (periodicGaugeTransform g U (x, ν)))) by
          rw [mul_smul]; rfl,
      frobNorm_smul, frobNorm_negI_smul, abs_of_pos (by positivity)]
    have : η⁻¹ * η⁻¹ * frobNorm (su2Log (periodicGaugeTransform g U (periodicLatticeShift x μ, ν))
        - su2Log (periodicGaugeTransform g U (x, ν))) ≤ η⁻¹ * η⁻¹ * ((Real.pi / 2) * T2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := Real.pi_pos
      exact hlip.trans (by gcongr)
    refine this.trans_lt ?_
    rw [mul_inv, show ((f : ℝ) * M * α) * (((ell : ℝ) ^ i)⁻¹ * η⁻¹) ^ 2 = η⁻¹ * η⁻¹ * (((f : ℝ) * M * α) * (((ell : ℝ) ^ i)⁻¹) ^ 2) by ring]
    exact mul_lt_mul_of_pos_left ha2 (by positivity)

/-- **the bridge**: the GChart form implies the region-chart form (constant `(π/2) C + 1`, threshold `min s (1/C)`). -/
theorem ballCharts_of_G (hG : BallChartsG) : BallCharts := by
  intro ell hell
  obtain ⟨m₁, hm⟩ := hG ell hell
  refine ⟨m₁, fun m hm1 => ?_⟩
  obtain ⟨R₁, hR⟩ := hm m hm1
  refine ⟨R₁, fun R hR1 => ?_⟩
  obtain ⟨C, hC, s, hs, hf⟩ := hR R hR1
  have hpi := Real.pi_pos
  have hC0 : 0 < C := by linarith
  refine ⟨(Real.pi / 2) * C + 1, by nlinarith, min s (1 / C), lt_min hs (by positivity), ?_⟩
  intro k hk Lu α₀ hα hsα hT S hS Lam hLam U hcc hU1 hne j hjk w hw r hr7 hnw hin hout hsm
  have hs1 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s := hsα.trans (min_le_left _ _)
  have hs2 : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ 1 / C := hsα.trans (min_le_right _ _)
  obtain ⟨g, hg⟩ := hf k hk Lu α₀ hα hs1 hT S hS Lam hLam U hcc hU1 hne j hjk w hw r hr7 hnw hin hout hsm
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

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.regionChart_of_gchart
#print axioms AdalyFormal.OneGap.ballCharts_of_G
