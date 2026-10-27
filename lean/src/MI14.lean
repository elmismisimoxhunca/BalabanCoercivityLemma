import MI13

/-!
# MI14 -- stratified curvature `C ∘ Dm`, and the curl commutator with the partition (M1 lane E, 2026-10-13)

`P = plaqIn Ω₀`, `χ_P = plaqMask P`, `C = curlCovariantLM_L2 U`; plaquette partition `h_p(q₀)` at the base point.
* `curv_strat`     : `‖χ_P C(Dm λ)‖² ≤ 12 ρ² ℓ⁸ ‖e^{−2σ} λ‖²`;
* `plaq_partition` : `Σ_p ‖h_p (χ_P g)‖² = ‖χ_P g‖²`;
* `cC_sum`         : `Σ_p ‖h_p(χ_P C A) − χ_P C(h_p A)‖² ≤ 12 ℓ² KG ‖e^{−σ} A‖²`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide pdist)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

variable {L : PeriodicLatticeExtent}

theorem curlLM_apply (U : Cfg L) (A : BondFnL2 L) (p : PeriodicLatticePlaquette L) :
    (curlCovariantLM_L2 U A) p = curlValueCovariant U (WithLp.ofLp A) p :=
  curlC_apply U A p

/-- the corners of a plaquette of `plaqIn S` lie in `S`. -/
theorem corners_of_plaqIn {S : Set (PeriodicLatticeSite L)} {p : PeriodicLatticePlaquette L} (hp : p ∈ plaqIn S) :
    p.1 ∈ S ∧ periodicLatticeShift p.1 p.2.1.1 ∈ S ∧ periodicLatticeShift p.1 p.2.1.2 ∈ S ∧
      periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∈ S := by
  classical
  have hm : ∀ e ∈ periodicPlaquetteBoundaryEdges p, e.1 ∈ S ∧ periodicLatticeShift e.1 e.2 ∈ S := hp
  have h1 := hm (p.1, p.2.1.1) (by simp [periodicPlaquetteBoundaryEdges])
  have h2 := hm (p.1, p.2.1.2) (by simp [periodicPlaquetteBoundaryEdges])
  have h3 := hm (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) (by simp [periodicPlaquetteBoundaryEdges])
  exact ⟨h1.1, h1.2, h2.2, h3.2⟩

section strat
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf}
  (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hR1 : 1 ≤ R) (hM1 : 1 ≤ M)
include hS hell hR1 hM1

/-- **stratified curvature of the masked gradient**. -/
theorem curv_strat (U : Cfg Lf) (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k U ρ) (lam : SiteL2 Lf) :
    ‖plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (Dm (geomOf ell k S) U lam))‖ ^ 2
      ≤ 12 * ρ ^ 2 * (ell : ℝ) ^ 8 * ‖siteWt (-(sigG (geomOf ell k S) + sigG (geomOf ell k S))) lam‖ ^ 2 := by
  classical
  set G := geomOf ell k S
  set Λ := siteWt (-(sigG G + sigG G)) lam
  have hell0 : 0 < ell := by omega
  have hellr : (0 : ℝ) < ell := by exact_mod_cast hell0
  have hpt : ∀ p : PeriodicLatticePlaquette Lf,
      ‖(plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (Dm G U lam))) p‖ ^ 2
        ≤ 4 * ρ ^ 2 * (ell : ℝ) ^ 8 * ‖Λ (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)‖ ^ 2 := by
    intro p
    rw [plaqMask_apply]
    split_ifs with hp
    · set z := periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2
      have hc := curv_pt U (siteMask G.Om0 lam) p
      have e : (curlCovariantLM_L2 U (Dm G U lam)) p = (curlC U (gradL2 U (siteMask G.Om0 lam))) p := rfl
      rw [e]
      have hd := hol_strat hS hell hR1 hM1 U ρ hρ hreg p hp
      have hz : pdist p.1 z ≤ 2 := pdist_corner2 hS hell hR1 hM1 p.1 _ _
      have hinv := inv_strat_le hS hell hR1 hM1 hz
      have hgz : ‖siteMask G.Om0 lam z‖ ≤ ‖lam z‖ := by
        by_cases hz0 : z ∈ G.Om0
        · rw [siteMask_on _ _ _ hz0]
        · rw [siteMask_off _ _ _ hz0, norm_zero]; exact norm_nonneg _
      have hΛ : ‖Λ z‖ = ‖lam z‖ * (1 / ((ell : ℝ) ^ AdalyFormal.M1.strat S k z) ^ 2) := by
        show ‖siteWt (-(sigG G + sigG G)) lam z‖ = _
        rw [siteWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
        congr 1
        rw [Pi.neg_apply, Pi.add_apply, neg_add, Real.exp_add, ← sq, exp_neg_sig_sq hS hell hR1 hM1 z]
      set s := AdalyFormal.M1.strat S k p.1
      set sz := AdalyFormal.M1.strat S k z
      have hdn : 0 ≤ AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p) :=
        AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _
      have h1 : ‖(curlC U (gradL2 U (siteMask G.Om0 lam))) p‖ ≤ 2 * (ρ * (ell : ℝ) ^ 2 / ((ell : ℝ) ^ s) ^ 2) * ‖lam z‖ := by
        refine hc.trans ?_
        exact mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num)) hgz (norm_nonneg _) (by positivity)
      have h2 : 2 * (ρ * (ell : ℝ) ^ 2 / ((ell : ℝ) ^ s) ^ 2) * ‖lam z‖ ≤ 2 * ρ * (ell : ℝ) ^ 4 * ‖Λ z‖ := by
        rw [hΛ]
        have := mul_le_mul_of_nonneg_left hinv (show (0:ℝ) ≤ 2 * ρ * (ell : ℝ) ^ 2 * ‖lam z‖ by positivity)
        calc 2 * (ρ * (ell : ℝ) ^ 2 / ((ell : ℝ) ^ s) ^ 2) * ‖lam z‖
            = 2 * ρ * (ell : ℝ) ^ 2 * ‖lam z‖ * (1 / ((ell : ℝ) ^ s) ^ 2) := by ring
          _ ≤ 2 * ρ * (ell : ℝ) ^ 2 * ‖lam z‖ * ((ell : ℝ) ^ 2 / ((ell : ℝ) ^ sz) ^ 2) := this
          _ = 2 * ρ * (ell : ℝ) ^ 4 * (‖lam z‖ * (1 / ((ell : ℝ) ^ sz) ^ 2)) := by ring
      have h3 := h1.trans h2
      calc ‖(curlC U (gradL2 U (siteMask G.Om0 lam))) p‖ ^ 2 ≤ (2 * ρ * (ell : ℝ) ^ 4 * ‖Λ z‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h3 2
        _ = 4 * ρ ^ 2 * (ell : ℝ) ^ 8 * ‖Λ z‖ ^ 2 := by ring
    · rw [norm_zero, zero_pow two_ne_zero]; positivity
  rw [PiLp.norm_sq_eq_of_L2]
  calc ∑ p, ‖(plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (Dm G U lam))) p‖ ^ 2
      ≤ ∑ p : PeriodicLatticePlaquette Lf, 4 * ρ ^ 2 * (ell : ℝ) ^ 8 *
          ‖Λ (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)‖ ^ 2 :=
        Finset.sum_le_sum (fun p _ => hpt p)
    _ = 4 * ρ ^ 2 * (ell : ℝ) ^ 8 * ∑ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite Lf,
          ‖Λ (periodicLatticeShift (periodicLatticeShift x d.1.1) d.1.2)‖ ^ 2 := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type_right]
    _ = 4 * ρ ^ 2 * (ell : ℝ) ^ 8 * ∑ _d : PeriodicPlaquetteDirections, ‖Λ‖ ^ 2 := by
        congr 1
        exact Finset.sum_congr rfl (fun d _ => sum_site_le Λ d.1.1 d.1.2)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, card_dirs]; simp; ring

end strat

/-! ## the curl commutator -/

section comm
variable {Lf : PeriodicLatticeExtent} {ell M R k κ c : ℕ} {S : Tower Lf}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c)
include hS hκ hM hell hR1 hR hc

/-- the plaquette partition is a partition on `plaqIn Ω₀`. -/
theorem plaq_partition (g : PlaqFnL2 Lf) :
    ∑ p, ‖plaqMul (fun q => AdalyFormal.M1.hpart ell M k κ c S p q.1) (plaqMask (plaqIn (S.Om 0)) g)‖ ^ 2
      = ‖plaqMask (plaqIn (S.Om 0)) g‖ ^ 2 := by
  classical
  simp only [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  simp only [plaqMul_apply, plaqMask_apply]
  split_ifs with hq
  · have h0 := (corners_of_plaqIn hq).1
    have hs := AdalyFormal.M1.sum_hpart_sq (ell := ell) (k := k) (κ := κ) (M := M) (c := c) (S := S) hc hκ hM (by omega) h0
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [← Finset.sum_mul, hs, one_mul]
  · simp

/-- **(L5) the curl commutator**. -/
theorem cC_sum (U : Cfg Lf) (A : BondFnL2 Lf) :
    ∑ p, ‖plaqMul (fun q => AdalyFormal.M1.hpart ell M k κ c S p q.1)
          (plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U A))
        - plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (bondMul (hbond ell M k κ c S p) A))‖ ^ 2
      ≤ 12 * (ell : ℝ) ^ 2 * KG ell M κ c * ‖bondWt (-sigG (geomOf ell k S)) A‖ ^ 2 := by
  classical
  set A' := bondWt (-sigG (geomOf ell k S)) A
  have hell0 : 0 < ell := by omega
  have hK0 := KG_nonneg ell M κ c
  have hpt : ∀ q : PeriodicLatticePlaquette Lf,
      ∑ p, ‖(plaqMul (fun q => AdalyFormal.M1.hpart ell M k κ c S p q.1)
          (plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U A))
        - plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (bondMul (hbond ell M k κ c S p) A))) q‖ ^ 2
      ≤ 2 * (ell : ℝ) ^ 2 * KG ell M κ c * (‖A' (periodicLatticeShift q.1 q.2.1.1, q.2.1.2)‖ ^ 2
          + ‖A' (periodicLatticeShift q.1 q.2.1.2, q.2.1.1)‖ ^ 2) := by
    intro q
    set x := q.1
    set μ := q.2.1.1
    set ν := q.2.1.2
    by_cases hq : q ∈ plaqIn (S.Om 0)
    · obtain ⟨hx0, hxμ, hxν, -⟩ := corners_of_plaqIn hq
      have hb : ∀ p, ∀ b : Bond Lf, b.1 ∈ S.Om 0 → hbond ell M k κ c S p b = AdalyFormal.M1.hpart ell M k κ c S p b.1 :=
        fun p b hb => if_pos hb
      have hval : ∀ p, (plaqMul (fun q => AdalyFormal.M1.hpart ell M k κ c S p q.1)
            (plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U A))
          - plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (bondMul (hbond ell M k κ c S p) A))) q
          = (AdalyFormal.M1.hpart ell M k κ c S p x - AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShift x μ))
              • RMap (U (x, μ)) (A (periodicLatticeShift x μ, ν))
            - (AdalyFormal.M1.hpart ell M k κ c S p x - AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShift x ν))
              • RMap (U (x, ν)) (A (periodicLatticeShift x ν, μ)) := by
        intro p
        rw [PiLp.sub_apply, plaqMul_apply, plaqMask_apply, plaqMask_apply, if_pos hq, if_pos hq, curlLM_apply, curlLM_apply]
        unfold curlValueCovariant
        have e1 : ∀ b : Bond Lf, (WithLp.ofLp (bondMul (hbond ell M k κ c S p) A)) b = hbond ell M k κ c S p b • A b :=
          fun b => rfl
        have e2 : ∀ b : Bond Lf, (WithLp.ofLp A) b = A b := fun b => rfl
        simp only [e1, e2]
        rw [hb p (x, μ) hx0, hb p (x, ν) hx0, hb p (periodicLatticeShift x μ, ν) hxμ, hb p (periodicLatticeShift x ν, μ) hxν]
        simp only [map_smul, smul_add, smul_sub, sub_smul]
        abel
      set Δμ := fun p => AdalyFormal.M1.hpart ell M k κ c S p x - AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShift x μ)
      set Δν := fun p => AdalyFormal.M1.hpart ell M k κ c S p x - AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShift x ν)
      have hsqp : ∀ p, ‖(plaqMul (fun q => AdalyFormal.M1.hpart ell M k κ c S p q.1)
            (plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U A))
          - plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (bondMul (hbond ell M k κ c S p) A))) q‖ ^ 2
          ≤ 2 * (Δμ p ^ 2 * ‖A (periodicLatticeShift x μ, ν)‖ ^ 2 + Δν p ^ 2 * ‖A (periodicLatticeShift x ν, μ)‖ ^ 2) := by
        intro p
        rw [hval p]
        have h1 := norm_sub_le (Δμ p • RMap (U (x, μ)) (A (periodicLatticeShift x μ, ν)))
          (Δν p • RMap (U (x, ν)) (A (periodicLatticeShift x ν, μ)))
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap,
          AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap] at h1
        have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        have ha := sq_abs (Δμ p)
        have hb' := sq_abs (Δν p)
        nlinarith [sq_nonneg (|Δμ p| * ‖A (periodicLatticeShift x μ, ν)‖ - |Δν p| * ‖A (periodicLatticeShift x ν, μ)‖),
          abs_nonneg (Δμ p), abs_nonneg (Δν p), norm_nonneg (A (periodicLatticeShift x μ, ν)),
          norm_nonneg (A (periodicLatticeShift x ν, μ))]
      have hstμ := hpart_step_w hS hκ hM hell hR1 hR hc hx0 μ hxμ
      have hstν := hpart_step_w hS hκ hM hell hR1 hR hc hx0 ν hxν
      -- convert the weights to the tails of the two bonds
      have hconv : ∀ (τ : Fin 3) (b : Bond Lf), b.1 = periodicLatticeShift x τ →
          ((ell : ℝ) ^ stratG (geomOf ell k S) x) ^ 2 * ‖A b‖ ^ 2 ≥ 0 ∧
          ‖A b‖ ^ 2 ≤ (ell : ℝ) ^ 2 * ((ell : ℝ) ^ stratG (geomOf ell k S) x) ^ 2 * ‖A' b‖ ^ 2 := by
        intro τ b hbt
        refine ⟨by positivity, ?_⟩
        have hpd : pdist x b.1 ≤ 2 := by rw [hbt]; exact pdist_corner1 hS hell hR1 hM x τ
        have hadj := strat_near hS hell hR1 (by omega) hpd
        rw [strat_eq_stratG hell0 hS, strat_eq_stratG hell0 hS] at hadj
        have e : ‖A' b‖ ^ 2 = ‖A b‖ ^ 2 / ((ell : ℝ) ^ stratG (geomOf ell k S) b.1) ^ 2 := by
          show ‖(bondWt (-sigG (geomOf ell k S)) A) b‖ ^ 2 = _
          rw [bondWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
          have : Real.exp ((-sigG (geomOf ell k S)) b.1) ^ 2 = 1 / ((ell : ℝ) ^ stratG (geomOf ell k S) b.1) ^ 2 := by
            show Real.exp (-(sigG (geomOf ell k S) b.1)) ^ 2 = _
            rw [Real.exp_neg, exp_sig (geomOf ell k S) hell0, inv_pow, one_div]; rfl
          rw [this]; ring
        rw [e]
        have hp1 : (0 : ℝ) < ((ell : ℝ) ^ stratG (geomOf ell k S) b.1) ^ 2 := by positivity
        rw [mul_div_assoc', le_div_iff₀ hp1]
        have hpow : ((ell : ℝ) ^ stratG (geomOf ell k S) b.1) ^ 2 ≤ (ell : ℝ) ^ 2 * ((ell : ℝ) ^ stratG (geomOf ell k S) x) ^ 2 := by
          rw [← pow_mul, ← pow_mul, ← pow_add]
          exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ ell by omega)) (by omega)
        nlinarith [sq_nonneg ‖A b‖]
      have hA1 := (hconv μ (periodicLatticeShift x μ, ν) rfl).2
      have hA2 := (hconv ν (periodicLatticeShift x ν, μ) rfl).2
      calc ∑ p, ‖(plaqMul (fun q => AdalyFormal.M1.hpart ell M k κ c S p q.1)
            (plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U A))
          - plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (bondMul (hbond ell M k κ c S p) A))) q‖ ^ 2
          ≤ ∑ p, 2 * (Δμ p ^ 2 * ‖A (periodicLatticeShift x μ, ν)‖ ^ 2 + Δν p ^ 2 * ‖A (periodicLatticeShift x ν, μ)‖ ^ 2) :=
            Finset.sum_le_sum (fun p _ => hsqp p)
        _ = 2 * ((∑ p, Δμ p ^ 2) * ‖A (periodicLatticeShift x μ, ν)‖ ^ 2 + (∑ p, Δν p ^ 2) * ‖A (periodicLatticeShift x ν, μ)‖ ^ 2) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
        _ ≤ 2 * (KG ell M κ c * (ell : ℝ) ^ 2 * ‖A' (periodicLatticeShift x μ, ν)‖ ^ 2
              + KG ell M κ c * (ell : ℝ) ^ 2 * ‖A' (periodicLatticeShift x ν, μ)‖ ^ 2) := by
            refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
            · have hl : (0 : ℝ) < ((ell : ℝ) ^ stratG (geomOf ell k S) x) ^ 2 := by
                have : (0:ℝ) < ell := (by exact_mod_cast hell0)
                positivity
              have h0 : (∑ p, Δμ p ^ 2) * ((ell : ℝ) ^ stratG (geomOf ell k S) x) ^ 2 ≤ KG ell M κ c := by
                rw [mul_comm]; exact hstμ
              nlinarith [hA1, sq_nonneg ‖A (periodicLatticeShift x μ, ν)‖, Finset.sum_nonneg (fun p (_ : p ∈ Finset.univ) => sq_nonneg (Δμ p))]
            · have hl : (0 : ℝ) < ((ell : ℝ) ^ stratG (geomOf ell k S) x) ^ 2 := by
                have : (0:ℝ) < ell := (by exact_mod_cast hell0)
                positivity
              have h0 : (∑ p, Δν p ^ 2) * ((ell : ℝ) ^ stratG (geomOf ell k S) x) ^ 2 ≤ KG ell M κ c := by
                rw [mul_comm]; exact hstν
              nlinarith [hA2, sq_nonneg ‖A (periodicLatticeShift x ν, μ)‖, Finset.sum_nonneg (fun p (_ : p ∈ Finset.univ) => sq_nonneg (Δν p))]
        _ = _ := by ring
    · have hz : ∀ p, (plaqMul (fun q => AdalyFormal.M1.hpart ell M k κ c S p q.1)
            (plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U A))
          - plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (bondMul (hbond ell M k κ c S p) A))) q = 0 := by
        intro p
        rw [PiLp.sub_apply, plaqMul_apply, plaqMask_apply, plaqMask_apply, if_neg hq, if_neg hq, smul_zero, sub_zero]
      simp only [hz, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
      positivity
  simp only [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  calc ∑ q, ∑ p, ‖(plaqMul (fun q => AdalyFormal.M1.hpart ell M k κ c S p q.1)
          (plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U A))
        - plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (bondMul (hbond ell M k κ c S p) A))) q‖ ^ 2
      ≤ ∑ q : PeriodicLatticePlaquette Lf, 2 * (ell : ℝ) ^ 2 * KG ell M κ c * (‖A' (periodicLatticeShift q.1 q.2.1.1, q.2.1.2)‖ ^ 2
          + ‖A' (periodicLatticeShift q.1 q.2.1.2, q.2.1.1)‖ ^ 2) := Finset.sum_le_sum (fun q _ => hpt q)
    _ = 2 * (ell : ℝ) ^ 2 * KG ell M κ c * ∑ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite Lf,
          (‖A' (periodicLatticeShift x d.1.1, d.1.2)‖ ^ 2 + ‖A' (periodicLatticeShift x d.1.2, d.1.1)‖ ^ 2) := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type_right]
    _ ≤ 2 * (ell : ℝ) ^ 2 * KG ell M κ c * ∑ _d : PeriodicPlaquetteDirections, 2 * ‖A'‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d _ => ?_)) (by positivity)
        rw [Finset.sum_add_distrib, sum_shift_site d.1.1 (fun y => ‖A' (y, d.1.2)‖ ^ 2),
          sum_shift_site d.1.2 (fun y => ‖A' (y, d.1.1)‖ ^ 2)]
        linarith [sum_dir_le A' d.1.2, sum_dir_le A' d.1.1]
    _ = 12 * (ell : ℝ) ^ 2 * KG ell M κ c * ‖A'‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, card_dirs]; simp; ring
    _ = _ := by rw [PiLp.norm_sq_eq_of_L2]

end comm

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.curlLM_apply
#print axioms AdalyFormal.M1IMS.corners_of_plaqIn
#print axioms AdalyFormal.M1IMS.curv_strat
#print axioms AdalyFormal.M1IMS.plaq_partition
#print axioms AdalyFormal.M1IMS.cC_sum
