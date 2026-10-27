import MI12

/-!
# MI13 -- stratified `Δ'` (M1 lane E, 2026-10-13)

`P = plaqIn Ω₀`, `HolRegime` (lane C's `hhol`), `σ = stratG · ln ℓ`; bond weights at the tail.
* `plaqMul` : multiplication of plaquette fields by a site function at the base point;
* `deltaPrime_diag`, `exp_neg_sig_sq`, `inv_strat_le` (helpers);
* `deltaPrime_strat` : `|Δ'_P(x,x)| ≤ (17/√2) · 12 · ρ ℓ⁴ ‖e^{−σ} x‖²`.
(The curvature bound `curv_strat`, `plaq_partition` and the curl commutator `cC_sum` are in MI14.)
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
open AdalyFormal.Balaban.DeltaPrimeOperator (bilPlaq)
open AdalyFormal.Balaban.LemmaAssembly (plaqBondSq plaqBondSq_nonneg)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply deltaPrimeBilL2NormLoc deltaPrimeBilNormLoc deltaPrimeBilRawLoc_apply)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

variable {L : PeriodicLatticeExtent}

/-! ## 0. plaquette multiplication -/

noncomputable def plaqMul (h : PeriodicLatticePlaquette L → ℝ) : PlaqFnL2 L →L[ℝ] PlaqFnL2 L :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun p => h p • f p)
      map_add' := fun f g => by refine PiLp.ext (fun x => ?_); simp [smul_add]
      map_smul' := fun c f => by
        refine PiLp.ext (fun x => ?_)
        simp only [PiLp.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }

theorem plaqMul_apply (h : PeriodicLatticePlaquette L → ℝ) (f : PlaqFnL2 L) (p : PeriodicLatticePlaquette L) :
    plaqMul h f p = h p • f p := rfl

open Classical in
/-- `Δ'_P(x,x) = ½ Σ_{p∈P} bilPlaq(x,x)`. -/
theorem deltaPrime_diag (U : Cfg L) (P : Set (PeriodicLatticePlaquette L)) (x : BondFnL2 L) :
    deltaPrimeBilL2NormLoc U P x x
      = (1 / 2) * ∑ p : PeriodicLatticePlaquette L, if p ∈ P then bilPlaq U p (WithLp.ofLp x) (WithLp.ofLp x) else 0 := by
  classical
  show deltaPrimeBilNormLoc U P (WithLp.ofLp x) (WithLp.ofLp x) = _
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul, deltaPrimeBilRawLoc_apply]
  ring

section strat
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf}
  (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hR1 : 1 ≤ R) (hM1 : 1 ≤ M)
include hS hell hR1 hM1

/-- the stratum weight on a site, as `1/ℓ^{2 strat}`. -/
theorem exp_neg_sig_sq (x : PeriodicLatticeSite Lf) :
    Real.exp (-sigG (geomOf ell k S) x) ^ 2 = 1 / ((ell : ℝ) ^ AdalyFormal.M1.strat S k x) ^ 2 := by
  rw [Real.exp_neg, exp_sig (geomOf ell k S) (show 0 < ell by omega), strat_eq_stratG (show 0 < ell by omega) hS]
  rw [inv_pow, one_div]; rfl

/-- `1/ℓ^{2 s_p} ≤ ℓ²/ℓ^{2 s_z}` for `z` within distance 2 of `p₀`. -/
theorem inv_strat_le {x z : PeriodicLatticeSite Lf} (hz : pdist x z ≤ 2) :
    1 / ((ell : ℝ) ^ AdalyFormal.M1.strat S k x) ^ 2 ≤ (ell : ℝ) ^ 2 / ((ell : ℝ) ^ AdalyFormal.M1.strat S k z) ^ 2 := by
  have h := strat_near hS hell hR1 hM1 hz
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have h1 : (0 : ℝ) < ((ell : ℝ) ^ AdalyFormal.M1.strat S k x) ^ 2 := by positivity
  have h2 : (0 : ℝ) < ((ell : ℝ) ^ AdalyFormal.M1.strat S k z) ^ 2 := by positivity
  rw [div_le_div_iff₀ h1 h2, one_mul, ← pow_mul, ← pow_mul, ← pow_add]
  exact pow_le_pow_right₀ hellr (by omega)

/-- **stratified `Δ'`**. -/
theorem deltaPrime_strat (U : Cfg Lf) (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k U ρ) (x : BondFnL2 Lf) :
    |deltaPrimeBilL2NormLoc U (plaqIn (S.Om 0)) x x|
      ≤ (17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4) * ‖bondWt (-sigG (geomOf ell k S)) x‖ ^ 2 := by
  classical
  rw [deltaPrime_diag]
  set y := bondWt (-sigG (geomOf ell k S)) x
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hpt : ∀ p : PeriodicLatticePlaquette Lf,
      |(if p ∈ plaqIn (S.Om 0) then bilPlaq U p (WithLp.ofLp x) (WithLp.ofLp x) else 0)|
        ≤ (34 / Real.sqrt 2) * (ρ * (ell : ℝ) ^ 4) * plaqBondSq (WithLp.ofLp y) p := by
    intro p
    split_ifs with hp
    · refine (bilPlaq_dv U _ p).trans ?_
      have hd := hol_strat hS hell hR1 hM1 U ρ hρ hreg p hp
      have hdn : 0 ≤ AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p) :=
        AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _
      -- each bond of `p` has its tail within distance 1 of `p₀`
      set s := AdalyFormal.M1.strat S k p.1
      have hy : ∀ b : Bond Lf, pdist p.1 b.1 ≤ 2 →
          ‖(WithLp.ofLp x) b‖ ^ 2 / ((ell : ℝ) ^ s) ^ 2 ≤ (ell : ℝ) ^ 2 * ‖(WithLp.ofLp y) b‖ ^ 2 := by
        intro b hb
        have h1 := inv_strat_le hS hell hR1 hM1 hb
        have e : ‖(WithLp.ofLp y) b‖ ^ 2 = ‖(WithLp.ofLp x) b‖ ^ 2 * (1 / ((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1) ^ 2) := by
          show ‖(bondWt (-sigG (geomOf ell k S)) x) b‖ ^ 2 = _
          rw [bondWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, mul_comm]
          congr 1
          exact exp_neg_sig_sq hS hell hR1 hM1 b.1
        rw [e, div_eq_mul_one_div]
        have := mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖(WithLp.ofLp x) b‖)
        rw [div_eq_mul_one_div ((ell : ℝ) ^ 2)] at this
        nlinarith [sq_nonneg ‖(WithLp.ofLp x) b‖]
      have hb1 : pdist p.1 (p.1, p.2.1.1).1 ≤ 2 := by simp [AdalyFormal.StatementLaneR8.pdist_self]
      have hb2 : pdist p.1 (p.1, p.2.1.2).1 ≤ 2 := by simp [AdalyFormal.StatementLaneR8.pdist_self]
      have hb3 : pdist p.1 (periodicLatticeShift p.1 p.2.1.1, p.2.1.2).1 ≤ 2 := pdist_corner1 hS hell hR1 hM1 p.1 _
      have hb4 : pdist p.1 (periodicLatticeShift p.1 p.2.1.2, p.2.1.1).1 ≤ 2 := pdist_corner1 hS hell hR1 hM1 p.1 _
      have hpbs : plaqBondSq (WithLp.ofLp x) p / ((ell : ℝ) ^ s) ^ 2 ≤ (ell : ℝ) ^ 2 * plaqBondSq (WithLp.ofLp y) p := by
        unfold plaqBondSq
        have := hy _ hb1; have := hy _ hb2; have := hy _ hb3; have := hy _ hb4
        rw [add_div, add_div, add_div]
        nlinarith
      have hpos : (0 : ℝ) < ((ell : ℝ) ^ s) ^ 2 := by have : (0:ℝ) < ell := (by exact_mod_cast (show 0 < ell by omega)); positivity
      have hX0 := plaqBondSq_nonneg (WithLp.ofLp x) p
      calc (34 / Real.sqrt 2) * AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p) * plaqBondSq (WithLp.ofLp x) p
          ≤ (34 / Real.sqrt 2) * (ρ * (ell : ℝ) ^ 2 / ((ell : ℝ) ^ s) ^ 2) * plaqBondSq (WithLp.ofLp x) p :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by positivity)) hX0
        _ = (34 / Real.sqrt 2) * (ρ * (ell : ℝ) ^ 2) * (plaqBondSq (WithLp.ofLp x) p / ((ell : ℝ) ^ s) ^ 2) := by ring
        _ ≤ (34 / Real.sqrt 2) * (ρ * (ell : ℝ) ^ 2) * ((ell : ℝ) ^ 2 * plaqBondSq (WithLp.ofLp y) p) :=
            mul_le_mul_of_nonneg_left hpbs (by positivity)
        _ = _ := by ring
    · rw [abs_zero]
      have := plaqBondSq_nonneg (WithLp.ofLp y) p
      positivity
  have hsum := pbs_sum_le y
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc (1 / 2) * |∑ p : PeriodicLatticePlaquette Lf, (if p ∈ plaqIn (S.Om 0) then bilPlaq U p (WithLp.ofLp x) (WithLp.ofLp x) else 0)|
      ≤ (1 / 2) * ∑ p : PeriodicLatticePlaquette Lf, (34 / Real.sqrt 2) * (ρ * (ell : ℝ) ^ 4) * plaqBondSq (WithLp.ofLp y) p :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p _ => hpt p))) (by norm_num)
    _ = (17 / Real.sqrt 2) * (ρ * (ell : ℝ) ^ 4) * ∑ p : PeriodicLatticePlaquette Lf, plaqBondSq (WithLp.ofLp y) p := by
        rw [← Finset.mul_sum]; ring
    _ ≤ (17 / Real.sqrt 2) * (ρ * (ell : ℝ) ^ 4) * (12 * ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4) * ‖y‖ ^ 2 := by ring

end strat

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.plaqMul_apply
#print axioms AdalyFormal.M1IMS.deltaPrime_diag
#print axioms AdalyFormal.M1IMS.exp_neg_sig_sq
#print axioms AdalyFormal.M1IMS.inv_strat_le
#print axioms AdalyFormal.M1IMS.deltaPrime_strat
#print axioms AdalyFormal.M1IMS.plaqMul
