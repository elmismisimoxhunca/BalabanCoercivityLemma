
namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## K. Assembly: the soft premise `InteriorSoft` of round 1 holds -/
section FlatCarrier

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply)

/-- The flat localized carrier form is a sum of three squares (frozen `NsPtD1.flat_ginv_form`,
outside the `DrEquiv` closure, restated for the pinned localized assembly). -/
theorem flat_ginv_form_in (P : IngrBParams) (hU : P.U = flatCfg) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selIn selIn P).Ginv x⟫ =
      ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2
      + ‖Tfull P.G P.U (iE P.G x)‖ ^ 2
      + ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
  rw [BaseDataS.inner_Ginv]
  have hD : ⟪x, (dataS selIn selIn P).Dpi x⟫ =
      ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2 := by
    have : ⟪x, (dataS selIn selIn P).Dpi x⟫ = ⟪iE P.G x, DpiFull P.G P.U P.a (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (DpiFull P.G P.U P.a (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, hU]
    exact AdalyFormal.StatementLaneG.inner_DpiFull_flat P.G P.a (iE P.G x)
  have hM : ⟪x, (dataS selIn selIn P).Mass x⟫ =
      ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
    have : ⟪x, (dataS selIn selIn P).Mass x⟫ = ⟪iE P.G x, MassFull P.G P.a P.sector (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (MassFull P.G P.a P.sector (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, inner_MassFull]
    rfl
  rw [hD, hM]
  rfl

/-- The flat localized carrier of the dilated tower is positive definite. -/
theorem dil_flat_pos {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (hx : x ≠ 0) :
    0 < ⟪x, (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv x⟫ := by
  set P := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R) with hP
  have hform := flat_ginv_form_in P rfl x
  have t1 := sq_nonneg ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖
  have t2 := sq_nonneg ‖Tfull P.G P.U (iE P.G x)‖
  have hell : (0 : ℝ) < P.ell := by show (0 : ℝ) < (2 : ℕ); norm_num
  have t3 : 0 ≤ ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 :=
    Finset.sum_nonneg (fun p _ => by
      have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
      positivity)
  rcases (add_nonneg (add_nonneg t1 t2) t3).lt_or_eq with h | h
  · rw [hform]; exact h
  · exfalso
    apply hx
    have h1 : ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2 = 0 := by
      linarith
    have h2 : ‖Tfull P.G P.U (iE P.G x)‖ ^ 2 = 0 := by linarith
    have h3 : ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by
      linarith
    have hm : plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x)) = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
    have hT : Tfull P.G P.U (iE P.G x) = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
    have hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg (iE P.G x) = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by
        have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
        positivity)).mp h3
      refine PiLp.ext (fun p => ?_)
      have h1 := hz p (Finset.mem_univ p)
      have hp : 0 < P.a * (P.ell : ℝ) ^ (p.1 : ℕ) := by
        have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
        positivity
      have h2 : ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hp.ne'
        · exact h
      have := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
      exact this
    have hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → (iE P.G x) b = 0 :=
      fun b hb => x.2 b hb
    have hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0),
        curlValueCovariant flatCfg (WithLp.ofLp (iE P.G x)) p = 0 := by
      intro p hp
      have h := congrArg (fun v : AdalyFormal.Balaban.CovariantHjMinimizer.PlaqFnL2 P.Lf => WithLp.ofLp v p) hm
      simp only [plaqMask_apply, PiLp.zero_apply] at h
      rw [if_pos (show p ∈ plaqIn P.G.Om0 from hp)] at h
      have e : curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x) =
          WithLp.toLp 2 (curlValueCovariant flatCfg (WithLp.ofLp (iE P.G x))) :=
        curlCovariantCLM_L2_toLp _ _
      rw [e] at h
      exact h
    have hA := dil_flat_kernel hq hR (iE P.G x) hsupp hQ hcurl hT
    exact Subtype.ext hA

theorem dil_flat_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv := by
  set M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
    (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv with hMdef
  have hinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have := dil_flat_pos hq hR x hne
    rw [hx, inner_zero_right] at this
    exact lt_irrefl _ this
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →ₗ[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))))).mp hinj⟩

end FlatCarrier

end AdalyFormal.Round9.Guarded.AnalyticR2
