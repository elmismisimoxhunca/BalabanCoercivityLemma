
namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## M. The vacuum all-plaquette carrier at angle `0` is positive definite

At the trivial background the `Δ'` part of every plaquette form vanishes, so the carrier form of
`dataS sD sJ` is `‖χ curl(W x)‖² + ‖T x‖² + Σ a ℓʲ ‖Q x‖²` with `χ` the selected plaquettes; the
all-plaquette form dominates the localized one, which is definite (section J). -/
section VacuumStart

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply)

theorem inner_Dpi_flat_sel (sD sJ : PlaqSel) (P : IngrBParams) (hU : P.U = flatCfg)
    (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS sD sJ P).Dpi x⟫ = ‖plaqMask (sD _ P.G) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf)
      (Wop P.G P.U P.a (iE P.G x)))‖ ^ 2 := by
  show ⟪x, (pE P.G) (DpiFullS sD P.G P.U P.a (iE P.G x))⟫ = _
  rw [pE_inner_right]
  simp only [DpiFullS, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, DeltaS,
    AdalyFormal.StatementLaneR6.inner_deltaKLocCLM]
  rw [hU]
  have h0 : AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc (flatCfg : Cfg P.Lf) (sD _ P.G)
      (Wop P.G flatCfg P.a (iE P.G x)) (Wop P.G flatCfg P.a (iE P.G x)) = 0 :=
    AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc_trivialU _ _ _
  rw [h0, add_zero, real_inner_self_eq_norm_sq]
  rfl

theorem norm_plaqMask_le {L : PeriodicLatticeExtent} (P : Set (PeriodicLatticePlaquette L))
    (c : AdalyFormal.Balaban.CovariantHjMinimizer.PlaqFnL2 L) : ‖plaqMask P c‖ ^ 2 ≤ ‖c‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_le_sum (fun p _ => ?_)
  rw [plaqMask_apply]
  split_ifs
  · exact le_rfl
  · simp

/-- At the trivial background the all-plaquette carrier form dominates the localized one. -/
theorem flat_sel_le (P : IngrBParams) (hU : P.U = flatCfg) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selIn selIn P).Ginv x⟫ ≤ ⟪x, (dataS selAll selAll P).Ginv x⟫ := by
  rw [BaseDataS.inner_Ginv, BaseDataS.inner_Ginv, inner_Dpi_flat_sel selIn selIn P hU,
    inner_Dpi_flat_sel selAll selAll P hU]
  have hT : (dataS selIn selIn P).T = (dataS selAll selAll P).T := rfl
  have hM : (dataS selIn selIn P).Mass = (dataS selAll selAll P).Mass := rfl
  rw [hT, hM]
  have h1 := norm_plaqMask_le (selIn _ P.G) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf)
    (Wop P.G P.U P.a (iE P.G x)))
  have h2 : plaqMask (selAll _ P.G) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf)
      (Wop P.G P.U P.a (iE P.G x))) = curlCovariantCLM_L2 (flatCfg : Cfg P.Lf)
      (Wop P.G P.U P.a (iE P.G x)) := by
    refine PiLp.ext (fun p => ?_)
    rw [plaqMask_apply, if_pos (show p ∈ selAll _ P.G from Set.mem_univ p)]
  rw [h2]
  linarith

/-- The vacuum all-plaquette carrier of the dilated tower at the trivial background is positive
definite. -/
theorem dil_flat_all_pos {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (hx : x ≠ 0) :
    0 < ⟪x, (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv x⟫ :=
  lt_of_lt_of_le (dil_flat_pos hq hR x hx)
    (flat_sel_le (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R)) rfl x)

theorem dil_flat_all_psd {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    AdalyFormal.D1Literal.PSD (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num)
      (dilTower q R) (fun _ => 1) 1 (dilLam q R))).Ginv := by
  intro v
  by_cases hv : v = 0
  · rw [hv, inner_zero_left]
  · exact (dil_flat_all_pos hq hR v hv).le

theorem dil_flat_all_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv := by
  set M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
    (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv with hMdef
  have hinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have := dil_flat_all_pos hq hR x hne
    rw [hx, inner_zero_right] at this
    exact lt_irrefl _ this
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →ₗ[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))))).mp hinj⟩

end VacuumStart

end AdalyFormal.Round9.Guarded.AnalyticR2
