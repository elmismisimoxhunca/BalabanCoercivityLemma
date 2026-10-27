import ZGU1H

/-!
# GU1I -- FEASIBILITY (`WellDef`) of the genuine construction at flat `U`, full tower, ANY level `k`
and ANY blocking `ell ≥ 1` (torus tiling `ell ∣ Lu μ + 1`, `1 ≤ Lu μ`), `a > 0`:
  `H₀` bijective  ∧  `IsUnit G₁⁻¹`  ∧  `IsUnit (Q G₁ Q*)`.
Standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.GenuineU1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.FullySupplied (suTwoLift lineCoarseRestrictSuTwo_suTwoLift)

theorem bondSupp_G (ell k : ℕ) (Lu : PeriodicLatticeExtent) (A : BondFnL2 (scaleUp ell k Lu)) :
    A ∈ bondSupp (geomOf ell k (fullTower ell k Lu)) := by
  intro b hb
  exfalso
  apply hb
  unfold bondsOm0
  rw [G_Om0]
  exact Or.inl (Set.mem_univ _)

namespace Gen
variable (P : IngrBParams)

/-- the quadratic form of `G₁⁻¹` at flat `U`, full support -/
theorem G1inv_form (hFS : P.FullSupp) (hOm : P.G.Om0 = Set.univ) (hU : P.U = flatCfg) (x : ↥(bondSupp P.G)) :
    ⟪x, P.G1inv x⟫ = ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G x)‖ ^ 2 +
      ‖Tfull P.G P.U (iE P.G x)‖ ^ 2 + P.a * (P.ell : ℝ) ^ P.k * ‖P.data.Q x‖ ^ 2 := by
  have hJ : P.Jf = 0 := Jf_flat P hU
  have hJd : P.data.J = 0 := by
    show (pE P.G) P.Jf = 0
    rw [hJ]; exact map_zero _
  rw [P.G1inv_spec.form x]
  unfold BaseDataS.K
  rw [hJd, inner_zero_right, mul_zero, sub_zero, mass_inner P hFS]
  have hD : ⟪x, P.data.Dpi x⟫ = ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G x)‖ ^ 2 := by
    have : ⟪x, P.data.Dpi x⟫ = ⟪iE P.G x, DpiFull P.G P.U P.a (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (DpiFull P.G P.U P.a (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, hU]
    exact inner_DpiFull_flat_univ P.G hOm P.a (iE P.G x)
  rw [hD]
  rfl

end Gen

#print axioms bondSupp_G
#print axioms Gen.G1inv_form

section PKfacts
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))

local notation "PP" => PK ell k Lu hell a Lam

/-- positive definiteness of the genuine `G₁⁻¹` form (the content of "`Δ_a` positive definite", flat) -/
theorem PK_pd0 (hN : ∀ μ, 1 ≤ Lu μ) (ha : 0 < a) (x : ↥(bondSupp (PP).G))
    (h0 : ⟪x, (PP).G1inv x⟫ = 0) : x = 0 := by
  have hFS : (PP).FullSupp := PK_fullSupp ell k Lu hell a Lam
  rw [Gen.G1inv_form (PP) hFS (PK_Om0_univ ell k Lu hell a Lam) rfl] at h0
  have h0' : ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G x)‖ ^ 2 +
      ‖Tfull (PP).G (PP).U (iE (PP).G x)‖ ^ 2 + (PP).a * ((PP).ell : ℝ) ^ (PP).k * ‖(PP).data.Q x‖ ^ 2 = 0 := h0
  have hell' : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hc : 0 < (PP).a * ((PP).ell : ℝ) ^ (PP).k := by
    show 0 < a * (ell : ℝ) ^ k
    positivity
  have h1 := sq_nonneg ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G x)‖
  have h2 := sq_nonneg ‖Tfull (PP).G (PP).U (iE (PP).G x)‖
  have h3 := mul_nonneg hc.le (sq_nonneg ‖(PP).data.Q x‖)
  have e1 : ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G x)‖ ^ 2 = 0 := by linarith [h0']
  have e2 : ‖Tfull (PP).G (PP).U (iE (PP).G x)‖ ^ 2 = 0 := by linarith [h0']
  have e3 : (PP).a * ((PP).ell : ℝ) ^ (PP).k * ‖(PP).data.Q x‖ ^ 2 = 0 := by linarith [h0']
  have c1 : curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G x) = 0 :=
    norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp e1)
  have c2 : Tfull (PP).G (PP).U (iE (PP).G x) = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp e2)
  have c3 : (PP).data.Q x = 0 := by
    have : ‖(PP).data.Q x‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp e3 with h | h
      · exact absurd h hc.ne'
      · exact h
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  have hker := ker_trivial ell k Lu hell hN (iE (PP).G x) c1 c2 (fun e => by
    have h := congrFun (congrArg WithLp.ofLp c3) ((PP).eqv hFS e)
    have h' : ((PP).sector.Qfull (iE (PP).G x)) ((PP).eqv hFS e) = 0 := h
    rw [Qfull_top ell k Lu hell a Lam] at h'
    exact h')
  exact Subtype.ext hker

#print axioms PK_pd0


theorem PK_isUnit_G1inv (hN : ∀ μ, 1 ≤ Lu μ) (ha : 0 < a) : IsUnit (PP).G1inv := by
  have hinj : Function.Injective ((PP).G1inv : ↥(bondSupp (PP).G) →ₗ[ℝ] ↥(bondSupp (PP).G)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine PK_pd0 ell k Lu hell a Lam hN ha x ?_
    have : (PP).G1inv x = 0 := hx
    rw [this, inner_zero_right]
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩

theorem PK_Q_surj (y : FSp (PP).G) : ∃ x : ↥(bondSupp (PP).G), (PP).data.Q x = y := by
  have hFS : (PP).FullSupp := PK_fullSupp ell k Lu hell a Lam
  have hpos : 0 < ell ^ k := pow_pos hell k
  let F : CoarseBond (scaleUp ell k Lu) (ell ^ k) → SuTwo :=
    fun c => (WithLp.ofLp y) ((PP).eqv hFS ((bondsE ell k Lu hell).symm c))
  let A : BondFnL2 (scaleUp ell k Lu) := WithLp.toLp 2 (suTwoLift (ell ^ k) F)
  refine ⟨⟨A, bondSupp_G ell k Lu A⟩, ?_⟩
  refine PiLp.ext (fun p => ?_)
  obtain ⟨e, rfl⟩ := ((PP).eqv hFS).surjective p
  show ((PP).sector.Qfull A) ((PP).eqv hFS e) = _
  rw [Qfull_top ell k Lu hell a Lam]
  show lineCoarseRestrictSuTwo (ell ^ k) (suTwoLift (ell ^ k) F) (bondsE ell k Lu hell e) = _
  rw [lineCoarseRestrictSuTwo_suTwoLift hpos (scaleUp_tiling ell k Lu hell) F]
  simp [F]

theorem PK_Qs_injective : Function.Injective (PP).data.Qs := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨x, hx⟩ := PK_Q_surj ell k Lu hell a Lam w
  have h1 : ⟪(PP).data.Q x, w⟫ = ⟪x, (PP).data.Qs w⟫ := (PP).data.Q_adj x w
  rw [hw, inner_zero_right, hx] at h1
  exact inner_self_eq_zero.mp h1

theorem PK_isUnit_Nmat (hN : ∀ μ, 1 ≤ Lu μ) (ha : 0 < a) : IsUnit (GenP.Nmat (PP)) := by
  have hG := PK_isUnit_G1inv ell k Lu hell a Lam hN ha
  have hinj : Function.Injective ((GenP.Nmat (PP)) : FSp (PP).G →ₗ[ℝ] FSp (PP).G) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    set A : ↥(bondSupp (PP).G) := (PP).data.G1 (PP).G1inv ((PP).data.Qs z) with hA
    have hG1 : (PP).G1inv A = (PP).data.Qs z := by
      have := Ring.mul_inverse_cancel _ hG
      exact ContinuousLinearMap.ext_iff.mp this ((PP).data.Qs z)
    have hNz : GenP.Nmat (PP) z = (PP).data.Q A := rfl
    have hz' : GenP.Nmat (PP) z = 0 := hz
    have h0 : ⟪A, (PP).G1inv A⟫ = 0 := by
      rw [hG1, ← (PP).data.Q_adj, ← hNz, hz', inner_zero_left]
    have hA0 : A = 0 := PK_pd0 ell k Lu hell a Lam hN ha A h0
    have : (PP).data.Qs z = 0 := by rw [← hG1, hA0, map_zero]
    exact PK_Qs_injective ell k Lu hell a Lam (by rw [this, map_zero])
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩

/-- **FEASIBILITY OF THE GENUINE CONSTRUCTION, flat `U`, full tower, ALL `k`, all `ell ≥ 1`.** -/
theorem PK_wellDef (hN : ∀ μ, 1 ≤ Lu μ) (hdvd : ∀ μ, ell ∣ Lu μ + 1) (ha : 0 < a) :
    GenP.WellDef (PP) :=
  ⟨IngrBParams.hb_flat (PP) rfl hdvd, PK_isUnit_G1inv ell k Lu hell a Lam hN ha,
   PK_isUnit_Nmat ell k Lu hell a Lam hN ha⟩

#print axioms PK_isUnit_G1inv
#print axioms PK_Q_surj
#print axioms PK_Qs_injective
#print axioms PK_isUnit_Nmat
#print axioms PK_wellDef
end PKfacts

end AdalyFormal.GenuineU1
