import R7Fork.ZGU1M

/-!
# GU1N -- the ingredient lane's CLOSED INSTANCE `IngrB_genuine` extended from `k = 0` (`IngrB0`) to ALL `k`
at flat `U`, full tower: both hypotheses of `toIngr` (`hb`, `hunit`) are PROVED, with `hunit` obtained from
`unit_of_chain` using a coercivity constant of `G⁻¹` obtained by compactness (it depends on the torus;
no uniformity of that constant in `Lu` or `k` is claimed).   Standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.GenuineU1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Ingr)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)

/-- a positive semidefinite, definite quadratic form on a finite-dimensional inner product space is coercive -/
theorem coercive_of_posdef {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : E →L[ℝ] E) (hnn : ∀ x, 0 ≤ ⟪x, M x⟫)
    (hpd : ∀ x, ⟪x, M x⟫ = 0 → x = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, M x⟫ := by
  by_cases hE : Subsingleton E
  · refine ⟨1, one_pos, fun x => ?_⟩
    have : x = 0 := Subsingleton.elim _ _
    simp [this]
  · have hne : (Metric.sphere (0 : E) 1).Nonempty := by
      haveI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
      exact NormedSpace.sphere_nonempty.mpr zero_le_one
    have hcomp : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
    have hcont : ContinuousOn (fun x : E => ⟪x, M x⟫) (Metric.sphere (0 : E) 1) := by
      apply Continuous.continuousOn
      fun_prop
    obtain ⟨x0, hx0, hmin⟩ := hcomp.exists_isMinOn hne hcont
    have hx0n : ‖x0‖ = 1 := by simpa using hx0
    have hpos : 0 < ⟪x0, M x0⟫ := by
      rcases lt_or_eq_of_le (hnn x0) with h | h
      · exact h
      · exfalso
        have := hpd x0 h.symm
        rw [this] at hx0n; simp at hx0n
    refine ⟨⟪x0, M x0⟫, hpos, fun x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      set u : E := (‖x‖⁻¹) • x with hu
      have hun : u ∈ Metric.sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
      have h1 : ⟪x0, M x0⟫ ≤ ⟪u, M u⟫ := hmin hun
      have h2 : ⟪u, M u⟫ = (‖x‖⁻¹) ^ 2 * ⟪x, M x⟫ := by
        rw [hu, map_smul, inner_smul_left, inner_smul_right]
        simp only [conj_trivial]; ring
      have h3 : ⟪x, M x⟫ = ‖x‖ ^ 2 * ⟪u, M u⟫ := by
        rw [h2]; field_simp
      rw [h3]
      nlinarith [sq_nonneg ‖x‖, h1]

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))
local notation "PP" => PK ell k Lu hell a Lam

theorem PK_G1inv_nonneg (ha : 0 < a) (x : ↥(bondSupp (PP).G)) : 0 ≤ ⟪x, (PP).G1inv x⟫ := by
  have hFS : (PP).FullSupp := PK_fullSupp ell k Lu hell a Lam
  have hpos : 0 < a * (ell : ℝ) ^ k := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  rw [Gen.G1inv_form (PP) hFS (PK_Om0_univ ell k Lu hell a Lam) rfl]
  have h3 := mul_nonneg hpos.le (sq_nonneg ‖(PP).data.Q x‖)
  have h1 := sq_nonneg ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G x)‖
  have h2 := sq_nonneg ‖Tfull (PP).G (PP).U (iE (PP).G x)‖
  show 0 ≤ ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G x)‖ ^ 2 +
      ‖Tfull (PP).G (PP).U (iE (PP).G x)‖ ^ 2 + a * (ell : ℝ) ^ k * ‖(PP).data.Q x‖ ^ 2
  linarith

theorem PK_G1inv_coercive (hN : ∀ μ, 1 ≤ Lu μ) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ↥(bondSupp (PP).G), c * ‖x‖ ^ 2 ≤ ⟪x, (PP).G1inv x⟫ :=
  coercive_of_posdef (PP).G1inv (PK_G1inv_nonneg ell k Lu hell a Lam ha)
    (fun x hx => PK_pd0 ell k Lu hell a Lam hN ha x hx)

theorem PK_Delta2_zero : (PP).data.Delta2 (PP).data_laws = 0 := by
  obtain ⟨hs, hf⟩ := (PP).data.Delta2_spec (PP).data_laws
  refine symm_unique hs (fun x y => by simp) (fun A => ?_)
  rw [hf A]
  have hJ : (PP).data.J = 0 := by
    show (pE (PP).G) (PP).Jf = 0
    rw [Jf_flat (PP) rfl]; exact map_zero _
  rw [hJ]; simp

/-- **`hunit` of `toIngr` at flat `U`, full tower, ALL `k`** -/
theorem PK_hunit (hN : ∀ μ, 1 ≤ Lu μ) (ha : 0 < a) :
    IsUnit (((PP).Qin.comp (PP).G1in).comp (ContinuousLinearMap.adjoint (PP).Qin)) := by
  obtain ⟨c, hc, hco⟩ := PK_G1inv_coercive ell k Lu hell a Lam hN ha
  have hτ : Function.Bijective (PP).tau := IngrBParams.tau_bijective _ (PK_fullSupp ell k Lu hell a Lam)
  have hJ : (PP).data.J = 0 := by
    show (pE (PP).G) (PP).Jf = 0
    rw [Jf_flat (PP) rfl]; exact map_zero _
  refine IngrBParams.unit_of_chain (PP) hτ (c := c) (ε := 0) hc (fun x => ?_) ?_
    (PK_Qs_injective ell k Lu hell a Lam) (IngrBParams.eta_pos _)
  · have h1 := hco x
    have h2 := (PP).G1inv_spec.form x
    rw [BaseDataS.K_eq, hJ, inner_zero_right, mul_zero, sub_zero] at h2
    rw [← h2]; exact h1
  · rw [PK_Delta2_zero]; exact le_of_eq ContinuousLinearMap.opNorm_zero

/-- the CLOSED genuine ingredient structure at level `k` (flat `U`, full tower): the ingredient lane's
`IngrB0` for all `k`. -/
noncomputable def IngrBk (hN : ∀ μ, 1 ≤ Lu μ) (hdvd : ∀ μ, ell ∣ Lu μ + 1) (ha : 0 < a) :
    Ingr ell Lu (scaleUp ell k Lu) Lam :=
  IngrBParams.IngrB_genuine (PP) (IngrBParams.hb_flat (PP) rfl hdvd) (PK_hunit ell k Lu hell a Lam hN ha)

/-- the variational characterisation at the genuine point (needs only `WellDef`, proved) -/
theorem PK_genForm_eq_min (hN : ∀ μ, 1 ≤ Lu μ) (hdvd : ∀ μ, ell ∣ Lu μ + 1) (ha : 0 < a)
    (B : BondFnL2 Lu) :
    ∃ A : ↥(bondSupp (PP).G), (PP).data.Q A = ContinuousLinearMap.adjoint (PP).tau B ∧
      GenP.genForm (PP) B = (PP).eta * (‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G A)‖ ^ 2 +
        ‖Tfull (PP).G (PP).U (iE (PP).G A)‖ ^ 2) ∧
      ∀ A' : ↥(bondSupp (PP).G), (PP).data.Q A' = ContinuousLinearMap.adjoint (PP).tau B →
        GenP.genForm (PP) B ≤ (PP).eta * (‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G A')‖ ^ 2 +
        ‖Tfull (PP).G (PP).U (iE (PP).G A')‖ ^ 2) :=
  Gen.genForm_eq_min (PP) (PK_fullSupp ell k Lu hell a Lam) (PK_Om0_univ ell k Lu hell a Lam) rfl
    (PK_isUnit_G1inv ell k Lu hell a Lam hN ha) (PK_isUnit_Nmat ell k Lu hell a Lam hN ha) ha B

end

#print axioms PK_genForm_eq_min
#print axioms coercive_of_posdef
#print axioms PK_G1inv_coercive
#print axioms PK_Delta2_zero
#print axioms PK_hunit
#print axioms IngrBk

end AdalyFormal.GenuineU1
