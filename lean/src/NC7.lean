import NC5

/-!
# NC7 -- the coverage-free headline forces `Ginv` (3.122) to be invertible at every coverage-free class member of the NC5 instances
(lane nocover_20261015)

* `genForm_of_not_unit`: at any parameter point where `Ginv = Δ_π + DRD* + Q*aQ` (3.122) is NOT invertible, the encoded objects take
  their `Ring.inverse` junk values (`G = 0`, `H = 0`, hence `G₁⁻¹ = Ginv`, `G₁ = 0`, `QG₁Q* = 0`), and
  `genForm B = - a ⟪B, B⟫`.
* `instIneq_fails_of_not_unit`: on the NC5 instance, for every `γ₀ ≥ 0`, `a > 0` and every configuration `U` at which `Ginv` is not
  invertible, `InstIneq` FAILS (witness `B̃ = BseedNc`, with `C B̃ ≠ 0`).
* `nc_forces_unit`: `P428Target8NC` implies: for every `ell ≥ 3`, `a > 0` there is `m₀` such that for every `m ≥ m₀` there is `R₀` such that
  for every `R ≥ max R₀ 1` and EVERY `v ∈ SU(2)`, `Ginv` is invertible at `(ncS, 1[b* ↦ v], a)`.
  (Contrapositive: one `v` with `Ginv` singular on these instances, for arbitrarily large `m` and `R`, refutes `P428Target8NC`.)
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NoCover

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.FullReparamC (freeBond freeBond_not_dropped)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

theorem data_H_zero (P : IngrBParams) (h : ¬ IsUnit P.data.Ginv) : P.data.H = 0 := by
  unfold BaseDataS.H BaseDataS.G
  rw [Ring.inverse_non_unit _ h]
  simp only [ContinuousLinearMap.zero_comp]

theorem G1inv_eq_Ginv (P : IngrBParams) (h : ¬ IsUnit P.data.Ginv) : P.G1inv = P.data.Ginv := by
  apply BaseDataS.G1inv_unique P.data P.G1inv_spec
  refine ⟨fun x y => P.data.Ginv_symm P.data_laws x y, fun A => ?_⟩
  rw [BaseDataS.K_eq, data_H_zero P h]
  simp only [zero_apply, inner_zero_left, mul_zero, sub_zero]

/-- junk evaluation of the encoded (3.156) form when `Ginv` (3.122) is singular. -/
theorem genForm_of_not_unit (P : IngrBParams) (h : ¬ IsUnit P.data.Ginv) (B : BondFnL2 P.Lu) :
    GenP.genForm P B = - P.a * ⟪B, B⟫ := by
  have hG1 : P.data.G1 P.G1inv = 0 := by
    unfold BaseDataS.G1
    rw [G1inv_eq_Ginv P h, Ring.inverse_non_unit _ h]
  have hN : GenP.Nmat P = 0 := by
    unfold GenP.Nmat
    rw [hG1]; simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  have hH1 : P.H1in = 0 := by
    unfold IngrBParams.H1in BaseDataS.H1
    rw [hG1]; simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  unfold GenP.genForm GenP.firstTerm
  rw [hN, hH1, Ring.inverse_zero]
  simp only [zero_apply, inner_zero_left, inner_zero_right, mul_zero, sub_zero, zero_sub]
  ring

/-- on the NC5 instance: `InstIneq` fails at every configuration where `Ginv` is singular. -/
theorem instIneq_fails_of_not_unit {ell M R : ℕ} (hell : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (_hR : 1 ≤ R)
    {a γ₀ : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ₀) (U : LinkCfg (scaleUp ell 1 (ncLu M R)))
    (h : ¬ IsUnit (gparams ell 1 (ncLu M R) (by omega) (ncS ell M R) U a (ncLam M R)).data.Ginv) :
    ¬ InstIneq ell 1 (by omega) a (ncLu M R) γ₀ (ncS ell M R) (ncLam M R) U := by
  intro hI
  obtain ⟨h1, h2, h3, -⟩ := BseedNc_props (R := R) hell hdvd hM
  have hI' := hI (BseedNc (R := R) ell hM) h1 h2
  rw [genForm_of_not_unit _ h] at hI'
  -- `C B̃` is nonzero at the free bond
  have hell2 : 2 ≤ ell := by omega
  have hdvd' : ∀ μ : Fin 3, ell ∣ ncLu M R μ + 1 := fun μ => by
    rw [ncLu_succ hM]; exact Dvd.dvd.mul_right hdvd _
  have hy : yNc (R := R) hM ∈ CoarseLattice (ncLu M R) ell := by
    rw [mem_CoarseLattice]
    intro μ
    show (if μ = 0 then M * (2 * R + 2) else 0) % ell = 0
    split_ifs
    · exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right hdvd _)
    · simp
  set Bt := BseedNc (R := R) ell hM
  set P := gparams ell 1 (ncLu M R) (by omega) (ncS ell M R) U a (ncLam M R)
  have hnd : ¬ IsDroppedIn (ncLam M R) ell (freeBond ell (yNc (R := R) hM)) := by
    rintro ⟨c, -, hc⟩
    exact freeBond_not_dropped hell2 hdvd' (yNc (R := R) hM) hy ⟨c, hc⟩
  have hC : GenP.genC P Bt (freeBond ell (yNc (R := R) hM)) = suTwoWitness := by
    show Cop (ncLam M R) P.Q1 Bt (freeBond ell (yNc (R := R) hM)) = suTwoWitness
    rw [Cop_id _ _ _ _ hnd]
    exact Pi.single_eq_same _ _
  have hpos : 0 < ⟪(WithLp.toLp 2 (GenP.genC P Bt) : BondFnL2 (ncLu M R)),
      (WithLp.toLp 2 (GenP.genC P Bt) : BondFnL2 (ncLu M R))⟫ := by
    rw [real_inner_self_eq_norm_sq]
    have hne : (WithLp.toLp 2 (GenP.genC P Bt) : BondFnL2 (ncLu M R)) ≠ 0 := by
      intro h0
      have := congrArg (fun f : BondFnL2 (ncLu M R) => (WithLp.ofLp f) (freeBond ell (yNc (R := R) hM))) h0
      have h00 : GenP.genC P Bt (freeBond ell (yNc (R := R) hM)) = 0 := by simpa using this
      rw [hC] at h00
      exact suTwoWitness_ne_zero h00
    have := norm_pos_iff.mpr hne
    positivity
  have hE : 0 ≤ γ₀ * bondEnergy Bt := mul_nonneg hγ h3.le
  have : -P.a * ⟪(WithLp.toLp 2 (GenP.genC P Bt) : BondFnL2 (ncLu M R)),
      (WithLp.toLp 2 (GenP.genC P Bt) : BondFnL2 (ncLu M R))⟫ < 0 := by
    have hPa : P.a = a := rfl
    rw [hPa]; nlinarith
  linarith

/-- **`P428Target8NC` forces `Ginv` (3.122) to be invertible at every `1[b* ↦ v]` on the NC5 instances.** -/
theorem nc_forces_unit (h : AdalyFormal.NoCover.P428Target8NC) :
    ∀ (ell : ℕ) (hell : 3 ≤ ell) (a : ℝ), 0 < a →
      ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ (hR : 1 ≤ R) (v : Matrix.specialUnitaryGroup (Fin 2) ℂ),
        IsUnit (gparams ell 1 (ncLu (ell ^ m) R) (by omega) (ncS ell (ell ^ m) R)
          (Function.update (fun _ => 1) ((xsNc ell (ell ^ m) R hell (pow_pos (by omega) m) hR, 1) : Bond _) v) a
          (ncLam (ell ^ m) R)).data.Ginv := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell (by omega) a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hm'
  refine ⟨R₀, fun R hR' hR1 v => ?_⟩
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hcore⟩ := hR R hR'
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega)
  have hMr : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by exact_mod_cast hM
  set α₀ : ℝ := a₀ / (12 * ((ell ^ m : ℕ) : ℝ)) with hα
  have hα0 : 0 < α₀ := by rw [hα]; positivity
  have hαS : ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by
    rw [hα]; field_simp; norm_num
  have hcls : PerCubeRegular2 ell (ell ^ m) 12 1 (ncS ell (ell ^ m) R) α₀ ((ell : ℝ) ^ 1)⁻¹
      (Function.update (fun _ => 1) ((xsNc ell (ell ^ m) R hell hM hR1, 1) : Bond _) v) := by
    have hη : (0 : ℝ) < ((ell : ℝ) ^ 1)⁻¹ := by
      have : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
      positivity
    exact perCube_update (perCube_one (by omega) hM (by norm_num) hα0 hη) _
      (fun sites j hq => xsNc_uncovered hell hM hR1 sites j hq) v
  have hI := hcore 1 le_rfl (ncLu (ell ^ m) R) α₀ hα0 hαS (torusOK_nc hell hdvd hM) (ncS ell (ell ^ m) R)
    (nc_admissible hell hM hR1) (ncLam (ell ^ m) R) (lambdaOK2_nc hell hdvd hM hR1) _ hcls
  by_contra hn
  exact instIneq_fails_of_not_unit hell hdvd hM hR1 ha hγ.le _ hn hI

#print axioms data_H_zero
#print axioms G1inv_eq_Ginv
#print axioms genForm_of_not_unit
#print axioms instIneq_fails_of_not_unit
#print axioms nc_forces_unit

end AdalyFormal.NoCover
