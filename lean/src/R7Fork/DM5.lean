import R7Fork.DM5a
import R7Fork.ZT5A

/-!
# DM5 -- THE U=1 FLOOR AT A PROPER TOWER (conditional on the two `Ring.inverse` units of `WellDef`).
**[SUPERSEDED IN PLACE (S75, 2026-10-10): `IsUnit N` is a theorem (`DM7f.isUnit_Nmat_of_G1inv`) and `IsUnit G1inv` is a theorem (`DM13i.isUnit_G1inv_proper`); the unconditional statement is `DM14.closed_point_proper_unconditional`. The conditional form below is RETAINED as the history of this module.]**
`ell = 2`, flat `U`, ANY admissible tower `S` (multi-stratum, `Omega_0` a proper subset allowed), ANY `Lambda` with `LambdaOK2`, `3 <= R M`:
   `(1/1728) ||B~||^2 <= genForm(C B~)`    for every `B~ in Lambda~` with touching support,
provided `IsUnit G1inv` and `IsUnit N` at that tower.  The constant is the whole-torus constant; the comparison is DIRECT
(no min-over-smaller-set argument): `genForm = eta(||chi_{plaqIn} curl A||^2 + ||T A||^2 + <A,Mass A>) - a||B||^2`, mass cancels the `-a||B||^2` exactly
(level-`k` terms only), the local Stokes comparison replaces the global one, and Lemma 2.4 is applied on the unit torus to `C B~`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlCovariantLM)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue curlCovariantLM_trivialU_eq_flatCurlLM)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.IngredientFamily (q1SU2)

theorem closed_point_proper_cond {k : ℕ} {Lu : PeriodicLatticeExtent} (hL : ∀ μ : Fin 3, 4 ≤ Lu μ)
    (hd : ∀ μ, 2 ∣ Lu μ + 1) {M R : ℕ} (hRM : 3 ≤ R * M) (hell : 0 < 2) (a : ℝ) (ha : 0 < a)
    (S : Tower (scaleUp 2 k Lu)) (hS : Admissible 2 M R k S)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLam : LambdaOK2 2 M R k S Lam)
    (hG : IsUnit (gparams 2 k Lu hell S flatCfg a Lam).G1inv)
    (hN : IsUnit (GenP.Nmat (gparams 2 k Lu hell S flatCfg a Lam))) :
    InstIneq 2 k hell a Lu (1 / 1728 : ℝ) S Lam flatCfg := by
  intro Bt hBt hBT
  set P := gparams 2 k Lu hell S flatCfg a Lam with hP
  have hU : P.U = flatCfg := rfl
  have hu : ∀ μ, 1 ≤ Lu μ := fun μ => by have := hL μ; omega
  have hQ1 : P.Q1 = q1SU2 2 := Q1_eq_q1SU2 P hU hd
  have hb : Function.Bijective (H0 Lam (q1SU2 2)) := by
    have := IngrBParams.hb_flat P hU hd
    rw [hQ1] at this
    exact this
  have hgen : GenP.genC P Bt = Cop Lam (q1SU2 2) Bt := by
    unfold GenP.genC; rw [hQ1]
  obtain ⟨hax, hker, hen, hsup⟩ := Cop_props_gen hd hu hLam.2 hb Bt hBt hBT
  set Bf := Cop Lam (q1SU2 2) Bt with hBf
  have h24 := lemma24_flat hL hd Bf hax hker
  rw [hgen]
  obtain ⟨A, hQA, hform⟩ := genForm_reduction_gen P hU hG hN (WithLp.toLp 2 Bf)
  have hMR : 1 ≤ R * M := le_trans (by norm_num) hRM
  -- the mass term: Bf lives on embedded frakB-bonds
  have hsuppB : ∀ e : Bond Lu, unitBondEmb P.ell P.k P.Lu P.hell e ∉ bondsLam P.G P.k →
      (WithLp.ofLp (WithLp.toLp 2 Bf : BondFnL2 Lu)) e = 0 := by
    intro e he
    by_contra hne
    exact he (touching_in_frakB hell hu hMR hS hLam.1 e (hsup e hne))
  have hmass := mass_ge_gen P ha.le A (WithLp.toLp 2 Bf) hQA hsuppB
  -- local Stokes
  have hQloc : ∀ e : Bond Lu, embY 2 k Lu hell e.1 ∈ S.Om k →
      embY 2 k Lu hell (periodicLatticeShift e.1 e.2) ∈ S.Om k →
      AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictSuTwo (2 ^ k) (WithLp.ofLp (iE P.G A))
        (bondsE 2 k Lu hell e) = Bf e := by
    intro e h1 h2
    have h := emb_bondsLam hell hS e h1
    have e1 := Qfull_top_gen P hU (iE P.G A) e h
    have e2 : (P.sector.Qfull (iE P.G A)) (pe P e h) = (ContinuousLinearMap.adjoint P.tau (WithLp.toLp 2 Bf)) (pe P e h) := by
      rw [← hQA]; rfl
    rw [← e1, e2]
    exact tauAdj_apply P (WithLp.toLp 2 Bf) e h
  have hStokes := local_unit_stokes hell hu hS (WithLp.ofLp (iE P.G A)) Bf hQloc
    (fun q hq => curl_zero_of_not_good hell hu hRM hLam.1 Bf hsup q hq)
  have hmasked := masked_curl_norm_sq (plaqIn P.G.Om0) (iE P.G A)
  -- real arithmetic
  have hpos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hEta : P.eta = (((2 ^ k : ℕ) : ℝ))⁻¹ := by
    unfold IngrBParams.eta; simp [hP, gparams]
  have hηn : P.eta * (P.ell : ℝ) ^ P.k = 1 := by
    rw [hEta]; simp [hP, gparams]
  have hcu : ∑ p : PeriodicLatticePlaquette Lu, ‖curlCovariantLM (trivialU Lu) Bf p‖ ^ 2
      = ∑ p : PeriodicLatticePlaquette Lu, ‖flatCurlValue Bf p‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [curlCovariantLM_trivialU_eq_flatCurlLM]; rfl
  set Eu := ∑ p : PeriodicLatticePlaquette Lu, ‖flatCurlValue Bf p‖ ^ 2 with hEu
  set X := ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn P.G.Om0)
          (AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
            (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G A))‖ ^ 2 with hX
  have hTT := sq_nonneg ‖Tfull P.G P.U (iE P.G A)‖
  have hStokes' : ((2 ^ k : ℕ) : ℝ) * Eu ≤ X := by
    rw [hmasked]; exact hStokes
  have h24' : (1 / 1728 : ℝ) * ∑ b : Bond Lu, ‖Bf b‖ ^ 2 ≤ Eu := by rw [← hcu]; exact h24
  have hb2 : (1 / 1728 : ℝ) * bondEnergy Bt ≤ (1 / 1728 : ℝ) * ∑ b : Bond Lu, ‖Bf b‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hen (by norm_num)
  have hEX : Eu ≤ P.eta * X := by
    rw [hEta, ← div_eq_inv_mul, le_div_iff₀ hpos]
    linarith [hStokes']
  have hη0 : 0 ≤ P.eta := P.eta_pos.le
  -- genForm >= eta * X
  have hge : P.eta * X ≤ GenP.genForm P (WithLp.toLp 2 Bf) := by
    rw [hform]
    have h1 : P.eta * (P.a * (P.ell : ℝ) ^ P.k * ‖(WithLp.toLp 2 Bf : BondFnL2 Lu)‖ ^ 2)
        = P.a * ‖(WithLp.toLp 2 Bf : BondFnL2 Lu)‖ ^ 2 := by
      calc P.eta * (P.a * (P.ell : ℝ) ^ P.k * ‖(WithLp.toLp 2 Bf : BondFnL2 Lu)‖ ^ 2)
          = (P.eta * (P.ell : ℝ) ^ P.k) * (P.a * ‖(WithLp.toLp 2 Bf : BondFnL2 Lu)‖ ^ 2) := by ring
        _ = P.a * ‖(WithLp.toLp 2 Bf : BondFnL2 Lu)‖ ^ 2 := by rw [hηn, one_mul]
    have h2 := mul_le_mul_of_nonneg_left hmass hη0
    nlinarith [h1, h2, mul_nonneg hη0 hTT]
  linarith

#print axioms closed_point_proper_cond

end AdalyFormal.DirichletMono
