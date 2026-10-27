import ZGU1E

/-!
# GU1F -- THE FLOOR AT ALL LEVELS `k` (conditional on the feasibility conjuncts `IsUnit G₁⁻¹`, `IsUnit N`):
for the GENUINE `genForm`, `genC`, `ell = 2`, flat `U`, full tower, `Λ = univ`, any `k`, any torus
`4 ≤ Lu μ`, `2 ∣ Lu μ + 1`, any `a > 0`, any `B̃ ∈ Λ̃`:   `(1/1728)‖B̃‖² ≤ genForm(C B̃)`.
Standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.GenuineU1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp OnLambdaTildeIn)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlCovariantLM curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue curlCovariantLM_trivialU_eq_flatCurlLM)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.IngredientFamily (q1SU2)

/-- the flat full-tower genuine parameters at level `k` -/
def PK (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) : IngrBParams :=
  gparams ell k Lu hell (fullTower ell k Lu) flatCfg a Lam

theorem PK_fullSupp (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) : (PK ell k Lu hell a Lam).FullSupp :=
  fullTower_fullSupp ell k Lu hell flatCfg a Lam

/-- the full tower has `Ω₀ = ` the whole torus (so the r6 plaquette localisation is the identity). -/
theorem PK_Om0_univ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) : (PK ell k Lu hell a Lam).G.Om0 = Set.univ := by
  simp [PK, gparams, IngrBParams.G, geomOf, fullTower]

theorem bgTower_PK (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (j : ℕ) :
    bgTower (PK ell k Lu hell a Lam).G (PK ell k Lu hell a Lam).U j = flatCfg := by
  unfold bgTower
  exact Ubar_flat _ j

/-- **TOP-LEVEL IDENTIFICATION**: the genuine `Q_k` (jet of the printed composite of raw maps, at the
flat tower) read at the unit bond `e` is the `ell^k`-block line average at the embedded coarse bond. -/
theorem Qfull_top (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (A : BondFnL2 (scaleUp ell k Lu)) (e : Bond Lu) :
    ((PK ell k Lu hell a Lam).sector.Qfull A)
        ((PK ell k Lu hell a Lam).eqv (PK_fullSupp ell k Lu hell a Lam) e)
      = lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp A) (bondsE ell k Lu hell e) := by
  have hell' : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have key := Qcomp_closed ell hell (bgTower (PK ell k Lu hell a Lam).G (PK ell k Lu hell a Lam).U)
    (bgTower_PK ell k Lu hell a Lam) k (scaleUp_tiling ell k Lu hell)
    (suCoordF (WithLp.ofLp A)) k le_rfl (ell ^ k) rfl (bondsE ell k Lu hell e)
  rw [suCoordFInv_suCoordF] at key
  show (((PK ell k Lu hell a Lam).G.ell : ℝ) ^ ((Fin.last k : Fin (k + 1)) : ℕ))⁻¹ •
    (WithLp.ofLp (QlinB (PK ell k Lu hell a Lam).G (PK ell k Lu hell a Lam).U ((Fin.last k : Fin (k + 1)) : ℕ) A))
      (unitBondEmb ell k Lu hell e) = _
  rw [Fin.val_last]
  have hQ : (WithLp.ofLp (QlinB (PK ell k Lu hell a Lam).G (PK ell k Lu hell a Lam).U k A))
      (unitBondEmb ell k Lu hell e) = suCoordFInv (QlinCompX ell
        (bgTower (PK ell k Lu hell a Lam).G (PK ell k Lu hell a Lam).U) k (suCoordF (WithLp.ofLp A)))
        ((bondsE ell k Lu hell e).1.1, (bondsE ell k Lu hell e).2) := by
    have hb := QlinCompL_eq_QlinCompX ell (bgTower (PK ell k Lu hell a Lam).G (PK ell k Lu hell a Lam).U) k
      (fun j _ => by rw [bgTower_PK]; exact RegBg_flat _ _) k le_rfl
    rw [← hb]; rfl
  rw [hQ, key]
  show ((ell : ℝ) ^ k)⁻¹ • (((ell ^ k : ℕ) : ℝ) • _) = _
  rw [smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (pow_ne_zero k hell'), one_smul]
  rfl

#print axioms Qfull_top

/-- the curl norm of an `L²` bond field as a plaquette sum -/
theorem curlnorm_eq {L : PeriodicLatticeExtent} (x : BondFnL2 L) :
    ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) x‖ ^ 2
      = ∑ p' : PeriodicLatticePlaquette L, ‖flatCurlValue (WithLp.ofLp x) p'‖ ^ 2 := by
  have : x = WithLp.toLp 2 (WithLp.ofLp x) := rfl
  rw [this, curlCovariantCLM_L2_toLp, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hc : curlCovariantLM (trivialU L) (WithLp.ofLp x) = flatCurlValue (WithLp.ofLp x) := by
    rw [curlCovariantLM_trivialU_eq_flatCurlLM]; rfl
  have := congrFun hc p
  simp only [WithLp.ofLp_toLp]
  exact congrArg (fun x => ‖x‖ ^ 2) this

#print axioms curlnorm_eq

/-- **THE FLOOR AT EVERY LEVEL `k` (conditional on the two feasibility conjuncts).** -/
theorem floor_cond (k : ℕ) (Lu : PeriodicLatticeExtent) (hL : ∀ μ : Fin 3, 4 ≤ Lu μ)
    (hd : ∀ μ, 2 ∣ Lu μ + 1) (hell : 0 < 2) (a : ℝ)
    (hG : IsUnit (PK 2 k Lu hell a Set.univ).G1inv)
    (hN : IsUnit (GenP.Nmat (PK 2 k Lu hell a Set.univ)))
    (Bt : Bond Lu → SuTwo) (hBt : OnLambdaTildeIn (Set.univ : Set (PeriodicLatticeSite Lu)) 2 Bt) :
    (1 / 1728 : ℝ) * bondEnergy Bt ≤
      GenP.genForm (PK 2 k Lu hell a Set.univ)
        (WithLp.toLp 2 (GenP.genC (PK 2 k Lu hell a Set.univ) Bt)) := by
  set P := PK 2 k Lu hell a Set.univ with hP
  have hN1 : ∀ μ, 1 ≤ Lu μ := fun μ => by have := hL μ; omega
  have hU : P.U = flatCfg := rfl
  have hFS : P.FullSupp := PK_fullSupp 2 k Lu hell a Set.univ
  have hQ1 : P.Q1 = q1SU2 2 := Q1_eq_q1SU2 P hU hd
  have hb : Function.Bijective (H0 (Set.univ : Set (PeriodicLatticeSite Lu)) (q1SU2 2)) := by
    have := IngrBParams.hb_flat P hU hd
    rw [hQ1] at this
    exact this
  have hgen : GenP.genC P Bt = Cop Set.univ (q1SU2 2) Bt := by
    unfold GenP.genC; rw [hQ1]; rfl
  obtain ⟨hax, hker, hen⟩ := Cop_props_univ Lu hd hb Bt hBt
  set Bf := Cop (Set.univ : Set (PeriodicLatticeSite Lu)) (q1SU2 2) Bt with hBf
  have h24 := lemma24_flat hL hd Bf hax hker
  rw [hgen]
  obtain ⟨A, hQA, hform⟩ := Gen.genForm_reduction P hFS (PK_Om0_univ 2 k Lu hell a Set.univ) hU hG hN (WithLp.toLp 2 Bf)
  -- the unit field is the carried level-k average of A
  have hBU : Bf = unitField 2 k Lu hell (lineCoarseRestrictSuTwo (2 ^ k) (WithLp.ofLp (iE P.G A))) := by
    funext e
    have h1 := hQA e
    rw [show P.sector.Qfull (iE P.G A) = (PK 2 k Lu hell a Set.univ).sector.Qfull (iE P.G A) from rfl,
      Qfull_top 2 k Lu hell a Set.univ] at h1
    exact h1.symm
  have hst := stokes_unit 2 k Lu hell hN1 (WithLp.ofLp (iE P.G A))
  rw [← hBU] at hst
  -- curl energy of the fine candidate
  have hcurl := curlnorm_eq (iE P.G A)
  have hcu : ∑ p : PeriodicLatticePlaquette Lu, ‖curlCovariantLM (trivialU Lu) Bf p‖ ^ 2
      = ∑ p : PeriodicLatticePlaquette Lu, ‖flatCurlValue Bf p‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [curlCovariantLM_trivialU_eq_flatCurlLM]; rfl
  have hpow : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hEta : P.eta = (((2 ^ k : ℕ) : ℝ))⁻¹ := by
    unfold IngrBParams.eta; simp [hP, PK, gparams]
  set Eu := ∑ p : PeriodicLatticePlaquette Lu, ‖flatCurlValue Bf p‖ ^ 2 with hEu
  set Ef := ∑ p' : PeriodicLatticePlaquette (scaleUp 2 k Lu), ‖flatCurlValue (WithLp.ofLp (iE P.G A)) p'‖ ^ 2 with hEf
  have hTT := sq_nonneg ‖Tfull P.G P.U (iE P.G A)‖
  have hform' : GenP.genForm P (WithLp.toLp 2 Bf) = P.eta * (Ef + ‖Tfull P.G P.U (iE P.G A)‖ ^ 2) := by
    rw [hform]
    exact congrArg (fun t => P.eta * (t + ‖Tfull P.G P.U (iE P.G A)‖ ^ 2)) hcurl
  have hbond : bondEnergy Bt ≤ ∑ b : Bond Lu, ‖Bf b‖ ^ 2 := hen
  have h24' : (1 / 1728 : ℝ) * ∑ b : Bond Lu, ‖Bf b‖ ^ 2 ≤ Eu := by rw [← hcu]; exact h24
  have hstokes : Eu ≤ P.eta * Ef := by
    have hst' : ((2 ^ k : ℕ) : ℝ) * Eu ≤ Ef := hst
    rw [hEta, ← div_eq_inv_mul, le_div_iff₀ hpow]
    linarith [hst']
  have hge : P.eta * Ef ≤ GenP.genForm P (WithLp.toLp 2 Bf) := by
    rw [hform']
    have : 0 ≤ P.eta := P.eta_pos.le
    nlinarith [mul_nonneg this hTT]
  have hb2 : (1 / 1728 : ℝ) * bondEnergy Bt ≤ (1 / 1728 : ℝ) * ∑ b : Bond Lu, ‖Bf b‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hbond (by norm_num)
  linarith

#print axioms floor_cond

end AdalyFormal.GenuineU1
