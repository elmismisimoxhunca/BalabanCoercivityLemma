import MA7

/-!
# MA8 -- `chart_core` (lane m1_assembly_20261014)

The M1 inequality `gam1 * ||Bt||^2 <= genForm(C Bt)` at ONE configuration `V`, from the abstract inputs:
W4 (`hcoer`), the stratified D-layer (`hD2`, `hJ`), the sandwich data (`HatPack`, `HolRegime`), the top-row drift (`hδ`), the top-stratum link bound (`hα`),
the unit-level `C`-perturbation (`hcop`) and well-definedness (`hWD`).  No `B0` / gauge-projected field is used.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.M1Assembly

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp OnLambdaTildeIn TorusOK)
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneG (gparams pe tauAdj_apply pe_injective LambdaOK2 GenP.genForm GenP.firstTerm GenP.genC GenP.WellDef GenP.Nmat)
open AdalyFormal.GenuineU1 (bondsE unitField)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.IngredientFamily (q1SU2)
open AdalyFormal.M1IMS (HatPack HolRegime Fform Ymass sigG)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy curlDrift)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.StatementLaneR6 (plaqMask)
open AdalyFormal.FlatEllGeneral (InBox)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

open Classical in
/-- squared norm of a masked plaquette function. -/
theorem plaqMask_sq {L : PeriodicLatticeExtent} (P : Set (PeriodicLatticePlaquette L))
    (f : Balaban.CovariantHjMinimizer.PlaqFnL2 L) :
    ‖plaqMask P f‖ ^ 2 = ∑ p, (if p ∈ P then ‖f p‖ ^ 2 else 0) := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [AdalyFormal.StatementLaneR6.plaqMask_apply]
  by_cases hp : p ∈ P <;> simp [hp]


open Classical in
theorem chart_core {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (hell2 : 2 ≤ ell)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hRM3 : 3 ≤ R * M)
    (hT : TorusOK ell M Lu) {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK2 ell M R k S Lam)
    (V : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a)
    (hWD : GenP.WellDef (gparams ell k Lu hell0 S V a Lam))
    (cw ε2s εJ : ℝ) (hcw : 0 < cw) (hε2 : 0 ≤ ε2s) (hεJ : 0 ≤ εJ) (hε2cw : ε2s ≤ cw)
    (hcoer : ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S V a Lam).G),
      cw * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
        ≤ ⟪A, (gparams ell k Lu hell0 S V a Lam).data.Ginv A⟫)
    (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu hell0 S V a Lam).G),
      |⟪A, (gparams ell k Lu hell0 S V a Lam).data.Delta2 (gparams ell k Lu hell0 S V a Lam).data_laws A⟫|
        ≤ ε2s * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)))
    (hJ : ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      |⟪(gparams ell k Lu hell0 S V a Lam).H1in ((gparams ell k Lu hell0 S V a Lam).D2in
          (WithLp.toLp 2 (Cop Lam (gparams ell k Lu hell0 S V a Lam).Q1 Bt))), (gparams ell k Lu hell0 S V a Lam).Jf⟫|
        ≤ εJ * ‖(WithLp.toLp 2 (Cop Lam (gparams ell k Lu hell0 S V a Lam).Q1 Bt) : BondFnL2 Lu)‖ ^ 2)
    {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell) (hR1 : 1 ≤ R) (hM1 : 1 ≤ M)
    (cs ρ ε1 : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) V a cs) (hρ : 0 ≤ ρ)
    (hreg : HolRegime S ell k V ρ) (hε1 : 0 < ε1) (hε1' : ε1 < 1)
    (hTT : (1 + 1 / ε1) * (12 * ρ ^ 2 * (ell : ℝ) ^ 8 * (4 * ell / cs) ^ 2)
        + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) *
          ((ell : ℝ) * (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)
            * (4 / cs))) ^ 2 ≤ 1)
    (δs : ℝ)
    (hδ : ∀ x : BondFnL2 (scaleUp ell k Lu), ∑ p, AdalyFormal.W6.wF p *
        ‖(WithLp.ofLp ((bondSectorOf (geomOf ell k S) V).Qfull x)) p
          - (WithLp.ofLp ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x)) p‖ ^ 2 ≤ 3 * δs ^ 2 * ‖x‖ ^ 2)
    (s : ℝ) (hs : 0 ≤ s)
    (hα : ∀ e : Bond (scaleUp ell k Lu), e.1 ∈ S.Om k → periodicLatticeShift e.1 e.2 ∈ S.Om k →
      frobNorm ((V e : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ s / (ell : ℝ) ^ k)
    (dC cB : ℝ) (hdC : 0 ≤ dC) (hcB : 0 ≤ cB)
    (hcop : ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      ∑ b, ‖Cop Lam (gparams ell k Lu hell0 S V a Lam).Q1 Bt b - Cop Lam (q1SU2 ell) Bt b‖ ^ 2
          ≤ dC ^ 2 * ∑ b, ‖Cop Lam (gparams ell k Lu hell0 S V a Lam).Q1 Bt b‖ ^ 2 ∧
      ∑ b, ‖Cop Lam (gparams ell k Lu hell0 S V a Lam).Q1 Bt b‖ ^ 2 ≤ cB ^ 2 * bondEnergy Bt)
    (Et : ℝ) (hEt : (8 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) / (1 - ε1) + 4 * (32 * s ^ 2)
        + 128 * (3 * δs ^ 2)) / cw ≤ Et) :
    ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      gam1 (1 / 54 * (1 / (ell : ℝ) ^ 5)) a (ε2s / cw) εJ ε1 Et dC cB * bondEnergy Bt
        ≤ GenP.genForm (gparams ell k Lu hell0 S V a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S V a Lam) Bt)) := by
  intro Bt hBt hBT
  set P := gparams ell k Lu hell0 S V a Lam with hP
  have hd : ∀ μ, ell ∣ Lu μ + 1 := hT.1
  have hstrict : ∀ μ, ell < Lu μ + 1 := hT.2.1
  have hu1 : ∀ μ, 1 ≤ Lu μ := fun μ => by have := hstrict μ; omega
  have hMR : 1 ≤ R * M := by omega
  obtain ⟨-, hG, hN⟩ := hWD
  set B : Bond Lu → SuTwo := Cop Lam P.Q1 Bt with hB
  set Bv : BondFnL2 Lu := WithLp.toLp 2 B with hBv
  have hgenC : GenP.genC P Bt = B := rfl
  rw [hgenC]
  obtain ⟨A, hQA, hin⟩ := AdalyFormal.GenuineU1.Gen.firstTerm_core P hG hN (ContinuousLinearMap.adjoint P.tau Bv)
  set y : BondFnL2 (scaleUp ell k Lu) := (A : BondFnL2 (scaleUp ell k Lu)) with hy
  set n : ℝ := (ell : ℝ) ^ k with hn
  have hnpos : 0 < n := by positivity
  set xx : ℝ := AdalyFormal.M1.wnormSq S ell k y with hxx
  set β : ℝ := ‖Bv‖ with hβ
  set bt : ℝ := Real.sqrt (bondEnergy Bt) with hbt
  have hbt0 : 0 ≤ bondEnergy Bt := Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have hbt2 : bt ^ 2 = bondEnergy Bt := Real.sq_sqrt hbt0
  set G : ℝ := ⟪A, P.data.Ginv A⟫ with hGdef
  have hEq : P.G1inv = P.data.Ginv - P.data.Delta2 P.data_laws :=
    P.data.G1inv_unique P.G1inv_spec (P.data.isG1inv_sub P.data_laws)
  have hG1A : ⟪A, P.G1inv A⟫ = G - ⟪A, P.data.Delta2 P.data_laws A⟫ := by
    rw [hEq, sub_apply, inner_sub_right]
  have h1 : cw * xx ≤ G := hcoer A
  have hxxG : xx ≤ G / cw := by rw [le_div_iff₀ hcw]; linarith
  have hD2A : ⟪A, P.data.Delta2 P.data_laws A⟫ ≤ ε2s * xx := le_trans (le_abs_self _) (hD2 A)
  have hlow : (1 - ε2s / cw) * G ≤ ⟪A, P.G1inv A⟫ := by
    rw [hG1A]
    have : ε2s * xx ≤ ε2s * (G / cw) := mul_le_mul_of_nonneg_left hxxG hε2
    have e : ε2s * (G / cw) = ε2s / cw * G := by ring
    nlinarith
  have hJ' := hJ Bt hBt hBT
  have hη : P.eta = n⁻¹ := rfl
  have hBB : ⟪Bv, Bv⟫ = β ^ 2 := real_inner_self_eq_norm_sq Bv
  -- the lower bound for genForm in the variable X = G - a n beta^2
  set X : ℝ := G - a * n * β ^ 2 with hX
  have h10 : (1 - ε2s / cw) * (X / n) - (ε2s / cw * a + 2 * εJ) * β ^ 2
      ≤ GenP.genForm P Bv := by
    unfold GenP.genForm GenP.firstTerm
    rw [hin, hη, hBB]
    have hcw1 : 0 ≤ 1 - ε2s / cw := by
      have : ε2s / cw ≤ 1 := by rw [div_le_one hcw]; exact hε2cw
      linarith
    have hm := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hnpos.le)
    have e1 : n⁻¹ * ((1 - ε2s / cw) * G) = (1 - ε2s / cw) * (X / n) + (1 - ε2s / cw) * a * β ^ 2 := by
      rw [hX]; field_simp; ring
    have hJle : ⟪P.H1in (P.D2in Bv), P.Jf⟫ ≤ εJ * β ^ 2 := le_trans (le_abs_self _) hJ'
    have hPa : P.a = a := rfl
    rw [hPa]
    nlinarith
  -- ===== the sandwich =====
  have hu : IsUnit (AdalyFormal.M1Site.LP (geomOf ell k S) V a) := hp.hu
  have hGF : G = Fform S ell k V a y := ginv_eq_Fform hell0 S V a Lam ha.le hu A
  have hMM : ⟪A, P.data.Mass A⟫ = ‖Ymass (geomOf ell k S) V a y‖ ^ 2 := mass_eq_Ymass hell0 S V a Lam ha.le A
  have hsupp : ∀ e : Bond Lu, unitBondEmb ell k Lu hell0 e ∉ bondsLam (geomOf ell k S) k → (WithLp.ofLp Bv) e = 0 :=
    fun e he => Cop_frakB hell0 hd hu1 hMR hS hL.1 P.Q1 Bt hBT e he
  have hMge : a * n * β ^ 2 ≤ ⟪A, P.data.Mass A⟫ :=
    AdalyFormal.FlatEllGeneral.mass_ge_gen P ha.le A Bv hQA hsupp
  have hfl := AdalyFormal.M1IMS.fform_lower hS hell2 hR1 hM1 hW hWR V a cs hp ρ hρ hreg ε1 hε1 hTT y
  have hNle : ‖(AdalyFormal.DLayer.bondWt (-AdalyFormal.M1IMS.sigG (geomOf ell k S))) y‖ ^ 2 ≤ xx :=
    AdalyFormal.M1IMS.N_le_wnorm hS hell0 y
  set ν : ℝ := (17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4) with hν
  have hν0 : 0 ≤ ν := by positivity
  set Ffine : Finset (PeriodicLatticePlaquette (scaleUp ell k Lu)) :=
    Finset.univ.filter (fun p => p ∈ plaqIn (S.Om k)) with hFfine
  set Xbox : ℝ := ∑ p ∈ Ffine, ‖curlValueCovariant V (WithLp.ofLp y) p‖ ^ 2 with hXbox
  have hXbox_le : Xbox ≤ ‖plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 V y)‖ ^ 2 := by
    rw [plaqMask_sq]
    have hsub : ∀ p ∈ Ffine, p ∈ plaqIn (S.Om 0) := by
      intro p hpF e he
      have hpk := (Finset.mem_filter.mp hpF).2 e he
      exact ⟨AdalyFormal.FlatEllGeneral.om_k_sub_om0 S hS.1 k hpk.1, AdalyFormal.FlatEllGeneral.om_k_sub_om0 S hS.1 k hpk.2⟩
    calc Xbox = ∑ p ∈ Ffine, (if p ∈ plaqIn (S.Om 0) then ‖(curlCovariantLM_L2 V y) p‖ ^ 2 else 0) := by
          refine Finset.sum_congr rfl (fun p hpF => ?_)
          rw [if_pos (hsub p hpF)]; rfl
      _ ≤ ∑ p, (if p ∈ plaqIn (S.Om 0) then ‖(curlCovariantLM_L2 V y) p‖ ^ 2 else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => by split_ifs <;> positivity)
  have h2 : (1 - ε1) * Xbox ≤ X + 2 * ν * xx := by
    have hmul := mul_le_mul_of_nonneg_left hXbox_le (by linarith : (0 : ℝ) ≤ 1 - ε1)
    have hF : Fform S ell k V a y = G := hGF.symm
    have hnu : 2 * ν * ‖(AdalyFormal.DLayer.bondWt (-AdalyFormal.M1IMS.sigG (geomOf ell k S))) y‖ ^ 2 ≤ 2 * ν * xx :=
      mul_le_mul_of_nonneg_left hNle (by positivity)
    rw [hF] at hfl
    have hMM' : a * n * β ^ 2 ≤ ‖Ymass (geomOf ell k S) V a y‖ ^ 2 := by rw [← hMM]; exact hMge
    rw [hX]
    nlinarith
  -- ===== curl drift on the good boxes =====
  set R' : Finset (Bond (scaleUp ell k Lu)) :=
    Finset.univ.filter (fun b => b.1 ∈ S.Om k ∧ periodicLatticeShift b.1 b.2 ∈ S.Om k) with hR'
  set c12 : ℝ := ∑ p ∈ Ffine, ‖flatCurlValue (WithLp.ofLp y) p‖ ^ 2 with hc12
  have hbd : ∀ p ∈ Ffine, (p.1, p.2.1.1) ∈ R' ∧ (p.1, p.2.1.2) ∈ R' ∧
      (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∈ R' ∧ (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∈ R' := by
    intro p hpF
    have hpk := (Finset.mem_filter.mp hpF).2
    have hm : ∀ e ∈ periodicPlaquetteBoundaryEdges p, e ∈ R' := fun e he =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpk e he⟩
    refine ⟨hm _ ?_, hm _ ?_, hm _ ?_, hm _ ?_⟩ <;>
      simp [periodicPlaquetteBoundaryEdges]
  have hnn : (0 : ℝ) ≤ s / n := by positivity
  have hRU : ∀ b ∈ R', frobNorm ((V b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ s / n := by
    intro b hb
    have := (Finset.mem_filter.mp hb).2
    exact hα b this.1 this.2
  have hdr := curlDrift_good V (WithLp.ofLp y) (s / n) hnn Ffine R' hRU hbd
  have hRy : ∑ b ∈ R', ‖(WithLp.ofLp y) b‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => sq_nonneg _)
  have hy2 : ‖y‖ ^ 2 ≤ n ^ 2 * xx := normSq_le_wnorm (k := k) hell0 S y
  have hflat := flat_sum_le V (WithLp.ofLp y) Ffine
  have h3 : c12 ≤ 2 * Xbox + 2 * (32 * s ^ 2) * xx := by
    have e1 : 32 * (s / n) ^ 2 * (n ^ 2 * xx) = 32 * s ^ 2 * xx := by field_simp
    have hxx0 : 0 ≤ xx := Finset.sum_nonneg (fun b _ => by positivity)
    have e2 : 32 * (s / n) ^ 2 * ∑ b ∈ R', ‖(WithLp.ofLp y) b‖ ^ 2 ≤ 32 * s ^ 2 * xx := by
      calc 32 * (s / n) ^ 2 * ∑ b ∈ R', ‖(WithLp.ofLp y) b‖ ^ 2 ≤ 32 * (s / n) ^ 2 * (n ^ 2 * xx) :=
            mul_le_mul_of_nonneg_left (hRy.trans hy2) (by positivity)
        _ = 32 * s ^ 2 * xx := e1
    rw [hc12]
    nlinarith
  -- ===== Stokes and the flat floor =====
  set Bf : Bond Lu → SuTwo := unitField ell k Lu hell0 (lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp y)) with hBf
  set Qg : Finset (PeriodicLatticePlaquette Lu) := Finset.univ.filter
    (fun q => ∀ c, InBox q.1 c → embY ell k Lu hell0 c ∈ S.Om k) with hQg
  set E : Finset (Bond Lu) := Finset.univ.filter (fun b => embY ell k Lu hell0 b.1 ∈ S.Om k) with hE
  set Kq : ℝ := ∑ q ∈ Qg, ‖flatCurlValue Bf q‖ ^ 2 with hKq
  have h4 : n * Kq ≤ c12 := by
    have := AdalyFormal.FlatEllGeneral.local_unit_stokes_good hell0 hu1 hS (WithLp.ofLp y)
    have hcast : (((ell ^ k : ℕ)) : ℝ) = n := by rw [hn]; push_cast; rfl
    rw [hcast] at this
    exact this
  have hb1 : Function.Bijective (H0 Lam (q1SU2 ell)) := by
    have h := IngrBParams.hb_flat (gparams ell k Lu hell0 S flatCfg a Lam) rfl hd
    rw [AdalyFormal.StatementLaneG.Q1_eq_q1SU2 (gparams ell k Lu hell0 S flatCfg a Lam) rfl hd] at h
    exact h
  have hfloor := flat_floor_good hell2 hstrict hd hL.2 hb1 Bt hBt hBT hRM3 hL.1 Bf
  set dd : ℝ := ∑ b ∈ E, ‖Bf b - Cop Lam (q1SU2 ell) Bt b‖ ^ 2 with hdd
  have h5 : (1 / 54 * (1 / (ell : ℝ) ^ 5)) * bt ^ 2 ≤ 2 * Kq + 64 * dd := by
    rw [hbt2]; exact hfloor
  -- ===== the bond defect =====
  have hbE : ∀ b ∈ E, unitBondEmb ell k Lu hell0 b ∈ bondsLam (geomOf ell k S) k := fun b hb =>
    AdalyFormal.FlatEllGeneral.emb_bondsLam hell0 hS b (Finset.mem_filter.mp hb).2
  have hQy : (bondSectorOf (geomOf ell k S) V).Qfull y = ContinuousLinearMap.adjoint (gparams ell k Lu hell0 S V a Lam).tau Bv := hQA
  have hrows := rows_drift hell0 S V a Lam y Bv hQy E hbE
  have hy3 := hδ y
  have hdrift : ∑ b ∈ E, ‖lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp y) (bondsE ell k Lu hell0 b) - (WithLp.ofLp Bv) b‖ ^ 2
      ≤ (3 * δs ^ 2 / n) * xx := by
    have h1' : n ^ 3 * ∑ b ∈ E, ‖lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp y) (bondsE ell k Lu hell0 b) - (WithLp.ofLp Bv) b‖ ^ 2
        ≤ 3 * δs ^ 2 * (n ^ 2 * xx) := by
      calc _ ≤ _ := hrows
        _ ≤ 3 * δs ^ 2 * ‖y‖ ^ 2 := hy3
        _ ≤ 3 * δs ^ 2 * (n ^ 2 * xx) := mul_le_mul_of_nonneg_left hy2 (by positivity)
    have hn3 : 0 < n ^ 3 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hnpos]
    have : (∑ b ∈ E, ‖lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp y) (bondsE ell k Lu hell0 b) - (WithLp.ofLp Bv) b‖ ^ 2) * n
        * n ^ 2 ≤ 3 * δs ^ 2 * xx * n ^ 2 := by nlinarith
    have hn2 : 0 < n ^ 2 := by positivity
    exact le_of_mul_le_mul_right this hn2
  have hcop' := hcop Bt hBt hBT
  have hBsq : β ^ 2 = ∑ b : Bond Lu, ‖Cop Lam P.Q1 Bt b‖ ^ 2 := by
    rw [hβ, hBv, PiLp.norm_sq_eq_of_L2]
  have h7 : dd ≤ 2 * dC ^ 2 * β ^ 2 + 2 * (3 * δs ^ 2 / n) * xx := by
    have hpt : ∀ b ∈ E, ‖Bf b - Cop Lam (q1SU2 ell) Bt b‖ ^ 2 ≤
        2 * ‖Bf b - B b‖ ^ 2 + 2 * ‖Cop Lam (q1SU2 ell) Bt b - B b‖ ^ 2 := by
      intro b _
      have e : Bf b - Cop Lam (q1SU2 ell) Bt b = (Bf b - B b) - (Cop Lam (q1SU2 ell) Bt b - B b) := by abel
      rw [e]; exact AdalyFormal.M0Finish.sq_sub_le2 _ _
    have hs1 : dd ≤ 2 * ∑ b ∈ E, ‖Bf b - B b‖ ^ 2 + 2 * ∑ b ∈ E, ‖Cop Lam (q1SU2 ell) Bt b - B b‖ ^ 2 := by
      rw [hdd, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hpt
    have hs2 : ∑ b ∈ E, ‖Bf b - B b‖ ^ 2 ≤ (3 * δs ^ 2 / n) * xx := by
      have : ∀ b ∈ E, ‖Bf b - B b‖ ^ 2 = ‖lineCoarseRestrictSuTwo (ell ^ k) (WithLp.ofLp y) (bondsE ell k Lu hell0 b) - (WithLp.ofLp Bv) b‖ ^ 2 :=
        fun b _ => rfl
      rw [Finset.sum_congr rfl this]; exact hdrift
    have hs3 : ∑ b ∈ E, ‖Cop Lam (q1SU2 ell) Bt b - B b‖ ^ 2 ≤ dC ^ 2 * β ^ 2 := by
      have hall : ∑ b ∈ E, ‖Cop Lam (q1SU2 ell) Bt b - B b‖ ^ 2 ≤ ∑ b : Bond Lu, ‖Cop Lam (q1SU2 ell) Bt b - B b‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => sq_nonneg _)
      have hsw : ∑ b : Bond Lu, ‖Cop Lam (q1SU2 ell) Bt b - B b‖ ^ 2 = ∑ b : Bond Lu, ‖B b - Cop Lam (q1SU2 ell) Bt b‖ ^ 2 :=
        Finset.sum_congr rfl (fun b _ => by rw [norm_sub_rev])
      rw [hBsq]
      exact hall.trans (hsw.le.trans hcop'.1)
    nlinarith
  have h9 : β ≤ cB * bt := by
    have : β ^ 2 ≤ (cB * bt) ^ 2 := by
      rw [mul_pow, hbt2, hBsq]; exact hcop'.2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp this
  have hxx0 : 0 ≤ xx := Finset.sum_nonneg (fun b _ => by positivity)
  have h1' : cw * xx ≤ X + a * n * β ^ 2 := by rw [hX]; linarith
  have key := assemble_real n (1 / 54 * (1 / (ell : ℝ) ^ 5)) a (ε2s / cw) εJ cw ν (32 * s ^ 2) (3 * δs ^ 2) dC cB ε1 Et
    X xx β bt Kq Xbox c12 dd (GenP.genForm P Bv) hnpos hcw hε1 hε1' ha.le hν0 (by positivity) (by positivity) hxx0
    (norm_nonneg _) (Real.sqrt_nonneg _) hcB (by positivity)
    (by rw [div_le_one hcw]; exact hε2cw) hεJ hEt h1' h2 h3 h4 h5 h7 h9 h10
  rw [hbt2] at key
  exact key

end AdalyFormal.M1Assembly

#print axioms AdalyFormal.M1Assembly.plaqMask_sq
#print axioms AdalyFormal.M1Assembly.chart_core
