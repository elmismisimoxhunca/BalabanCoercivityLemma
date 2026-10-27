import SK1

/-!
# SK2 -- `chart_core_class`: the M1 sandwich/assembly at `V = U` (no gauge), with the unit floor as a hypothesis (lane m2_skeleton_20261015)

Head of the proof = MA8 `chart_core` up to the sandwich step `h2` (all of it is stated for an arbitrary configuration `V`).  The M1 unit chain
(Stokes, flat floor, drift, `C`-perturbation, `h3`-`h9`) is replaced by the hypothesis `hfloor` (the shape of `UD7.unit_floor_class`).
The real arithmetic is MA2 `assemble_real` instantiated with `bt := ‖B‖`, `cB := 1`, `dC := 0`, `dd := 0`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.M2Skel

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
open AdalyFormal.M1Assembly (gam1 assemble_real plaqMask_sq ginv_eq_Fform mass_eq_Ymass Cop_frakB)

open Classical in
theorem chart_core_class {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (hell2 : 2 ≤ ell)
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
    (cUc c1 c2 : ℝ) (hcU : 0 < cUc) (hc1 : 0 < c1) (hc2 : 0 ≤ c2)
    (hfloor : ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      ∀ y : BondFnL2 (scaleUp ell k Lu),
      (bondSectorOf (geomOf ell k S) V).Qfull y = ContinuousLinearMap.adjoint (gparams ell k Lu hell0 S V a Lam).tau
        (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S V a Lam) Bt)) →
      (cUc * ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu hell0 S V a Lam) Bt b‖ ^ 2
        ≤ c1 / (ell : ℝ) ^ k *
            ∑ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette (scaleUp ell k Lu))).filter
                (fun p => p ∈ plaqIn (S.Om k)), ‖curlValueCovariant V (WithLp.ofLp y) p‖ ^ 2
          + c2 / (ell : ℝ) ^ k * AdalyFormal.M1.wnormSq S ell k y)
      ∧ bondEnergy Bt ≤ ∑ b : Bond Lu, ‖GenP.genC (gparams ell k Lu hell0 S V a Lam) Bt b‖ ^ 2)
    (Et : ℝ) (hEt : (8 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) / (1 - ε1) + 4 * (c2 / c1)) / cw ≤ Et)
    (hg0 : 0 ≤ gam1 (4 * cUc / c1) a (ε2s / cw) εJ ε1 Et 0 1) :
    ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      gam1 (4 * cUc / c1) a (ε2s / cw) εJ ε1 Et 0 1 * bondEnergy Bt
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
  -- ===== the unit floor =====
  have hxx0 : 0 ≤ xx := Finset.sum_nonneg (fun b _ => by positivity)
  have hBsq : β ^ 2 = ∑ b : Bond Lu, ‖Cop Lam P.Q1 Bt b‖ ^ 2 := by
    rw [hβ, hBv, PiLp.norm_sq_eq_of_L2]
  obtain ⟨hf1, hf2⟩ := hfloor Bt hBt hBT y hQA
  have hf1' : cUc * β ^ 2 ≤ c1 / n * Xbox + c2 / n * xx := by
    rw [hBsq]; exact hf1
  have hf2' : bondEnergy Bt ≤ β ^ 2 := by rw [hBsq]; exact hf2
  have hfl : n * (4 * cUc / c1) / 4 * β ^ 2 ≤ Xbox + (c2 / c1) * xx := by
    have h := mul_le_mul_of_nonneg_left hf1' hnpos.le
    have e1 : n * (c1 / n * Xbox + c2 / n * xx) = c1 * Xbox + c2 * xx := by field_simp
    rw [e1] at h
    have e2 : n * (4 * cUc / c1) / 4 * β ^ 2 = (n * (cUc * β ^ 2)) / c1 := by field_simp
    rw [e2, div_le_iff₀ hc1]
    have e3 : (Xbox + c2 / c1 * xx) * c1 = c1 * Xbox + c2 * xx := by field_simp
    rw [e3]; exact h
  have hΓ0 : 0 ≤ 4 * cUc / c1 := by positivity
  have h1' : cw * xx ≤ X + a * n * β ^ 2 := by rw [hX]; linarith
  have hδ : 0 ≤ c2 / c1 := div_nonneg hc2 hc1.le
  have key := assemble_real n (4 * cUc / c1) a (ε2s / cw) εJ cw ν (c2 / c1) 0 0 1 ε1 Et
    X xx β β ((4 * cUc / c1) * β ^ 2 / 2) Xbox (n * ((4 * cUc / c1) * β ^ 2 / 2)) 0 (GenP.genForm P Bv)
    hnpos hcw hε1 hε1' ha.le hν0 hδ le_rfl hxx0 (norm_nonneg _) (norm_nonneg _) zero_le_one
    (div_nonneg hε2 hcw.le) (by rw [div_le_one hcw]; exact hε2cw) hεJ (by simpa using hEt) h1' h2
    (by nlinarith) le_rfl (by ring_nf; exact le_rfl) (by simp) (by simp) h10
  have hmono : gam1 (4 * cUc / c1) a (ε2s / cw) εJ ε1 Et 0 1 * bondEnergy Bt
      ≤ gam1 (4 * cUc / c1) a (ε2s / cw) εJ ε1 Et 0 1 * β ^ 2 := mul_le_mul_of_nonneg_left hf2' hg0
  exact hmono.trans key

end AdalyFormal.M2Skel

#print axioms AdalyFormal.M2Skel.chart_core_class
