import NuM2

/-!
# NuM3 -- `main_neg_two` (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.CoverJacobi
open AdalyFormal.GaugeCov
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.StatementLane (scaleUp Tower)
open AdalyFormal.StatementLaneG
open scoped RealInnerProductSpace
open Filter Topology

section
variable [CfData]
variable {M R : ℕ}

theorem main_neg_two (hdvd : 2 ∣ M) (hM4 : 4 ≤ M) (hR : 1 ≤ R) {a : ℝ} (ha : 0 < a)
    (hinj : ∀ y : FSp (geomOf 2 2 (neS 2 M R)), (Pt 2 M R (by norm_num) (neC0 2 M R) 0 a).data.Qs y = 0 → y = 0)
    (h0 : UnitsFour (Pt 2 M R (by norm_num) (neC0 2 M R) 0 a)) :
    ∃ uE : ℕ, uE % 2 = 0 ∧ neLo M R ≤ uE ∧ uE + 1 < neLo M R + M ∧
      ∃ t : ℝ, |t| < Real.pi / 2 ∧ GenP.WellDefG (Pt 2 M R (by norm_num) (neC0 2 M R) t a) ∧
        GenP.genForm (Pt 2 M R (by norm_num) (neC0 2 M R) t a)
          (WithLp.toLp 2 (GenP.genC (Pt 2 M R (by norm_num) (neC0 2 M R) t a) (Bpatf uE))) < 0 := by
  have hM : 0 < M := by omega
  obtain ⟨cs, hcs1, hcs2, hpsd0, hpos, es, hes, hes0, hqes, i1, p, hp2, hRM, hi1, hlnN, hstN, hp, hBF⟩ :=
    chain_instance hdvd hM4 hR
  have hp2' : p ≤ 2 := by rcases hp2 with rfl | rfl <;> norm_num
  have h2lo : 2 ∣ neLo M R := Dvd.dvd.mul_right hdvd _
  have hpar : (neLo M R + p) % 2 = 0 := by rcases hp2 with rfl | rfl <;> omega
  have hlo : neLo M R ≤ neLo M R + p := by omega
  have hhi : neLo M R + p + 1 < neLo M R + M := by omega
  have hlnE : lnN 2 M R (i1 + p) = 4 := hlnN p (by omega)
  have hlnO : lnN 2 M R (i1 + p + 1) = 4 := hlnN (p + 1) (by omega)
  have hsE : neP0 2 M R + stN 2 M R (i1 + p) = 4 * (neLo M R + p) := hstN p (by omega)
  have hsO : neP0 2 M R + stN 2 M R (i1 + p + 1) = 4 * (neLo M R + p + 1) := by
    have h := hstN (p + 1) (by omega)
    have e : 4 * (neLo M R + (p + 1)) = 4 * (neLo M R + p + 1) := by ring
    rw [e] at h; exact h
  -- geometry of the slab
  have hNu : neLo M R + M ≤ neLu M R 0 + 1 := by
    rw [neLu_succ hM]
    have e : neLo M R = 2 * (R * M) + CfData.cf * M + 2 * M := by unfold neLo; ring
    unfold neNu; omega
  have huE : neLo M R + p + 1 < neLu M R 0 + 1 := by omega
  have h1 : 2 ∣ neLu M R 1 + 1 := by rw [neLu_succ hM]; exact neNu_dvd hdvd
  have h2 : 2 ∣ neLu M R 2 + 1 := by rw [neLu_succ hM]; exact neNu_dvd hdvd
  -- the window of parameters
  have hts : |tOf cs| < Real.pi / 2 := abs_tOf_lt (by linarith)
  obtain ⟨δ, hδ, hpunct⟩ := wellDefG_punctured (le_refl 2) (dvd_refl 2) hdvd hM hR ha h0 hts
  have hcont : ContinuousAt tOf cs := (Real.continuous_arccos.continuousAt).div_const 2
  obtain ⟨η1, hη1, hη1'⟩ := Metric.continuousAt_iff.mp hcont δ hδ
  have hε0 : 0 < min η1 (1 - cs) := lt_min hη1 (by linarith)
  set ε0 := min η1 (1 - cs) with hε0def
  have hwin : ∀ w, cs < w → w < cs + ε0 → |tOf w| < Real.pi / 2 ∧
      GenP.WellDefG (Pt 2 M R (by norm_num) (neC0 2 M R) (tOf w) a) := by
    intro w hw1 hw2
    have hw1' : w ≤ 1 := by have := min_le_right η1 (1 - cs); linarith
    have hne : tOf w ≠ tOf cs := by
      intro h
      have e1 := cos_tOf (by linarith : -1 ≤ w) hw1'
      have e2 := cos_tOf (by linarith : -1 ≤ cs) (by linarith : cs ≤ 1)
      rw [h] at e1; linarith
    have hd : |tOf w - tOf cs| < δ := by
      have := hη1' (x := w) (by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [min_le_left η1 (1 - cs)])
      simpa [Real.dist_eq] using this
    exact hpunct (tOf w) hne hd
  -- the reference point and constants
  have hcref1 : cs < cs + ε0 / 2 := by linarith
  have hcref2 : cs + ε0 / 2 < cs + ε0 := by linarith
  have hcref3 : cs + ε0 ≤ 1 := by have := min_le_right η1 (1 - cs); linarith
  set cref := cs + ε0 / 2 with hcref
  set uE := neLo M R + p with huE_def
  set τs := ContinuousLinearMap.adjoint (tauExt 2 2 (neLu M R) (by norm_num) (neS 2 M R)) with hτs
  set Kp : ℝ := (inner ℝ (τs (Bperp uE)) (Ring.inverse (GenP.Nmat (Pt 2 M R (by norm_num) (neC0 2 M R) (tOf cref) a)) (τs (Bperp uE))) : ℝ) with hKp
  set K0 : ℝ := (inner ℝ (τs (zfield (gbar uE)))
    (diagW (geomOf 2 2 (neS 2 M R)) (massW (geomOf 2 2 (neS 2 M R)) a) (τs (zfield (gbar uE)))) : ℝ) with hK0
  set Bn : ℝ := (inner ℝ (Bpat uE : BondFnL2 (neLu M R)) (Bpat uE) : ℝ) with hBn
  set η0 : ℝ := (Pt 2 M R (by norm_num) (neC0 2 M R) 0 a).eta with hη0def
  have hη0 : 0 < η0 := IngrBParams.eta_pos _
  set T1c : ℝ := c0 * ((((scaleUp 2 2 (neLu M R)) 1 + 1) * ((scaleUp 2 2 (neLu M R)) 2 + 1) : ℕ) : ℝ) with hT1c
  have hT1 : 0 < T1c := by
    have hc0 : 0 < c0 := c0_pos
    have : (0 : ℝ) < ((((scaleUp 2 2 (neLu M R)) 1 + 1) * ((scaleUp 2 2 (neLu M R)) 2 + 1) : ℕ) : ℝ) := by positivity
    exact mul_pos hc0 this
  set M0 : ℝ := (a * Bn / η0 - K0 - Kp - 1) / T1c with hM0
  obtain ⟨τ, ε, hε, htr⟩ := trial_neg (neC0 2 M R - neP0 2 M R) cs es
    (f0pair (nGeo_two (le_refl 2) hdvd hM hR) i1 p hp) hqes hBF M0
  have hε1 : 0 < min ε (ε0 / 2) := lt_min hε (by linarith)
  set ε1 := min ε (ε0 / 2) with hε1def
  have hε1a : ε1 ≤ ε := min_le_left _ _
  have hε1b : ε1 ≤ ε0 / 2 := min_le_right _ _
  set w := cs + ε1 / 2 with hw
  have hw1 : cs < w := by linarith
  have hw2 : w < cref := by linarith
  have hw3 : w < cs + ε := by linarith
  have hwW := hwin w hw1 (by linarith)
  obtain ⟨hwabs, hwWD⟩ := hwW
  obtain ⟨⟨hH, hG1, hN⟩, hguards⟩ := hwWD
  have hcosw : Real.cos (2 * tOf w) = w := cos_tOf (by linarith) (by linarith)
  refine ⟨uE, hpar, hlo, hhi, tOf w, hwabs, ⟨⟨hH, hG1, hN⟩, hguards⟩, ?_⟩
  rw [genForm_pat_eq hdvd hM hR a (tOf w) hwabs uE hpar]
  -- the split
  have hsplit := val_split (le_refl 2) (dvd_refl 2) hdvd hM hR (tOf w) a hwabs hG1 hN uE huE h1 h2
  have hpsd : ∀ e' : Fin (nN 2 M R) → ℝ, e' ∈ Vsub (rowOfN 2 M R) →
      0 ≤ qF1 (neC0 2 M R - neP0 2 M R) (Real.cos (2 * tOf w)) e' := by
    intro e' he'
    rw [hcosw]
    by_cases h : e' = 0
    · rw [h, qF1_vec_zero]
    · exact (hpos w hw1 (by linarith) e' he' h).le
  have hv0 := val0_bound hdvd hM hR (tOf w) a hwabs hG1 hN hpsd hp hlnE hlnO hsE hsO hes τ
  rw [hcosw] at hv0
  -- the orthogonal part is monotone
  have hmono := monotone_perp (ell := 2) (M := M) (R := R) (le_refl 2) (dvd_refl 2) hdvd hM hR ha (lo := w) (hi := cref)
    (by linarith) (by linarith) hinj
    (by
      intro w' hw'
      have := hwin w' (by linarith [hw'.1]) (by linarith [hw'.2])
      exact ⟨this.2.1.2.1, this.2.1.2.2⟩)
    (τs (Bperp uE)) (tauStar_fixed 2 2 (neLu M R) (by norm_num) (neS 2 M R) (Bperp_sig uE))
  have hvP : (inner ℝ (τs (Bperp uE)) (Ring.inverse (GenP.Nmat (Pt 2 M R (by norm_num) (neC0 2 M R) (tOf w) a)) (τs (Bperp uE))) : ℝ) ≤ Kp :=
    hmono ⟨le_refl w, hw2.le⟩ ⟨hw2.le, le_refl cref⟩ hw2.le
  have hq := htr w hw1 hw3
  -- combine
  have hq' : T1c * qF1 (neC0 2 M R - neP0 2 M R) w
      (f0pair (nGeo_two (le_refl 2) hdvd hM hR) i1 p hp + τ • es) < a * Bn / η0 - K0 - Kp - 1 := by
    have := mul_lt_mul_of_pos_left hq hT1
    rw [hM0, mul_div_cancel₀ _ hT1.ne'] at this
    exact this
  have hval : (inner ℝ (τs (Bpat uE)) (Ring.inverse (GenP.Nmat (Pt 2 M R (by norm_num) (neC0 2 M R) (tOf w) a)) (τs (Bpat uE))) : ℝ) <
      a * Bn / η0 - 1 := by
    rw [hsplit]
    linarith
  have hηeq : (Pt 2 M R (by norm_num) (neC0 2 M R) (tOf w) a).eta = η0 := rfl
  rw [hηeq]
  have := mul_lt_mul_of_pos_left hval hη0
  have e : η0 * (a * Bn / η0 - 1) = a * Bn - η0 := by field_simp
  linarith

#print axioms main_neg_two

end

end AdalyFormal.NcwdhTwo
