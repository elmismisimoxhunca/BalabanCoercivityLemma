import SoM2
import NuM3

/-!
# SoM3 -- `main_neg_S`: `genForm (genC B) < 0` for the pattern competitor just above the Z-chain crossing, for general `ell >= 3` at the decoupled layer (lane sites_only_20261019)

Given the flat-point units (`UnitsFour` and injectivity of `Qs` at `t = 0`), there are a slice `uE` inside the slab with `uE % ell + 2 <= ell` and a parameter `t`, `|t| < π/2`, at which
`WellDefG` holds and `genForm (genC B) < 0` for `B = Bpatf ell uE`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

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
open AdalyFormal.NcwdhTwo

section
variable [CfData]
variable {ell M R : ℕ}

theorem main_neg_S {c : ℕ} (hell3 : 3 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hMe2 : ell * ell ≤ M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c)
    {a : ℝ} (ha : 0 < a)
    (hinj : ∀ y : FSp (geomOf ell 2 (neS ell M R)), (Pt ell M R (by omega) (soC ell M R c) 0 a).data.Qs y = 0 → y = 0)
    (h0 : UnitsFour (Pt ell M R (by omega) (soC ell M R c) 0 a)) :
    ∃ uE : ℕ, uE % ell + 2 ≤ ell ∧ neLo M R ≤ uE ∧ uE + 1 < neLo M R + M ∧
      ∃ t : ℝ, |t| < Real.pi / 2 ∧ GenP.WellDefG (Pt ell M R (by omega) (soC ell M R c) t a) ∧
        GenP.genForm (Pt ell M R (by omega) (soC ell M R c) t a)
          (WithLp.toLp 2 (GenP.genC (Pt ell M R (by omega) (soC ell M R c) t a) (Bpatf ell uE))) < 0 := by
  have hell2 : 2 ≤ ell := by omega
  have hM : 0 < M := by nlinarith
  have hCp := cpos_soC hell2 hM hR hrel hc
  obtain ⟨cs, hcs1, hcs2, hpsd0, hpos, es, hes, hes0, hqes, i1, p, hp2, hRM, hi1, hlnN, hstN, hp, hBF⟩ :=
    chain_instance_S hell3 hdvd hM hR hrel hc
  set C := soC ell M R c with hCdef
  have hp2' : p ≤ 2 := by rcases hp2 with rfl | rfl <;> norm_num
  have hlo_dvd : ell ∣ neLo M R := Dvd.dvd.mul_right hdvd _
  have hu0 : u0N M R = neLo M R + 1 := by unfold u0N neLo; ring
  set uE := u0N M R + (ell - 3) + p with huE_def
  have hpar : uE % ell + 2 ≤ ell := by
    obtain ⟨q, hq⟩ := hlo_dvd
    have e : uE = ell * q + (ell - 2 + p) := by rw [huE_def, hu0, hq]; omega
    rw [e, Nat.mul_add_mod]
    rcases hp2 with rfl | rfl
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [show ell - 2 + 2 = ell by omega, Nat.mod_self]; omega
  have hlo : neLo M R ≤ uE := by rw [huE_def, hu0]; omega
  have hhi : uE + 1 < neLo M R + M := by
    have : ell * ell ≥ 3 * ell := Nat.mul_le_mul_right ell hell3
    rw [huE_def, hu0]; omega
  have hlnE : lnN ell M R (i1 + p) = ell ^ 2 := hlnN p (by omega)
  have hlnO : lnN ell M R (i1 + p + 1) = ell ^ 2 := hlnN (p + 1) (by omega)
  have hsE : neP0 ell M R + stN ell M R (i1 + p) = ell ^ 2 * uE := hstN p (by omega)
  have hsO : neP0 ell M R + stN ell M R (i1 + p + 1) = ell ^ 2 * (uE + 1) := by
    have h := hstN (p + 1) (by omega)
    have e : ell ^ 2 * (u0N M R + (ell - 3) + (p + 1)) = ell ^ 2 * (uE + 1) := by rw [huE_def]; ring
    rw [e] at h; exact h
  -- geometry of the slab
  have hNu : neLo M R + M ≤ neLu M R 0 + 1 := by
    rw [neLu_succ hM]
    have e : neLo M R = 2 * (R * M) + CfData.cf * M + 2 * M := by unfold neLo; ring
    unfold neNu; omega
  have huE : uE + 1 < neLu M R 0 + 1 := by omega
  have h1 : ell ∣ neLu M R 1 + 1 := by rw [neLu_succ hM]; exact neNu_dvd hdvd
  have h2 : ell ∣ neLu M R 2 + 1 := by rw [neLu_succ hM]; exact neNu_dvd hdvd
  -- the window of parameters
  have hts : |tOf cs| < Real.pi / 2 := abs_tOf_lt (by linarith)
  obtain ⟨δ, hδ, hpunct⟩ := wellDefG_punctured hCp hell2 hE hdvd hM hR ha h0 hts
  have hcont : ContinuousAt tOf cs := (Real.continuous_arccos.continuousAt).div_const 2
  obtain ⟨η1, hη1, hη1'⟩ := Metric.continuousAt_iff.mp hcont δ hδ
  have hε0 : 0 < min η1 (1 - cs) := lt_min hη1 (by linarith)
  set ε0 := min η1 (1 - cs) with hε0def
  have hwin : ∀ w, cs < w → w < cs + ε0 → |tOf w| < Real.pi / 2 ∧
      GenP.WellDefG (Pt ell M R (by omega) C (tOf w) a) := by
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
  set τs := ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) with hτs
  set Kp : ℝ := (inner ℝ (τs (Bperp ell uE)) (Ring.inverse (GenP.Nmat (Pt ell M R (by omega) C (tOf cref) a)) (τs (Bperp ell uE))) : ℝ) with hKp
  set K0 : ℝ := (inner ℝ (τs (zfield (gbar ell uE)))
    (diagW (geomOf ell 2 (neS ell M R)) (massW (geomOf ell 2 (neS ell M R)) a) (τs (zfield (gbar ell uE)))) : ℝ) with hK0
  set Bn : ℝ := (inner ℝ (Bpat ell uE : BondFnL2 (neLu M R)) (Bpat ell uE) : ℝ) with hBn
  set η0 : ℝ := (Pt ell M R (by omega) C 0 a).eta with hη0def
  have hη0 : 0 < η0 := IngrBParams.eta_pos _
  set T1c : ℝ := c0 * ((((scaleUp ell 2 (neLu M R)) 1 + 1) * ((scaleUp ell 2 (neLu M R)) 2 + 1) : ℕ) : ℝ) with hT1c
  have hT1 : 0 < T1c := by
    have hc0 : 0 < c0 := c0_pos
    have : (0 : ℝ) < ((((scaleUp ell 2 (neLu M R)) 1 + 1) * ((scaleUp ell 2 (neLu M R)) 2 + 1) : ℕ) : ℝ) := by positivity
    exact mul_pos hc0 this
  set M0 : ℝ := (a * Bn / η0 - K0 - Kp - 1) / T1c with hM0
  obtain ⟨τ, ε, hε, htr⟩ := trial_neg (C - neP0 ell M R) cs es
    (f0pair (nGeo_two hell2 hdvd hM hR) i1 p hp) hqes hBF M0
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
  rw [genForm_pat_eq hCp hell2 hE hdvd hM hR a (tOf w) hwabs uE hpar]
  -- the split
  have hsplit := val_split hCp hell2 hE hdvd hM hR (tOf w) a hwabs hG1 hN uE huE h1 h2
  have hpsd : ∀ e' : Fin (nN ell M R) → ℝ, e' ∈ Vsub (rowOfN ell M R) →
      0 ≤ qF1 (C - neP0 ell M R) (Real.cos (2 * tOf w)) e' := by
    intro e' he'
    rw [hcosw]
    by_cases h : e' = 0
    · rw [h, qF1_vec_zero]
    · exact (hpos w hw1 (by linarith) e' he' h).le
  have hv0 := val0_bound hCp hell2 hE hdvd hM hR (tOf w) a hwabs hG1 hN hpsd hp hlnE hlnO hsE hsO hes τ
  rw [hcosw] at hv0
  -- the orthogonal part is monotone
  have hmono := monotone_perp hCp hell2 hE hdvd hM hR ha (lo := w) (hi := cref)
    (by linarith) (by linarith) hinj
    (by
      intro w' hw'
      have := hwin w' (by linarith [hw'.1]) (by linarith [hw'.2])
      exact ⟨this.2.1.2.1, this.2.1.2.2⟩)
    (τs (Bperp ell uE)) (tauStar_fixed ell 2 (neLu M R) (by omega) (neS ell M R) (Bperp_sig ell uE))
  have hvP : (inner ℝ (τs (Bperp ell uE)) (Ring.inverse (GenP.Nmat (Pt ell M R (by omega) C (tOf w) a)) (τs (Bperp ell uE))) : ℝ) ≤ Kp :=
    hmono ⟨le_refl w, hw2.le⟩ ⟨hw2.le, le_refl cref⟩ hw2.le
  have hq := htr w hw1 hw3
  -- combine
  have hq' : T1c * qF1 (C - neP0 ell M R) w
      (f0pair (nGeo_two hell2 hdvd hM hR) i1 p hp + τ • es) < a * Bn / η0 - K0 - Kp - 1 := by
    have := mul_lt_mul_of_pos_left hq hT1
    rw [hM0, mul_div_cancel₀ _ hT1.ne'] at this
    exact this
  have hval : (inner ℝ (τs (Bpat ell uE)) (Ring.inverse (GenP.Nmat (Pt ell M R (by omega) C (tOf w) a)) (τs (Bpat ell uE))) : ℝ) <
      a * Bn / η0 - 1 := by
    rw [hsplit]
    linarith
  have hηeq : (Pt ell M R (by omega) C (tOf w) a).eta = η0 := rfl
  rw [hηeq]
  have := mul_lt_mul_of_pos_left hval hη0
  have e : η0 * (a * Bn / η0 - 1) = a * Bn - η0 := by field_simp
  linarith

#print axioms main_neg_S

end

end AdalyFormal.SitesOnly
