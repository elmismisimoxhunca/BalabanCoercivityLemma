import NP7
import WN12

/-!
# NP8 -- local W3 on the two-stratum patch at a NON-FLAT configuration in the link/plaquette regime
(m1_patch_nonflat, 2026-10-14)

Torus `scaleUp ell (j+1) Lu`, patch `GP ell j Lu Rg = geomOf ell (j+1) (patchTower j Rg)`, `n = ell^{j+1}`.  A configuration
`V` with `dv (V b) ≤ e` (links), `dv (pw 1 V) ≤ q0` (plaquettes), the WN7/WN10 smallness conditions on
`r = kapHat ell (rhoM0 ell (j+1) e q0)`, and FIRST-difference bound `frobNorm(V(x,μ) − V(x−e_μ,μ)) ≤ θ/n²`, `e ≤ θ/n`:
* `decay_chart` : the hypotheses of NP5 `harmDecay_nf` are discharged (tower class from WN6 `towerClass_patch`, row drift
  `dsum ≤ 6 r ≤ 1/2`, Poincaré from PW3 `poincare_patch` with `Pk = 2 Mc a`);
* **`w3loc_chart`** : for every `A` supported on bonds touching `Ball w s`, every `d ≥ 12 ell + 10`:
  `(1/(ell² KG0 a Ci) − epsNF ell (2 Mc a) θ d) · wnormSq ≤ locG0(V, K = Ball w (s + d ell^j))(A)`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1NonFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.StatementLane (BlockClosed scaleUp)
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.SiteCoercivity (ProperTower)
open AdalyFormal.M1Patch (patchTower GP patch_proper om0_univ dvd_scaleUp LemIFlat Kflat Pc)
open AdalyFormal.BondComposite (TowerClass dsum)
open AdalyFormal.CurvBlock (dv pw)
open AdalyFormal.RegBgKU (KUSmall kapHat kap Kc Kc_pos)
open AdalyFormal.AsmM0 (rhoM0 Mc)
open AdalyFormal.W3NF (towerClass_patch kap_nonneg' kap_le_class hU_patch hT_patch dsum_le_class lamC ThetaP KG0
  KG0_pos g0_patch_nonflat Pc_sq Mc_pos bstrat_patch_ge)
open AdalyFormal.M1IMS (G0form)
open AdalyFormal.M1W2 (HK gradOn locG0)

/-- the Poincaré factor used on the patch. -/
noncomputable def PkA (a : ℝ) : ℝ := 2 * Mc a

theorem PkA_ge_one (a : ℝ) : 1 ≤ PkA a := by
  unfold PkA Mc; have := le_max_left (6 : ℝ) (16 / (3 * a)); linarith

theorem dv_eq_frob (g : SU2) : dv g = frobNorm (((g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1) := rfl

section chart
variable {ell : ℕ} (hell : 2 ≤ ell) (j : ℕ) (Lu : PeriodicLatticeExtent)
  (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu))) (hRg : BlockClosed (ell ^ (j + 1)) Rg)
  (V : Cfg (scaleUp ell (j + 1) Lu)) (e q0 θ : ℝ) (he0 : 0 ≤ e) (hq0 : 0 ≤ q0) (hθ : 0 ≤ θ)
  (hlinks : ∀ b, dv (V b) ≤ e) (h0 : ∀ y ν μ, dv (pw 1 V y ν μ) ≤ q0)
  (hlinkθ : e ≤ θ / (ell : ℝ) ^ (j + 1))
  (hdiff : ∀ (x : PeriodicLatticeSite (scaleUp ell (j + 1) Lu)) (μ : Fin 3),
    frobNorm (((V (x, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
      - ((V (periodicLatticeShiftBack x μ, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) ≤ θ / ((ell : ℝ) ^ (j + 1)) ^ 2)
  (H : KUSmall ell (rhoM0 ell (j + 1) e q0))
  (hs1 : 432 * kapHat ell (rhoM0 ell (j + 1) e q0) ^ 2 ≤ 1)
  (hs2 : kapHat ell (rhoM0 ell (j + 1) e q0) ≤ 1 / (1000 * (ell : ℝ) ^ 3))
include hell hRg he0 hq0 hθ hlinks h0 hlinkθ hdiff H hs1 hs2

theorem decay_chart (a : ℝ) (ha : 0 < a) (d : ℕ) (hd : 12 * ell + 10 ≤ d) (w : PeriodicLatticeSite (scaleUp ell (j + 1) Lu))
    (s : ℕ) (h : SiteL2 (scaleUp ell (j + 1) Lu))
    (hh : h ∈ HK (geomOf ell (j + 1) (patchTower j Rg)) V (Ball w (s + d * ell ^ j))) :
    gradOn V (Ball w s) h ≤ epsNF ell (PkA a) θ d * (((ell : ℝ) ^ (j + 1))⁻¹) ^ 2 * ‖h‖ ^ 2 := by
  have hell0 : 0 < ell := by omega
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hl1 : (1 : ℝ) ≤ ell := by linarith
  have hlpos : (0 : ℝ) < ell := by linarith
  have hpi := Real.pi_pos
  have hKc := Kc_pos ell hell
  set n : ℝ := (ell : ℝ) ^ (j + 1) with hn
  have hnpos : 0 < n := by positivity
  set ρ := rhoM0 ell (j + 1) e q0 with hρ
  set r := kapHat ell ρ with hr
  have hρ_eq : ρ = n * e + 3 * Real.pi * (n ^ 2 * q0) := by
    rw [hρ]; unfold rhoM0; rw [← hn]; ring
  have hρ0 : 0 ≤ ρ := by rw [hρ_eq]; positivity
  have hρr : ρ ≤ r := by
    rw [hr]; unfold kapHat
    have : 0 ≤ Kc ell * (ρ / (3 * Real.pi) + ρ ^ 2) := by positivity
    linarith
  have hr0 : 0 ≤ r := hρ0.trans hρr
  have hen : e ≤ r / n := by
    rw [le_div_iff₀ hnpos]
    have : 0 ≤ 3 * Real.pi * (n ^ 2 * q0) := by positivity
    nlinarith
  have hlinksr : ∀ b, dv (V b) ≤ r / n := fun b => (hlinks b).trans hen
  have hrn0 : 0 ≤ r / n := by positivity
  obtain ⟨S, -⟩ := AdalyFormal.RegBgKU.towerSmall_of_KU ell (j + 1) hell e q0 he0 hq0 H
  have hcl := towerClass_patch ell j hell Lu V e q0 he0 hq0 hlinks h0 S
  have hε0 : ∀ i, 0 ≤ kap ell e q0 i := fun i => kap_nonneg' ell hell e q0 he0 hq0 i
  have hkapk : kap ell e q0 (j + 1) ≤ r := AdalyFormal.M0Finish.kap_le_kapHat ell (j + 1) hell e q0 he0 hq0
  have hεη : ∀ i, i < j + 1 → kap ell e q0 i ≤ (ell : ℝ) ^ i * (r / n) := by
    intro i hi
    refine (kap_le_class ell hell e q0 he0 hq0 (j + 1) i hi.le).trans ?_
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hkapk hnpos.le) (by positivity)
  -- geometry, site layer, Poincaré
  have hdvd := dvd_scaleUp ell j Lu hell0
  have hP : ProperTower (GP ell j Lu Rg) ell (j + 1) := patch_proper hell0 hRg
  have hOm : (GP ell j Lu Rg).Om0 = Set.univ := om0_univ j Rg ell
  have hr1000 : r ≤ 1 / 1000 := by
    have : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ hl1
    have h2 : 1 / (1000 * (ell : ℝ) ^ 3) ≤ 1 / 1000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have h216 : 216 * r ^ 2 < 1 := by nlinarith
  have hU := hU_patch ell j hell0 (GP ell j Lu Rg) V r hr0 hlinksr
  have hT := hT_patch ell j hell0 Lu Rg V (fun i => kap ell e q0 i) r hr0 hcl hεη
  have hPoinc : ∀ ν ∈ NQp (geomOf ell (j + 1) (patchTower j Rg)) V,
      ‖ν‖ ^ 2 ≤ PkA a * ((ell : ℝ) * ((ell ^ j : ℕ) : ℝ)) ^ 2 * ‖gradL2 V ν‖ ^ 2 := by
    intro ν hν
    have h1 := AdalyFormal.M1Patch.poincare_patch hell hdvd hP hOm V a ha r hr0 h216 hU hT ν hν
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, Pc_sq ell (j + 1) a r h216] at h2
    have hM := Mc_pos a
    have hden : (1 : ℝ) / 2 ≤ 1 - 216 * r ^ 2 := by nlinarith
    have e1 : ((ell : ℝ) * ((ell ^ j : ℕ) : ℝ)) ^ 2 = ((ell : ℝ) ^ (j + 1)) ^ 2 := by push_cast; ring
    rw [e1]
    refine h2.trans ?_
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    unfold PkA
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ ((ell : ℝ) ^ (j + 1)) ^ 2 * Mc a := by positivity
    nlinarith
  -- row drift
  have hbg : ∀ i, i < j + 1 → ∀ y ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice
      (scaleUp ell (j + 1) Lu) (ell ^ i), ∀ μ : Fin 3,
      frobNorm (((bgTower (geomOf ell (j + 1) (patchTower j Rg)) V i (y, μ) : _) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ kap ell e q0 i := fun i hi y hy μ => hcl i hi y hy μ
  have hdsum : ∀ m, m ≤ j + 1 → dsum ell (fun i => kap ell e q0 i) m ≤ 6 * r := by
    intro m hm
    have h1 := dsum_le_class ell hell (fun i => kap ell e q0 i) hε0 (r / n) hrn0 (j + 1) hεη m hm
    have h2 : (ell : ℝ) ^ (j + 1) * (r / n) = r := by rw [← hn]; field_simp
    rw [h2] at h1
    exact (le_abs_self _).trans h1
  have hD12 : 6 * r ≤ 1 / 2 := by linarith
  -- θ bounds
  have hU1 : ∀ b, frobNorm (((V b : SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ θ / (ell : ℝ) ^ (j + 1) :=
    fun b => (hlinks b).trans hlinkθ
  exact harmDecay_nf hell j hRg hdvd V θ hθ hU1 hdiff (fun i => kap ell e q0 i) (6 * r) hD12 hbg hdsum
    (PkA a) (PkA_ge_one a) hPoinc d hd w s h hh

theorem w3loc_chart {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci) (hI : LemIFlat ell a Ci)
    (hs3 : kapHat ell (rhoM0 ell (j + 1) e q0) ≤ 1)
    (hs4 : 324 * lamC ell * kapHat ell (rhoM0 ell (j + 1) e q0) ≤ 1)
    (hs5 : 2 * ThetaP ell a (kapHat ell (rhoM0 ell (j + 1) e q0)) ≤ 1 / Kflat a Ci)
    (hs6 : 8 * (272 * (kapHat ell (rhoM0 ell (j + 1) e q0) / (3 * Real.pi)) / (4 * Real.sqrt 2)) ≤ 1 / Kflat a Ci)
    (d : ℕ) (hd : 12 * ell + 10 ≤ d) (w : PeriodicLatticeSite (scaleUp ell (j + 1) Lu)) (s : ℕ)
    (A : BondFnL2 (scaleUp ell (j + 1) Lu))
    (hA : ∀ b : Bond (scaleUp ell (j + 1) Lu), (WithLp.ofLp A) b ≠ 0 →
      b.1 ∈ Ball w s ∨ periodicLatticeShift b.1 b.2 ∈ Ball w s) :
    (1 / ((ell : ℝ) ^ 2 * KG0 a Ci) - epsNF ell (PkA a) θ d) * AdalyFormal.M1.wnormSq (patchTower j Rg) ell (j + 1) A
      ≤ locG0 (patchTower j Rg) ell (j + 1) V a (Ball w (s + d * ell ^ j)) A := by
  have hell0 : 0 < ell := by omega
  have hlpos : (0 : ℝ) < ell := by exact_mod_cast hell0
  have hKG := KG0_pos ha hCi
  have hg0 := g0_patch_nonflat hell ha hCi hI j Lu Rg hRg V e q0 he0 hq0 hlinks h0 H hs1 hs2 hs3 hs4 hs5 hs6 A
  have hw : AdalyFormal.M1.wnormSq (patchTower j Rg) ell (j + 1) A ≤ (ell : ℝ) ^ 2 * (((ell : ℝ) ^ (j + 1)) ^ 2)⁻¹ * ‖A‖ ^ 2 := by
    unfold AdalyFormal.M1.wnormSq
    rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    refine Finset.sum_le_sum (fun b _ => ?_)
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hb : j ≤ AdalyFormal.M1.bstrat (patchTower j Rg) (j + 1) b := bstrat_patch_ge Rg b
    have h1 : (ell : ℝ) ^ j ≤ (ell : ℝ) ^ AdalyFormal.M1.bstrat (patchTower j Rg) (j + 1) b :=
      pow_le_pow_right₀ (by exact_mod_cast hell0) hb
    have h2 : (((ell : ℝ) ^ AdalyFormal.M1.bstrat (patchTower j Rg) (j + 1) b)⁻¹) ^ 2 ≤ (((ell : ℝ) ^ j)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) h1) 2
    refine h2.trans (le_of_eq ?_)
    field_simp; ring
  have hcW : 1 / ((ell : ℝ) ^ 2 * KG0 a Ci) * AdalyFormal.M1.wnormSq (patchTower j Rg) ell (j + 1) A
      ≤ G0form (patchTower j Rg) ell (j + 1) V a A := by
    have hG0nn : 0 ≤ G0form (patchTower j Rg) ell (j + 1) V a A := by
      unfold G0form; positivity
    have h1 : ‖A‖ ^ 2 ≤ ((ell : ℝ) ^ (j + 1)) ^ 2 * KG0 a Ci * G0form (patchTower j Rg) ell (j + 1) V a A := hg0
    calc 1 / ((ell : ℝ) ^ 2 * KG0 a Ci) * AdalyFormal.M1.wnormSq (patchTower j Rg) ell (j + 1) A
        ≤ 1 / ((ell : ℝ) ^ 2 * KG0 a Ci) * ((ell : ℝ) ^ 2 * (((ell : ℝ) ^ (j + 1)) ^ 2)⁻¹ * ‖A‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ ≤ 1 / ((ell : ℝ) ^ 2 * KG0 a Ci) * ((ell : ℝ) ^ 2 * (((ell : ℝ) ^ (j + 1)) ^ 2)⁻¹ *
            (((ell : ℝ) ^ (j + 1)) ^ 2 * KG0 a Ci * G0form (patchTower j Rg) ell (j + 1) V a A)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = G0form (patchTower j Rg) ell (j + 1) V a A := by field_simp
  have hεnn := epsNF_nonneg ell (by omega) (PkA_ge_one a) hθ d
  exact w3loc_lev ell hell0 V j Rg a _ _ hεnn d w s
    (fun h hh => decay_chart hell j Lu Rg hRg V e q0 θ he0 hq0 hθ hlinks h0 hlinkθ hdiff H hs1 hs2 a ha d hd w s h hh)
    A hA hcW

end chart

end AdalyFormal.M1NonFlat

#print axioms AdalyFormal.M1NonFlat.decay_chart
#print axioms AdalyFormal.M1NonFlat.w3loc_chart
