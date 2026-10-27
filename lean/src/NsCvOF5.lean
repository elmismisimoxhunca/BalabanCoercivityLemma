import NsCvOF4

/-!
# CvOF5 -- the unit level of the nested family: `genC (zfun g) = zfun g`, `D2in (zfield g) = 0`, `tau*` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)

variable {ell M R : ℕ}


theorem neNu_dvd {M R k : ℕ} (hk : k ∣ M) : k ∣ neNu M R := by
  simp only [neNu]
  exact Nat.dvd_add (Nat.dvd_add (Dvd.dvd.mul_left (Dvd.dvd.mul_left hk R) 4)
    (Dvd.dvd.mul_left (Dvd.dvd.mul_left hk CfData.cf) 2)) (Dvd.dvd.mul_left hk 6)

theorem unit_hdiv (hdvd : ell ∣ M) (hM : 0 < M) (μ : Fin 3) : ell ∣ neLu M R μ + 1 := by
  rw [neLu_succ hM μ]
  exact neNu_dvd hdvd

/-- the odd-block geometry of the nested instance. -/
theorem nested_oddGeo (hell3 : 3 ≤ ell) (hO : ell % 2 = 1) (h5 : 5 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) :
    OddGeo (scaleUp ell 2 (neLu M R)) ell (neC ell M R) := by
  have S := nested_stagSetup hell3 (Or.inr ⟨hO, h5⟩) hdvd hM hR
  have hbig : ell * ell + ell < scaleUp ell 2 (neLu M R) 1 + 1 := by
    rcases S.hE with h | ⟨-, -, h⟩
    · omega
    · exact h
  refine ⟨S.hN, hO, h5, S.hdiv, hbig, S.hc1, le_mul_self_c S.hc2, S.hc2, ?_⟩
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨R * (ell * m) + ell * m + CfData.cf * m, ?_⟩
  subst hm
  unfold neC neA'
  ring

/-- the unit-level background of the nested staggered family is a Cartan configuration with sub-`π` unit loops, and regular. -/
theorem Pn_unit_cartan (hell3 : 3 ≤ ell) (hE : StagOK ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (htπ : |t| < tcap ell) :
    ∃ θ : PeriodicLatticeEdge (neLu M R) → ℝ, (Pn ell M R (by omega) a t).unitBgU = cartanOf θ ∧
      (∀ cc : PeriodicLatticeEdge (neLu M R), ∀ x ∈ stepBlockOf cc.1 1 ell, |loopAngG 1 ell θ cc.1 cc.2 x| < Real.pi) ∧
      RegBg2 1 ell (Pn ell M R (by omega) a t).unitBgU := by
  have hell : 0 < ell := by omega
  have S := nested_stagSetup hell3 hE hdvd hM hR
  rcases hE with hE | ⟨hO, h5⟩
  · have htπ' : |t| < Real.pi := abs_lt_pi_of_tcap htπ
    have hT := unit_temporal (Lu := neLu M R) hell hE (neC ell M R) t htπ' S.hc1 (le_mul_self_c S.hc2)
    obtain ⟨av, hav⟩ : ∃ av, IsTemporal 1 (Pn ell M R (by omega) a t).unitBgU av := ⟨_, hT⟩
    refine ⟨phiT av, cartanOf_phiT hav, ?_, ?_⟩
    · intro cc x hx
      rw [loopAngG_phiT 1 ell av cc.1 cc.2 x hx, abs_zero]; exact Real.pi_pos
    · exact stag_unit_regBg2 (Lu := neLu M R) hell hE (neC ell M R) t htπ' S.hc1 (le_mul_self_c S.hc2)
  · have G := nested_oddGeo hell3 hO h5 hdvd hM hR
    rw [tcap_odd hO] at htπ
    obtain ⟨cu, hcu⟩ := G.hcd
    refine ⟨unitFld t (b2 ell) (d2 ell) cu, ?_, ?_, ?_⟩
    · show unitBg ell 2 (neLu M R) hell (UbarTower su2LogExp ell (stagCfg (neC ell M R) t : PeriodicLinkConfiguration SU2 (scaleUp ell 2 (neLu M R))) 2) = _
      rw [unitBg_eq_cartan hell G t htπ, phiu_eq_unitFld hell G cu hcu t]
    · intro cc x hx
      refine lt_of_le_of_lt (unitFld_loop_le (two_dvd_unit hO G.hN) hO cu t (b2 ell) (d2 ell) (b2_range h5) (d2_range h5) cc x hx) ?_
      exact lt_trans htπ pi_gt_8_5
    · exact unit_regBg2_odd hell G cu hcu t htπ

theorem Pn_Q1_zero (hell3 : 3 ≤ ell) (hE : StagOK ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (htπ : |t| < tcap ell)
    (g : ℕ → ℝ) (hblk : ∀ q : ℕ, ∑ n ∈ Finset.range ell, g (ell * q + n) = 0) :
    (Pn ell M R (by omega) a t).Q1 (zfun g) = 0 := by
  have hell : 0 < ell := by omega
  obtain ⟨θ, hθ, hφ, hreg⟩ := Pn_unit_cartan hell3 hE hdvd hM hR a t htπ
  funext c
  exact Q1jet_zfield_zero hell (unit_hdiv hdvd hM) hθ hφ hreg g hblk c

theorem Pn_genC (hell3 : 3 ≤ ell) (hE : StagOK ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (htπ : |t| < tcap ell)
    (g : ℕ → ℝ) (hblk : ∀ q : ℕ, ∑ n ∈ Finset.range ell, g (ell * q + n) = 0) :
    GenP.genC (Pn ell M R (by omega) a t) (zfun g) = zfun g := by
  have h0 := Pn_Q1_zero hell3 hE hdvd hM hR a t htπ g hblk
  show Cop (neLam M R) (Pn ell M R (by omega) a t).Q1 (zfun g) = zfun g
  unfold Cop hLift
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
  rw [h0]
  simp

theorem Pn_D2in (hell3 : 3 ≤ ell) (hE : StagOK ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (htπ : |t| < tcap ell)
    (g : ℕ → ℝ) : (Pn ell M R (by omega) a t).D2in (zfield g) = 0 := by
  have hell : 0 < ell := by omega
  obtain ⟨θ, hθ, hφ, hreg⟩ := Pn_unit_cartan hell3 hE hdvd hM hR a t htπ
  have hC : C2tilde ell (Pn ell M R (by omega) a t).unitBgU (zfun g) = 0 := by
    funext c
    exact C2tilde_zfield_zero hθ hφ hreg g c
  unfold IngrBParams.D2in
  show WithLp.toLp 2 (((ell : ℝ)⁻¹) • hLift (neLam M R) (Pn ell M R (by omega) a t).Q1 (C2tilde ell (Pn ell M R (by omega) a t).unitBgU (zfun g))) = 0
  rw [hC]
  simp

#print axioms Pn_genC
#print axioms Pn_D2in

end AdalyFormal.CoverOmega
