import CvOF4

/-!
# CvOF5 -- the unit level of the nested family: `genC (zfun g) = zfun g`, `D2in (zfield g) = 0`, `tau*` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

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
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)

variable {ell M R : ℕ}

theorem unit_hdiv (hdvd : ell ∣ M) (hM : 0 < M) (μ : Fin 3) : ell ∣ neLu M R μ + 1 := by
  rw [neLu_succ hM μ]
  exact Dvd.dvd.mul_right hdvd _

/-- the unit-level background of the nested staggered family is temporal and regular. -/
theorem Pn_unit_temporal (hell3 : 3 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (htπ : |t| < Real.pi) :
    (∃ av : ℕ → ℝ, IsTemporal 1 (Pn ell M R (by omega) a t).unitBgU av) ∧ RegBg2 1 ell (Pn ell M R (by omega) a t).unitBgU := by
  have hell : 0 < ell := by omega
  have S := nested_stagSetup hell3 hE hdvd hM hR
  refine ⟨?_, ?_⟩
  · exact ⟨_, unit_temporal (Lu := neLu M R) hell hE (neC ell M R) t htπ S.hc1 S.hc2⟩
  · exact stag_unit_regBg2 (Lu := neLu M R) hell hE (neC ell M R) t htπ S.hc1 S.hc2

theorem Pn_Q1_zero (hell3 : 3 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (htπ : |t| < Real.pi)
    (g : ℕ → ℝ) (hblk : ∀ q : ℕ, ∑ n ∈ Finset.range ell, g (ell * q + n) = 0) :
    (Pn ell M R (by omega) a t).Q1 (zfun g) = 0 := by
  have hell : 0 < ell := by omega
  obtain ⟨⟨av, hav⟩, hreg⟩ := Pn_unit_temporal hell3 hE hdvd hM hR a t htπ
  funext c
  exact Q1jet_zfield_zero hell (unit_hdiv hdvd hM) hav hreg g hblk c

theorem Pn_genC (hell3 : 3 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (htπ : |t| < Real.pi)
    (g : ℕ → ℝ) (hblk : ∀ q : ℕ, ∑ n ∈ Finset.range ell, g (ell * q + n) = 0) :
    GenP.genC (Pn ell M R (by omega) a t) (zfun g) = zfun g := by
  have h0 := Pn_Q1_zero hell3 hE hdvd hM hR a t htπ g hblk
  show Cop (neLam M R) (Pn ell M R (by omega) a t).Q1 (zfun g) = zfun g
  unfold Cop hLift
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
  rw [h0]
  simp

theorem Pn_D2in (hell3 : 3 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (htπ : |t| < Real.pi)
    (g : ℕ → ℝ) : (Pn ell M R (by omega) a t).D2in (zfield g) = 0 := by
  have hell : 0 < ell := by omega
  obtain ⟨⟨av, hav⟩, hreg⟩ := Pn_unit_temporal hell3 hE hdvd hM hR a t htπ
  have hC : C2tilde ell (Pn ell M R (by omega) a t).unitBgU (zfun g) = 0 := by
    funext c
    exact C2tilde_zfield_zero hav hreg g c
  unfold IngrBParams.D2in
  show WithLp.toLp 2 (((ell : ℝ)⁻¹) • hLift (neLam M R) (Pn ell M R (by omega) a t).Q1 (C2tilde ell (Pn ell M R (by omega) a t).unitBgU (zfun g))) = 0
  rw [hC]
  simp

#print axioms Pn_genC
#print axioms Pn_D2in

end AdalyFormal.CoverOmega
