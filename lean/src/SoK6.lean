import SoK5
import SoG4
import SoZ1
import NuK6

/-!
# SoK6 -- `Q₁` and `C̃⁽²⁾` of the pattern at the trivial unit background; `genC (pattern) = pattern`, for general `ell` and legal layer position `C` (lane sites_only_20261019)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.NcwdhTwo

section
variable [CfData]
variable {ell M R : ℕ}
variable {C : ℕ} (hCp : CPos ell M R C)
include hCp

/-- the unit-level background along the direction-0 staggered family is a Cartan configuration with trivial loops, regular. -/
theorem Pt_unit_cartan (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ)
    (ht : |t| < Real.pi / 2) :
    ∃ θ : PeriodicLatticeEdge (neLu M R) → ℝ, (Pt ell M R (by omega) C t a).unitBgU = cartanOf θ ∧
      (∀ cc : PeriodicLatticeEdge (neLu M R), ∀ x ∈ stepBlockOf cc.1 1 ell, |loopAngG 1 ell θ cc.1 cc.2 x| < Real.pi) ∧
      RegBg2 1 ell (Pt ell M R (by omega) C t a).unitBgU := by
  have hell : 0 < ell := by omega
  have S := nested_z0Setup_S hCp hell2 hE hdvd hM hR t ht
  have hxs2 : C + ell ≤ scaleUp ell 2 (neLu M R) 0 + 1 := by
    have := S.z.hc2; nlinarith [Nat.le_mul_self ell]
  have hNN : ell ≤ scaleUp ell 2 (neLu M R) 0 + 1 := by
    have := S.z.hc2; nlinarith [Nat.le_mul_self ell]
  have hT := unit_temporal_stag0 (Lu := neLu M R) hell hE t ht S.z.hc1 hxs2 hNN
  obtain ⟨av, hav⟩ : ∃ av, IsTemporal 1 (Pt ell M R hell C t a).unitBgU av := ⟨_, hT⟩
  refine ⟨phiT av, cartanOf_phiT hav, ?_, ?_⟩
  · intro cc x hx
    rw [loopAngG_phiT 1 ell av cc.1 cc.2 x hx, abs_zero]; exact Real.pi_pos
  · exact stag0_unit_regBg2 (Lu := neLu M R) hell hE t ht S.z.hc1 hxs2 hNN

/-- `Q₁` of the pattern competitor vanishes. -/
theorem Pt_Q1_pat (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ)
    (ht : |t| < Real.pi / 2) (uE : ℕ) (huE : uE % ell + 2 ≤ ell) :
    (Pt ell M R (by omega) C t a).Q1 (Bpatf ell uE) = 0 := by
  obtain ⟨θ, hθ, hφ, hreg⟩ := Pt_unit_cartan hCp hell2 hE hdvd hM hR a t ht
  have hNu : ∀ ν : Fin 3, ell ∣ neLu M R ν + 1 := by
    intro ν; rw [neLu_succ hM ν]
    exact neNu_dvd hdvd
  funext c
  have hy : ∀ ν : Fin 3, (c.1.1 ν).val % ell = 0 := AdalyFormal.Balaban.AdmissibleSubspace.mem_CoarseLattice.mp c.1.2
  show Q1jet ell (Pt ell M R (by omega) C t a).unitBgU (Bpatf ell uE) c = 0
  rw [Q1jet_sig (by omega) hθ hφ hreg (Bpatf ell uE) (Bpatf_sig ell uE) c]
  rw [Rsig_pat_zero ell uE hell2 huE hNu c.1.1 hy c.2, dgS_zero, smul_zero]

theorem Pt_genC_pat (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ)
    (ht : |t| < Real.pi / 2) (uE : ℕ) (huE : uE % ell + 2 ≤ ell) :
    GenP.genC (Pt ell M R (by omega) C t a) (Bpatf ell uE) = Bpatf ell uE := by
  have h0 := Pt_Q1_pat hCp hell2 hE hdvd hM hR a t ht uE huE
  show Cop (neLam M R) (Pt ell M R (by omega) C t a).Q1 (Bpatf ell uE) = Bpatf ell uE
  unfold Cop hLift
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
  rw [h0]
  simp

theorem Pt_D2in_pat (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ)
    (ht : |t| < Real.pi / 2) (uE : ℕ) :
    (Pt ell M R (by omega) C t a).D2in (Bpat ell uE) = 0 := by
  obtain ⟨θ, hθ, hφ, hreg⟩ := Pt_unit_cartan hCp hell2 hE hdvd hM hR a t ht
  have hC : C2tilde ell (Pt ell M R (by omega) C t a).unitBgU (Bpatf ell uE) = 0 := by
    funext c
    exact C2tilde_sig hθ hφ hreg (Bpatf ell uE) (Bpatf_sig ell uE) c
  unfold IngrBParams.D2in
  show WithLp.toLp 2 (((ell : ℝ)⁻¹) • hLift (neLam M R) (Pt ell M R (by omega) C t a).Q1
    (C2tilde ell (Pt ell M R (by omega) C t a).unitBgU (Bpatf ell uE))) = 0
  rw [hC]
  simp

end

#print axioms Pt_genC_pat
#print axioms Pt_D2in_pat

end AdalyFormal.SitesOnly
