import NuK5
import NuG4
import NtCvON4

/-!
# NuK6 -- `Q₁` and `C̃⁽²⁾` of a sigma_3 unit field at the trivial unit background; `genC (pattern) = pattern` (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

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

section
variable [CfData]
variable {L : PeriodicLatticeExtent}

theorem suCoordF_sig (Bf : Bond L → SuTwo) (hB : SigB Bf) : suCoordF Bf = aF (thetaOf Bf) := by
  funext b
  have hb : Bf b = dgS (thetaOf Bf b) := by
    have := sig_apply_eq (WithLp.toLp 2 Bf : BondFnL2 L) hB b
    simpa using this
  show fromM2 ((Bf b : SuTwo) : M2) = _
  rw [hb, dgS_coe, fromM2_dg]
  rfl

/-- `Q₁` of a sigma_3 unit field: the abelian block average. -/
theorem Q1jet_sig {ell : ℕ} (hell : 0 < ell) {V0 : PeriodicLinkConfiguration SU2 L} {θ : PeriodicLatticeEdge L → ℝ}
    (hV : V0 = cartanOf θ) (hφ : ∀ cc : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf cc.1 1 ell, |loopAngG 1 ell θ cc.1 cc.2 x| < Real.pi)
    (hreg : RegBg2 1 ell V0) (Bf : Bond L → SuTwo) (hB : SigB Bf) (c : CoarseBond L ell) :
    Q1jet ell V0 Bf c = ((ell : ℝ)⁻¹) • dgS (Rsig 1 ell (thetaOf Bf) (c.1.1, c.2)) := by
  have hV' := hV
  have hreg' : RegBg2 1 ell (cartanOf θ : PeriodicLinkConfiguration SU2 L) := by rw [← hV']; exact hreg
  have hQ : QlinStepL 1 ell V0 (aF (thetaOf Bf)) = aF (Rsig 1 ell (thetaOf Bf)) := by
    rw [QlinStepL_eq_of_reg2 1 ell V0 hreg, hV']
    exact QlinStepX_sigma3 1 ell θ hφ hreg' (thetaOf Bf)
  show ((ell : ℝ)⁻¹) • (suCoordFInv (QlinStepL 1 ell V0 (suCoordF Bf))) (c.1.1, c.2) = _
  rw [suCoordF_sig Bf hB, hQ, suCoordFInv_aF]

theorem C2tilde_sig {ell : ℕ} {V0 : PeriodicLinkConfiguration SU2 L} {θ : PeriodicLatticeEdge L → ℝ}
    (hV : V0 = cartanOf θ) (hφ : ∀ cc : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf cc.1 1 ell, |loopAngG 1 ell θ cc.1 cc.2 x| < Real.pi)
    (hreg : RegBg2 1 ell V0) (Bf : Bond L → SuTwo) (hB : SigB Bf) (c : CoarseBond L ell) :
    C2tilde ell V0 Bf c = 0 := by
  have hV' := hV
  have hreg' : RegBg2 1 ell (cartanOf θ : PeriodicLinkConfiguration SU2 L) := by rw [← hV']; exact hreg
  have hC : C2StepL 1 ell V0 (aF (thetaOf Bf)) = 0 := by
    rw [C2StepL_eq_C2StepX2 1 ell V0 hreg, hV']
    exact C2StepX_sigma3 1 ell θ hφ hreg' (thetaOf Bf)
  show (suCoordFInv (C2StepL 1 ell V0 (suCoordF Bf))) (c.1.1, c.2) = 0
  rw [suCoordF_sig Bf hB, hC]
  have : (suCoordFInv (0 : XS L)) = (0 : Bond L → SuTwo) := by
    funext b; apply Subtype.ext
    show toM2 ((0 : XS L) b) = ((0 : Bond L → SuTwo) b : SuTwo)
    rw [show (0 : XS L) b = 0 from rfl, map_zero]; rfl
  rw [this]; rfl

end

section
variable [CfData]
variable {ell M R : ℕ}

/-- the unit-level background along the direction-0 staggered family is a Cartan configuration with trivial loops, regular. -/
theorem Pt_unit_cartan (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ)
    (ht : |t| < Real.pi / 2) :
    ∃ θ : PeriodicLatticeEdge (neLu M R) → ℝ, (Pt ell M R (by omega) (neC0 ell M R) t a).unitBgU = cartanOf θ ∧
      (∀ cc : PeriodicLatticeEdge (neLu M R), ∀ x ∈ stepBlockOf cc.1 1 ell, |loopAngG 1 ell θ cc.1 cc.2 x| < Real.pi) ∧
      RegBg2 1 ell (Pt ell M R (by omega) (neC0 ell M R) t a).unitBgU := by
  have hell : 0 < ell := by omega
  have S := nested_z0Setup hell2 hE hdvd hM hR t ht
  have hxs2 : neC0 ell M R + ell ≤ scaleUp ell 2 (neLu M R) 0 + 1 := by
    have := S.z.hc2; nlinarith [Nat.le_mul_self ell]
  have hNN : ell ≤ scaleUp ell 2 (neLu M R) 0 + 1 := by
    have := S.z.hc2; nlinarith [Nat.le_mul_self ell]
  have hT := unit_temporal_stag0 (Lu := neLu M R) hell hE t ht S.z.hc1 hxs2 hNN
  obtain ⟨av, hav⟩ : ∃ av, IsTemporal 1 (Pt ell M R hell (neC0 ell M R) t a).unitBgU av := ⟨_, hT⟩
  refine ⟨phiT av, cartanOf_phiT hav, ?_, ?_⟩
  · intro cc x hx
    rw [loopAngG_phiT 1 ell av cc.1 cc.2 x hx, abs_zero]; exact Real.pi_pos
  · exact stag0_unit_regBg2 (Lu := neLu M R) hell hE t ht S.z.hc1 hxs2 hNN

/-- `Q₁` of the pattern competitor vanishes. -/
theorem Pt_Q1_pat (hell2 : 2 = ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ)
    (ht : |t| < Real.pi / 2) (uE : ℕ) (huE : uE % 2 = 0) :
    (Pt ell M R (by omega) (neC0 ell M R) t a).Q1 (Bpatf uE) = 0 := by
  subst hell2
  obtain ⟨θ, hθ, hφ, hreg⟩ := Pt_unit_cartan (le_refl 2) hE hdvd hM hR a t ht
  have hNu : ∀ ν : Fin 3, 2 ∣ neLu M R ν + 1 := by
    intro ν; rw [neLu_succ hM ν]
    exact ⟨M * (2 * R + CfData.cf + 3), by unfold neNu; ring⟩
  funext c
  have hy : ∀ ν : Fin 3, (c.1.1 ν).val % 2 = 0 := AdalyFormal.Balaban.AdmissibleSubspace.mem_CoarseLattice.mp c.1.2
  show Q1jet 2 (Pt 2 M R (by omega) (neC0 2 M R) t a).unitBgU (Bpatf uE) c = 0
  rw [Q1jet_sig (by norm_num) hθ hφ hreg (Bpatf uE) (Bpatf_sig uE) c]
  rw [Rsig_pat_zero uE huE hNu c.1.1 hy c.2, dgS_zero, smul_zero]


theorem Pt_genC_pat (hell2 : 2 = ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ)
    (ht : |t| < Real.pi / 2) (uE : ℕ) (huE : uE % 2 = 0) :
    GenP.genC (Pt ell M R (by omega) (neC0 ell M R) t a) (Bpatf uE) = Bpatf uE := by
  have h0 := Pt_Q1_pat hell2 hE hdvd hM hR a t ht uE huE
  show Cop (neLam M R) (Pt ell M R (by omega) (neC0 ell M R) t a).Q1 (Bpatf uE) = Bpatf uE
  unfold Cop hLift
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
  rw [h0]
  simp

theorem Pt_D2in_pat (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ)
    (ht : |t| < Real.pi / 2) (uE : ℕ) :
    (Pt ell M R (by omega) (neC0 ell M R) t a).D2in (Bpat uE) = 0 := by
  obtain ⟨θ, hθ, hφ, hreg⟩ := Pt_unit_cartan hell2 hE hdvd hM hR a t ht
  have hC : C2tilde ell (Pt ell M R (by omega) (neC0 ell M R) t a).unitBgU (Bpatf uE) = 0 := by
    funext c
    exact C2tilde_sig hθ hφ hreg (Bpatf uE) (Bpatf_sig uE) c
  unfold IngrBParams.D2in
  show WithLp.toLp 2 (((ell : ℝ)⁻¹) • hLift (neLam M R) (Pt ell M R (by omega) (neC0 ell M R) t a).Q1
    (C2tilde ell (Pt ell M R (by omega) (neC0 ell M R) t a).unitBgU (Bpatf uE))) = 0
  rw [hC]
  simp

end

end AdalyFormal.NcwdhTwo
