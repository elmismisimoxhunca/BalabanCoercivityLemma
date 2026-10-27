import TL8
import PP2
import OGP0

/-!
# TL9 -- `RegData` from `M1Regular12` (`regData_M112`) and the lane-E mass commutator for M1 with a `k`-free constant

`regData_M112` : `RegData ell k Lu S (U^g) (SstarM ell f M α₀)` from the M1 witness `(g, A)` (explicit definition, not an
existential): `ε = epsM`, `W = WM12`, `S* = SstarM`.   `massComm_M112` : `MassComm ell M k κ c S (U^g) a (CMcStar ell M κ c a S*)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.OneGap12

open AdalyFormal.TowerLoc
open AdalyFormal.OneGap12

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.NonflatJet
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.StatementLaneR8
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.BondComposite
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.M1IMS

section m1
variable {ell M R k f : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ η : ℝ}
  (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hroom : 17 * ell ≤ R * M)
  (hT3 : ∀ μ, 3 ≤ Lu μ + 1) (U : LinkCfg (scaleUp ell k Lu))
  (g : PeriodicLatticeSite (scaleUp ell k Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ)
  (A : Bond (scaleUp ell k Lu) → Matrix (Fin 2) (Fin 2) ℂ)
  (hU : ∀ e : Bond (scaleUp ell k Lu), ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
  (hB : AdalyFormal.OneGap12.M1Bounds12 S ell M f k α₀ η A) (hη : 0 < η) (hα0 : 0 ≤ α₀)
  (ha1 : (f : ℝ) * M * α₀ ≤ 1)
  (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 f M α₀ ≤ 1)
  (hsmA : (1 + 3 * Real.pi) * rho1 f M α₀ ≤ 1 / (1000 * (ell : ℝ) ^ 4))
  (hrr : Real.pi / 2 * ((loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 f M α₀)) < r0)

include hell2 hS hroom hT3 hU hB hη hα0 ha1 hsm4 hsmA hrr in
/-- **the regional class data of the M1 regime** (explicit; `ε = epsM`, `W = WM12`, `S* = SstarM`). -/
def regData_M112 : RegData ell k Lu S (periodicGaugeTransform g U) (SstarM ell f M α₀) where
  ε := fun j l => epsM ell f M α₀ j l
  W := fun j l => WM12 ell k S j l
  hcl := fun j l hlk z hzW hzA μ => hcl_M112 hell2 hS hroom hT3 U g A hU hB hη hα0 ha1 hsm4 j l hlk z hzW hzA μ
  hε0 := fun j l _ => epsM_nonneg ell f M α₀ hα0 j l
  hsm := fun j l _ => by
    have hell : 0 < ell := by omega
    have h0 := epsM_nonneg ell f M α₀ hα0 j l
    have h1 := rhoOf_le (ell := ell) _ h0
    have hsmall : epsM ell f M α₀ j l ≤ 1 / (1000 * (ell : ℝ) ^ 4) :=
      (epsM_le ell f M hell α₀ hα0 j l).trans hsmA
    have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
    have hk : epsM ell f M α₀ j l * (ell : ℝ) ^ 4 ≤ 1 / 1000 := by
      have hpos : (0 : ℝ) < (ell : ℝ) ^ 4 := by positivity
      have := mul_le_mul_of_nonneg_right hsmall hpos.le
      calc _ ≤ 1 / (1000 * (ell : ℝ) ^ 4) * (ell : ℝ) ^ 4 := this
        _ = 1 / 1000 := by field_simp
    have h4 : (ell : ℝ) ≤ (ell : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((ell : ℝ) - 1), sq_nonneg ((ell : ℝ) ^ 2 - 1)]
    have h5 : (ell : ℝ) * epsM ell f M α₀ j l ≤ 1 / 1000 := by
      nlinarith [mul_le_mul_of_nonneg_right h4 h0]
    have := Real.pi_gt_three
    nlinarith
  hr := fun j l _ => by
    have hell : 0 < ell := by omega
    have h0 := epsM_nonneg ell f M α₀ hα0 j l
    have hle := epsM_le ell f M hell α₀ hα0 j l
    refine lt_of_le_of_lt ?_ hrr
    have hpi := Real.pi_pos
    gcongr
  hW := fun j r l hl z hz => ⟨hl, r, hz⟩
  hSstar := fun j => sum_theta_epsM ell f M hell2 α₀ hα0 hsmA j

include hell2 hS hroom hT3 hU hB hη hα0 ha1 hsm4 hsmA hrr in
/-- **lane E's mass commutator for the M1 regime, `k`-free constant** -/
theorem massComm_M112 {κ c : ℕ} (hκ : 0 < κ) (hM : 0 < M) (hR1 : 1 ≤ R) (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c)
    (a : ℝ) (ha : 0 ≤ a) :
    MassComm ell M k κ c S (periodicGaugeTransform g U) a (CMcStar ell M κ c a (SstarM ell f M α₀)) :=
  massComm_proper_loc hS hκ hM hell2 hR1 hR hc (periodicGaugeTransform g U) (SstarM ell f M α₀)
    (regData_M112 hell2 hS hroom hT3 U g A hU hB hη hα0 ha1 hsm4 hsmA hrr) a ha

end m1

end AdalyFormal.OneGap12
#print axioms AdalyFormal.OneGap12.regData_M112
#print axioms AdalyFormal.OneGap12.massComm_M112
