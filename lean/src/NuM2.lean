import NuM1

/-!
# NuM2 -- `genForm < 0` for the pattern competitor at a parameter just above the Z-chain crossing (lane ncwdh_ell2_20261018)

`main_neg_two`: given the flat-point units (`UnitsFour` and injectivity of `Qs` at `t = 0`), there are an even `uE` inside the slab and a
parameter `t`, `|t| < π/2`, at which `WellDefG` holds and `genForm (genC B) < 0` for `B = Bpatf uE`.
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

theorem zfield_sig {L : PeriodicLatticeExtent} (g : ℕ → ℝ) : SigB (WithLp.ofLp (zfield g : BondFnL2 L)) := fun b => zfun_diag g b

theorem Bperp_sig {L : PeriodicLatticeExtent} (uE : ℕ) : SigB (WithLp.ofLp (Bperp uE : BondFnL2 L)) := by
  intro b
  have h1 := Bpat_sig (L := L) uE b
  have h2 := zfield_sig (L := L) (gbar uE) b
  show diagP ((Bpat uE : BondFnL2 L).ofLp b - (zfield (gbar uE) : BondFnL2 L).ofLp b) = _
  rw [map_sub, h1, h2]; rfl

theorem qF1_vec_zero {n : ℕ} (C : ℕ) (c : ℝ) : qF1 C c (0 : Fin n → ℝ) = 0 := by
  simp [qF1, AdalyFormal.CoverJacobi.aF, bF1, dlt, AdalyFormal.CoverJacobi.ex]

theorem genForm_pat_eq (hdvd : 2 ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (ht : |t| < Real.pi / 2) (uE : ℕ) (huE : uE % 2 = 0) :
    GenP.genForm (Pt 2 M R (by norm_num) (neC0 2 M R) t a)
        (WithLp.toLp 2 (GenP.genC (Pt 2 M R (by norm_num) (neC0 2 M R) t a) (Bpatf uE))) =
      (Pt 2 M R (by norm_num) (neC0 2 M R) t a).eta *
        (inner ℝ (ContinuousLinearMap.adjoint (tauExt 2 2 (neLu M R) (by norm_num) (neS 2 M R)) (Bpat uE))
          (Ring.inverse (GenP.Nmat (Pt 2 M R (by norm_num) (neC0 2 M R) t a))
            (ContinuousLinearMap.adjoint (tauExt 2 2 (neLu M R) (by norm_num) (neS 2 M R)) (Bpat uE))) : ℝ) -
      a * (inner ℝ (Bpat uE : BondFnL2 (neLu M R)) (Bpat uE) : ℝ) := by
  rw [Pt_genC_pat rfl (dvd_refl 2) hdvd hM hR a t ht uE huE]
  have hD := Pt_D2in_pat (le_refl 2) (dvd_refl 2) hdvd hM hR a t ht uE
  unfold GenP.genForm GenP.firstTerm
  have : (WithLp.toLp 2 (Bpatf uE) : BondFnL2 (neLu M R)) = Bpat uE := rfl
  rw [this, hD, map_zero, inner_zero_left, mul_zero, sub_zero]
  rfl

end

end AdalyFormal.NcwdhTwo
