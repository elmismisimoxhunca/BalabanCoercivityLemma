import NtCvOU3
import NtCvOF0
import NsCvOK7

/-!
# CvOF1 -- energies of Z-fields: `<zfield f, zfield h> = c0 * T1 * Σ_v f v h v`; `BF e e = Σ_x e_x BF e (single x)` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)

theorem thetaOf_zfun {L : PeriodicLatticeExtent} (f : ℕ → ℝ) (x : PeriodicLatticeSite L) :
    thetaOf (zfun f : Bond L → SuTwo) (x, 1) = f (x 0).val := by
  unfold thetaOf zfun
  simp only [if_true]
  rw [dgS_coe, fromM2_dg]
  rfl

theorem inner_zfield_zfield (L : PeriodicLatticeExtent) (f h : ℕ → ℝ) :
    (inner ℝ (zfield f : BondFnL2 L) (zfield h) : ℝ) =
      c0 * (((L 1 + 1) * (L 2 + 1) : ℕ) : ℝ) * ∑ v ∈ range (L 0 + 1), f v * h v := by
  have hs : SigB (WithLp.ofLp (zfield f : BondFnL2 L)) := fun b => zfun_diag f b
  rw [inner_sig_zfield _ hs h]
  have : ∀ x : PeriodicLatticeSite L, thetaOf (WithLp.ofLp (zfield f : BondFnL2 L)) (x, 1) * h (x 0).val = f (x 0).val * h (x 0).val := by
    intro x
    show thetaOf (zfun f : Bond L → SuTwo) (x, 1) * _ = _
    rw [thetaOf_zfun]
  simp only [this]
  rw [sum_site_x0 L (fun v => f v * h v)]
  ring

/-- `BF e f = Σ_x f_x BF e (single x)`. -/
theorem BF_eq_sum_single {n : ℕ} (C : ℕ) (c : ℝ) (e f : Fin n → ℝ) :
    BF C c e f = ∑ x : Fin n, f x * BF C c e (Pi.single x 1) := by
  let Φ : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => BF C c e f
      map_add' := fun f g => BF_add_right C c e f g
      map_smul' := fun r f => by simpa using BF_smul_right C c r e f }
  have := LinearMap.pi_apply_eq_sum_univ Φ f
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul] at this
  rw [this]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 2
  funext y
  simp [Pi.single_apply, eq_comm]

#print axioms inner_zfield_zfield
#print axioms BF_eq_sum_single

end AdalyFormal.CoverOmega
