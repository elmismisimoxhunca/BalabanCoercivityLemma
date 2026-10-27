import NuE1
import NuQ4
import NuQ2
import NtCvOF4

/-!
# NuE2 -- `G1inv` on the chain Z-fields of the nested instance and the Z-energy (lane ncwdh_ell2_20261018)

`Pt ell M R xs t a`: the genuine parameters of the nested instance with the direction-0 staggered family `stag0Cfg xs t`.
`G1inv_zfield0`: for a chain vector `e`, `G1inv (zfield (fe e)) = zfield (ginvProf0 ..)` (sigma_3: `Delta2 = 0`, then `Ginv_zfield0`).
`inner_G1inv_zfield`: `<x_e, G1inv x_e> = c0 T1 qF1 e + <zfield (fe e), zfield (Wt (a fSum (fe e)))>`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)

section
variable [CfData]
variable {ell M R : ℕ}

/-- the genuine parameters of the nested instance along the direction-0 staggered family. -/
noncomputable abbrev Pt (ell M R : ℕ) (hell : 0 < ell) (xs : ℕ) (t a : ℝ) : IngrBParams :=
  gparams ell 2 (neLu M R) hell (neS ell M R) (stag0Cfg xs t) a (neLam M R)

theorem neC0_ge_P0 (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) : neP0 ell M R ≤ neC0 ell M R := by
  have hcf := CfData.hcf
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  have e1 : ell * M ≤ ell * (ell * M) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have e4 : 10 * (ell * M) ≤ CfData.cf * (ell * M) := Nat.mul_le_mul_right _ hcf
  unfold neC0 neP0 neP1 neA'; omega

theorem neC0_lt_Q0 (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) : neC0 ell M R + 1 < neQ0 ell M R := by
  have hcf := CfData.hcf
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  have e1 : ell * M ≤ ell * (ell * M) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have e3 : CfData.cf * (ell * M) ≤ CfData.cf * (ell * (ell * M)) := Nat.mul_le_mul_left _ e1
  unfold neC0 neQ0 neQ1 neB neA'; omega

theorem G1inv_zfield0 (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (ht : |t| < Real.pi / 2) (e : Fin (nN ell M R) → ℝ)
    (hf : (zfield (fe (neP0 ell M R) e) : BondFnL2 (scaleUp ell 2 (neLu M R))) ∈ bondSupp (geomOf ell 2 (neS ell M R))) :
    (((Pt ell M R (by omega) (neC0 ell M R) t a).G1inv ⟨zfield (fe (neP0 ell M R) e), hf⟩ :
        ↥(bondSupp (Pt ell M R (by omega) (neC0 ell M R) t a).G)) : BondFnL2 (scaleUp ell 2 (neLu M R))) =
      zfield (ginvProf0 ell (isRowN ell M R) (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) (scaleUp ell 2 (neLu M R) 0)
        (neC0 ell M R) t a (fe (neP0 ell M R) e)) := by
  have hg := nGeo_two hell2 hdvd hM hR
  have hell : 0 < ell := by omega
  have S := nested_z0Setup hell2 hE hdvd hM hR t ht
  set P := Pt ell M R hell (neC0 ell M R) t a with hP
  have hcart : CartanCfg P.U := stag0Cfg_cartan _ t
  have hC : ∀ A : BondFnL2 P.Lf, SigB (WithLp.ofLp A) → P.sector.C2full A = 0 := fun A hA =>
    C2fullOf_sig0 S.z P.G S.hG S.hk A hA
  set x : ↥(bondSupp P.G) := ⟨zfield (fe (neP0 ell M R) e), hf⟩ with hx
  have hxs : SigB (WithLp.ofLp (x : BondFnL2 P.Lf)) := fun b => zfun_diag _ b
  have hD2 := Delta2_sig P hcart hC x hxs
  have hG1 : P.G1inv = P.data.Ginv - P.data.Delta2 P.data_laws :=
    P.data.G1inv_unique P.G1inv_spec (P.data.isG1inv_sub P.data_laws)
  have h1 : P.G1inv x = P.data.Ginv x := by
    rw [hG1]; simp [hD2]
  rw [h1]
  exact Ginv_zfield0 S (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R)
    (by ext y; simp only [IngrBParams.G, geomOf, Set.mem_setOf_eq]; exact neS_om0 y)
    (fun j hj v h => hrowJ_nested hg hj v h) a P.Jf (fe (neP0 ell M R) e) hf

end

end AdalyFormal.NcwdhTwo
