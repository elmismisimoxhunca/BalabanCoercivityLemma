import NuB3

/-!
# NuB4 -- the pencil identity: on `Ad_h`-fixed vectors, `<x', G1inv(t) x> = <x', G1inv(0) x> + (cos 2t - 1) β(x', x)` (lane ncwdh_ell2_20261018)
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

section
variable [CfData]
variable {ell M R : ℕ}

/-- the common form `β(x', x) = bPl_{Pl0}(W₀ x', W₀ x)` (flat reference). -/
noncomputable def betaForm (ell M R : ℕ) (a : ℝ) (x' x : ↥(bondSupp (geomOf ell 2 (neS ell M R)))) : ℝ :=
  bPl (plaqIn (geomOf ell 2 (neS ell M R)).Om0) (Pl0 (neC0 ell M R))
    (Wop (geomOf ell 2 (neS ell M R)) (stag0Cfg (neC0 ell M R) 0) a (iE (geomOf ell 2 (neS ell M R)) x'))
    (Wop (geomOf ell 2 (neS ell M R)) (stag0Cfg (neC0 ell M R) 0) a (iE (geomOf ell 2 (neS ell M R)) x))

theorem G1inv_affine (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) {a : ℝ} (ha : 0 < a) {t : ℝ}
    (ht : |t| < Real.pi / 2) (x' x : ↥(bondSupp (geomOf ell 2 (neS ell M R))))
    (hx' : TEc (geomOf ell 2 (neS ell M R)) x' = x') (hx : TEc (geomOf ell 2 (neS ell M R)) x = x) :
    ⟪x', (Pt ell M R (by omega) (neC0 ell M R) t a).G1inv x⟫ =
      ⟪x', (Pt ell M R (by omega) (neC0 ell M R) 0 a).G1inv x⟫ + (Real.cos (2 * t) - 1) * betaForm ell M R a x' x := by
  have hg := nGeo_two hell2 hdvd hM hR
  have hell : 0 < ell := by omega
  have h0 : |(0 : ℝ)| < Real.pi / 2 := by rw [abs_zero]; positivity
  have St := nested_z0Setup hell2 hE hdvd hM hR t ht
  have S0 := nested_z0Setup hell2 hE hdvd hM hR 0 h0
  have hxs' : SigB (WithLp.ofLp (x' : BondFnL2 (scaleUp ell 2 (neLu M R)))) := (TEc_fixed_iff _ x').mp hx'
  have hxs : SigB (WithLp.ofLp (x : BondFnL2 (scaleUp ell 2 (neLu M R)))) := (TEc_fixed_iff _ x).mp hx
  rw [G1inv_eq_Ginv hell2 hE hdvd hM hR t a ht x hxs, G1inv_eq_Ginv hell2 hE hdvd hM hR 0 a h0 x hxs]
  have hout : ∃ y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)), y ∉ (geomOf ell 2 (neS ell M R)).Om0 := by
    refine ⟨fun _ => 0, fun hmem => ?_⟩
    have := ((neS_om0 (ell := ell) (M := M) (R := R) (fun _ => 0)).mp hmem).1
    have hp := ne_P0_pos_two hell2 hM hR
    simp at this; omega
  have hN : 2 ∣ scaleUp ell 2 (neLu M R) 1 + 1 := St.z.hN
  have key := Ginv_family_affine (geomOf ell 2 (neS ell M R)) a (stag0Cfg_cartan _ t) (stag0Cfg_cartan _ 0)
    (bondSectorOf (geomOf ell 2 (neS ell M R)) (stag0Cfg (neC0 ell M R) t))
    (bondSectorOf (geomOf ell 2 (neS ell M R)) (stag0Cfg (neC0 ell M R) 0))
    (Pt ell M R hell (neC0 ell M R) t a).Jf (Pt ell M R hell (neC0 ell M R) 0 a).Jf
    (delpA_unit _ _ ha (by show 2 ≤ ell; omega) hout) (delpA_unit _ _ ha (by show 2 ≤ ell; omega) hout)
    (fun z hz => Qfull_sig_indep hell2 hE hdvd hM hR ht h0 ((sigB'_iff z).mp hz))
    (Pl0 (neC0 ell M R)) (ω := Real.cos (2 * t)) (ω0 := Real.cos (2 * 0))
    (fun p => holCos_stag0 hN _ t p) (fun p => holCos_stag0 hN _ 0 p) x' x ((sigB'_iff _).mpr hxs') ((sigB'_iff _).mpr hxs)
  rw [show Real.cos (2 * (0 : ℝ)) = 1 by simp] at key
  exact key

end

end AdalyFormal.NcwdhTwo
