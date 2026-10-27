import NtCvOF8

/-!
# CvOF9 -- `firstTerm` and `genForm` of the Z-profile at a chain saddle (lane omega)
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

variable {ell M R : ℕ}

/-- the `t`-independent constant of the energy identity: `<y, zrow (a * l^j * rho_y)>`. -/
noncomputable def Kc (ell M R : ℕ) (a : ℝ) (g : ℕ → ℝ) : ℝ :=
  inner ℝ (zrow (geomOf ell 2 (neS ell M R)) (rhoY ell g))
    (zrow (geomOf ell 2 (neS ell M R)) (fun j u => a * ((ell : ℝ) ^ j * rhoY ell g j u)))

theorem nested_firstTerm (hell3 : 3 ≤ ell) (hE : StagOK ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (htπ : |t| < tcap ell)
    (hN : IsUnit (GenP.Nmat (Pn ell M R (by omega) a t))) (hG1 : IsUnit (Pn ell M R (by omega) a t).G1inv)
    (g : ℕ → ℝ) (e : Fin (nN ell M R) → ℝ)
    (hrad : ∀ d : Fin (nN ell M R) → ℝ, d ∈ Vsub (rowOfN ell M R) → BF (neC ell M R - neP0 ell M R) (Real.cos t) e d = 0)
    (hS : ∀ j, j ≤ 2 → ∀ r, isRowN ell M R j r → fSum ell j (fe (neP0 ell M R) e) r = (ell : ℝ) ^ j * rhoY ell g j r) :
    GenP.firstTerm (Pn ell M R (by omega) a t) (zfield g) =
      (Pn ell M R (by omega) a t).eta *
        (c0 * ((((scaleUp ell 2 (neLu M R)) 1 + 1) * ((scaleUp ell 2 (neLu M R)) 2 + 1) : ℕ) : ℝ) *
          qF (neC ell M R - neP0 ell M R) (Real.cos t) e + Kc ell M R a g) := by
  have hg := nGeo hell3 hdvd hM hR
  have hell : 0 < ell := by omega
  have S := nested_stagSetup hell3 hE hdvd hM hR
  set P := Pn ell M R hell a t with hP
  have hf := zfield_fe_mem hg hell3 hM hR e
  set ρV := rhoV ell M R (neC ell M R - neP0 ell M R) (Real.cos t) a e with hρV
  have hv := zfield_Wt_mem hell3 hdvd hM hR ρV
  set x : ↥(bondSupp P.G) := ⟨zfield (fe (neP0 ell M R) e), hf⟩ with hx
  have hG1x := nested_G1inv_eq hell3 hE hdvd hM hR a t htπ e hrad hf hv
  have hQs : P.data.Qs (zrow P.G ρV) = ⟨zfield (Wt ell (isRowN ell M R) ρV), hv⟩ :=
    Subtype.ext (Qs_zrow S t htπ a P.Jf ρV hv)
  have hG1xs : P.G1inv x = P.data.Qs (zrow P.G ρV) := by
    rw [hQs]; exact Subtype.ext hG1x
  have hQx : P.data.Q x = zrow P.G (rhoY ell g) := nested_Q_eq hell3 hE hdvd hM hR a t htπ g e hS
  have hNv : GenP.Nmat P (zrow P.G ρV) = zrow P.G (rhoY ell g) := by
    show P.data.Q (P.data.G1 P.G1inv (P.data.Qs (zrow P.G ρV))) = _
    rw [← hG1xs]
    have : P.data.G1 P.G1inv (P.G1inv x) = x := by
      show Ring.inverse P.G1inv (P.G1inv x) = x
      obtain ⟨u, hu⟩ := hG1
      rw [← hu, Ring.inverse_unit]
      have : ((↑u⁻¹ : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G)) * (↑u : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G))) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      show ((↑u⁻¹ : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G)) * (↑u : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G))) x = x
      rw [this]; rfl
    rw [this]; exact hQx
  have hinv := ring_inverse_apply_of_eq _ hN _ _ hNv
  have hτ := Pn_tau_adjoint hell3 hdvd hM hR a t g
  unfold GenP.firstTerm
  rw [hτ, hinv]
  have h1 : (inner ℝ (zrow P.G (rhoY ell g)) (zrow P.G ρV) : ℝ) = inner ℝ x (P.G1inv x) := by
    rw [← hQx, P.data.Q_adj, hG1xs]
  rw [h1]
  have h2 : (inner ℝ x (P.G1inv x) : ℝ) = inner ℝ (zfield (fe (neP0 ell M R) e) : BondFnL2 (scaleUp ell 2 (neLu M R))) (zfield (Wt ell (isRowN ell M R) ρV)) := by
    rw [← hG1x]; rfl
  rw [h2, hρV, inner_Wt_split hell3 hdvd hM hR t a e hrad]
  congr 1
  congr 1
  have h3 := inner_Q_zrow S t htπ (zfield (fe (neP0 ell M R) e)) (fun j u => a * fSum ell j (fe (neP0 ell M R) e) u)
  rw [← h3]
  have h4 : QfullOf P.G (stagCfg (neC ell M R) t) (zfield (fe (neP0 ell M R) e)) = zrow P.G (rhoY ell g) := by
    exact nested_Q_eq hell3 hE hdvd hM hR a t htπ g e hS
  rw [h4]
  unfold Kc
  congr 1
  refine zrow_congr_nested hell3 hdvd hM hR _ _ (fun j hj r hr => ?_)
  rw [hS j hj r hr]

#print axioms nested_firstTerm

end AdalyFormal.CoverOmega
