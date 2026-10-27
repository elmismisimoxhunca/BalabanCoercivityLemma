import NsCvO23

/-!
# CvO24 -- curvature of a Z-field on a Cartan configuration (lane omega)

`zfun f : Bond L → SuTwo` is the function underlying `zfield f`.  On a Cartan `U`:
* `curl_zfun_01 : curl_U (zfun f) (x,(0,1)) = dgS (f(x₀+1) - f(x₀))` (written with the shifted site),
* `curl_zfun_02 = curl_zfun_12 = 0`.
Also `hsInner (RMap V Y) (dgS a) = hsInner Y (dgS a)` for Cartan `V`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.IngredientFamilyR2 (toM2 toM2_mem)

variable {L : PeriodicLatticeExtent}

theorem dgS_add (a b : ℝ) : dgS (a + b) = dgS a + dgS b := by
  apply Subtype.ext; rw [dgS_coe]; simp only [Submodule.coe_add, dgS_coe]; exact dg_add a b

theorem dgS_smul (c a : ℝ) : dgS (c * a) = c • dgS a := by
  apply Subtype.ext
  rw [dgS_coe]
  simp only [SetLike.val_smul, dgS_coe, Complex.coe_smul]
  exact (dg_smul c a).symm

theorem dgS_neg (a : ℝ) : dgS (-a) = - dgS a := by
  have := dgS_smul (-1) a
  rw [neg_one_mul, neg_one_smul] at this; exact this

theorem dgS_sub (a b : ℝ) : dgS (a - b) = dgS a - dgS b := by
  rw [sub_eq_add_neg, dgS_add, dgS_neg, sub_eq_add_neg]

theorem hsInner_RMap_dgS {V : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hV : IsCartan V) (Y : SuTwo) (a : ℝ) :
    hsInner (RMap V Y) (dgS a) = hsInner Y (dgS a) := by
  have h := AdalyFormal.Balaban.CovariantHjMinimizer.hsInner_RMap_transpose V Y (dgS a)
  rw [RMap_dgS (isCartan_inv hV)] at h
  exact h

theorem hsInner_dgS_smul (Y : SuTwo) (c a : ℝ) : hsInner Y (dgS (c * a)) = c * hsInner Y (dgS a) := by
  rw [dgS_smul, AdalyFormal.Balaban.SuTwoInner.hsInner_symm, AdalyFormal.Balaban.SuTwoInner.hsInner_smul_left, AdalyFormal.Balaban.SuTwoInner.hsInner_symm]

theorem hsInner_dgS_add (Y : SuTwo) (a b : ℝ) : hsInner Y (dgS (a + b)) = hsInner Y (dgS a) + hsInner Y (dgS b) := by
  rw [dgS_add, AdalyFormal.Balaban.SuTwoInner.hsInner_symm, AdalyFormal.Balaban.SuTwoInner.hsInner_add_left, AdalyFormal.Balaban.SuTwoInner.hsInner_symm (dgS a) Y, AdalyFormal.Balaban.SuTwoInner.hsInner_symm (dgS b) Y]

/-- the function underlying `zfield`. -/
noncomputable def zfun (f : ℕ → ℝ) : Bond L → SuTwo := fun b => if b.2 = 1 then dgS (f (b.1 0).val) else 0

theorem zfield_eq (f : ℕ → ℝ) : (zfield f : BondFnL2 L) = WithLp.toLp 2 (zfun f) := rfl

theorem zfun_diag (f : ℕ → ℝ) (b : Bond L) : diagP (zfun f b) = zfun f b := by
  unfold zfun; split_ifs
  · exact diagP_dgS _
  · apply Subtype.ext; rw [diagP_coe]; simp

theorem curl_zfun_01 {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U) (f : ℕ → ℝ)
    (x : PeriodicLatticeSite L) (h : ((0 : Fin 3), (1 : Fin 3)).1 < ((0 : Fin 3), (1 : Fin 3)).2) :
    curlValueCovariant U (zfun f) (x, ⟨((0 : Fin 3), (1 : Fin 3)), h⟩) =
      dgS (f ((periodicLatticeShift x 0) 0).val - f (x 0).val) := by
  unfold curlValueCovariant zfun
  simp only [if_neg (show ¬ ((0 : Fin 3) = 1) by decide), if_true]
  rw [RMap_dgS (hU _), dgS_sub]
  simp

theorem curl_zfun_02 {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (f : ℕ → ℝ)
    (x : PeriodicLatticeSite L) (h : ((0 : Fin 3), (2 : Fin 3)).1 < ((0 : Fin 3), (2 : Fin 3)).2) :
    curlValueCovariant U (zfun f) (x, ⟨((0 : Fin 3), (2 : Fin 3)), h⟩) = 0 := by
  unfold curlValueCovariant zfun
  simp only [if_neg (show ¬ ((0 : Fin 3) = 1) by decide), if_neg (show ¬ ((2 : Fin 3) = 1) by decide), if_true]
  simp

theorem curl_zfun_12 {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U) (f : ℕ → ℝ)
    (x : PeriodicLatticeSite L) (h : ((1 : Fin 3), (2 : Fin 3)).1 < ((1 : Fin 3), (2 : Fin 3)).2) :
    curlValueCovariant U (zfun f) (x, ⟨((1 : Fin 3), (2 : Fin 3)), h⟩) = 0 := by
  unfold curlValueCovariant zfun
  simp only [if_neg (show ¬ ((2 : Fin 3) = 1) by decide), if_true]
  have e : (periodicLatticeShift x 2) 0 = x 0 := by simp [periodicLatticeShift]
  rw [e, RMap_dgS (hU _)]
  simp

#print axioms dgS_sub
#print axioms hsInner_RMap_dgS
#print axioms hsInner_dgS_smul
#print axioms hsInner_dgS_add
#print axioms zfun_diag
#print axioms curl_zfun_01
#print axioms curl_zfun_02
#print axioms curl_zfun_12

end AdalyFormal.CoverOmega
