import NtPtH6b

/-!
# PtH6c -- the kernel of the flat nested `Ginv` is trivial (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {ell M R : ℕ}

theorem kernel_trivial (hP : PGeo ell M R) {x : BondFnL2 (scaleUp ell 2 (neLu M R))} (hk : KD ell M R x)
    (hT : Tfull (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) x = 0) : x = 0 := by
  have hp1 : 1 ≤ neP1 ell M R := by have := hP.p0pos; have := hP.collar_p; have := hP.rm2; omega
  obtain ⟨φ, c, hpot⟩ := hodge_pot x (hk.curl_zero hP)
  have hc1 : c 1 = 0 := c1_zero x φ c hpot 0 0 (fun t =>
    x_zero1 hP hk 0 t 0 hP.hNpos (by simp only [Omv]; omega))
  have hc2 : c 2 = 0 := c2_zero x φ c hpot 0 0 (fun t =>
    x_zero2 hP hk 0 0 t hP.hNpos (by simp only [Omv]; omega))
  obtain ⟨r0, r1, r2⟩ := rel_g x φ c hpot hc1 hc2
  have hpd : PD ell M R x (gpot φ (c 0)) := by
    refine ⟨r0, r1, r2, fun a b d => ?_, fun a b d => ?_⟩
    · unfold gpot
      have : mkS (scaleUp ell 2 (neLu M R)) a (b % neN ell M R) d = mkS (scaleUp ell 2 (neLu M R)) a b d :=
        mkS_ext rfl (by rw [← hNLμ hP 1, Nat.mod_mod]) rfl
      rw [this]
    · unfold gpot
      have : mkS (scaleUp ell 2 (neLu M R)) a b (d % neN ell M R) = mkS (scaleUp ell 2 (neLu M R)) a b d :=
        mkS_ext rfl rfl (by rw [← hNLμ hP 2, Nat.mod_mod])
      rw [this]
  obtain ⟨hκ, -, -⟩ := chain_apply hP hk hpd
  have hx := xi_grad hP hk hpd hκ
  have hn := xi_nqp hP hk hpd
  have hT' : Tfull (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R)))
      (gradL2 (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) (xiOf ell M R (gpot φ (c 0)))) = 0 := by
    rw [← hx]; exact hT
  have h0 := final_step (geomOf ell 2 (neS ell M R)) _ hn hT'
  rw [hx, h0]

#print axioms kernel_trivial

end AdalyFormal.CoverOmega
