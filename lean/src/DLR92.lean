import DLR91

/-!
# DL92 -- the Combes–Thomas constants as EXPLICIT real functions of the numeric fields (`FF.*`), with `rfl` bridges

Every derived constant of the abstract CT chain (DL12 `K0 K1 epsX epsDX`, DL13/14 `dGam dGi nX nDX kF dF gi dT kZ kDZ dZ dDZ dW`,
DL16/17 `nW δCW EA2 EG`, DL19 `X0 Y0 Ex Ey Px Py KD EN`) is a formula in the numeric fields of the structure only.  `FF.*` writes
these formulas as plain functions of reals; the bridges `site_*`, `gam_*`, `ginv_*`, `n_*` are `rfl` for EVERY structure (not only
the models).  Purpose: limits/continuity arguments in the parameters (DL93–), which cannot be stated on structures carrying proofs.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.DLayer

open AdalyFormal.AsmM0 (KhatM0)

namespace FF

noncomputable def K0 (c δD δQ m q : ℝ) : ℝ :=
  Real.sqrt (48 / c) * δD + (8 / c) * δD ^ 2 + (4 / c) * m * (2 * q * δQ + δQ ^ 2)
noncomputable def K1 (c δD δQ m q : ℝ) : ℝ :=
  Real.sqrt 24 * δD + 2 * Real.sqrt (12 / c) * δD ^ 2 + Real.sqrt (12 / c) * m * (2 * q * δQ + δQ ^ 2)
noncomputable def epsX (c δD δQ m q : ℝ) : ℝ :=
  (4 / c) * δQ + (4 / c) * δD * (q / Real.sqrt c) + K0 c δD δQ m q * (q / c)
noncomputable def epsDX (c δD δQ m q : ℝ) : ℝ :=
  Real.sqrt (12 / c) * δQ + Real.sqrt (12 / c) * δD * (q / Real.sqrt c) + K1 c δD δQ m q * (q / c)
noncomputable def dGam (c δD δQ m q : ℝ) : ℝ := 2 * epsX c δD δQ m q * (q / c) + epsX c δD δQ m q ^ 2
noncomputable def dGi (c δD δQ m q cG : ℝ) : ℝ := dGam c δD δQ m q / cG ^ 2
noncomputable def nX (c δD δQ m q : ℝ) : ℝ := q / c + epsX c δD δQ m q
noncomputable def nDX (c δD δQ m q : ℝ) : ℝ := q / Real.sqrt c + epsDX c δD δQ m q
noncomputable def kF (c δD δQ m q : ℝ) : ℝ := nDX c δD δQ m q + δD * nX c δD δQ m q
noncomputable def dF (c δD δQ m q : ℝ) : ℝ := δD * nX c δD δQ m q + epsDX c δD δQ m q
noncomputable def gi (cG : ℝ) : ℝ := 1 / cG
noncomputable def dT (c δD δQ m q cG : ℝ) : ℝ :=
  δD + epsX c δD δQ m q * gi cG * kF c δD δQ m q + (q / c) * dGi c δD δQ m q cG * kF c δD δQ m q
    + (q / c) * gi cG * dF c δD δQ m q
noncomputable def kZ (c δD δQ m q cG : ℝ) : ℝ :=
  Real.sqrt (48 / c) + (4 / c) * nX c δD δQ m q * gi cG * kF c δD δQ m q
noncomputable def kDZ (c δD δQ m q cG : ℝ) : ℝ :=
  Real.sqrt 24 + Real.sqrt (12 / c) * nX c δD δQ m q * gi cG * kF c δD δQ m q
noncomputable def dZ (c δD δQ m q cG : ℝ) : ℝ :=
  (8 / c) * δD + K0 c δD δQ m q / Real.sqrt c
  + ((4 / c) * δD / Real.sqrt c + K0 c δD δQ m q / c) * nX c δD δQ m q * gi cG * kF c δD δQ m q
  + (1 / c) * epsX c δD δQ m q * gi cG * kF c δD δQ m q + (1 / c) * (q / c) * dGi c δD δQ m q cG * kF c δD δQ m q
  + (1 / c) * (q / c) * gi cG * dF c δD δQ m q
noncomputable def dDZ (c δD δQ m q cG : ℝ) : ℝ :=
  2 * Real.sqrt (12 / c) * δD + K1 c δD δQ m q / Real.sqrt c
  + (Real.sqrt (12 / c) * δD / Real.sqrt c + K1 c δD δQ m q / c) * nX c δD δQ m q * gi cG * kF c δD δQ m q
  + (1 / Real.sqrt c) * epsX c δD δQ m q * gi cG * kF c δD δQ m q
  + (1 / Real.sqrt c) * (q / c) * dGi c δD δQ m q cG * kF c δD δQ m q
  + (1 / Real.sqrt c) * (q / c) * gi cG * dF c δD δQ m q
noncomputable def dW (c δD δQ m q cG : ℝ) : ℝ := δD * kZ c δD δQ m q cG + dDZ c δD δQ m q cG
noncomputable def nW (c δD δQ m q cG : ℝ) : ℝ := 1 + kDZ c δD δQ m q cG + dDZ c δD δQ m q cG
noncomputable def δCW (c δD δQ m q cG δC κ δK : ℝ) : ℝ :=
  δC + δK * kZ c δD δQ m q cG + κ * dZ c δD δQ m q cG
noncomputable def EA2 (c δD δQ m q cG ν δν : ℝ) : ℝ :=
  nW c δD δQ m q cG * ν * dW c δD δQ m q cG + nW c δD δQ m q cG * δν * (nW c δD δQ m q cG + dW c δD δQ m q cG)
  + dW c δD δQ m q cG * (ν + δν) * (nW c δD δQ m q cG + dW c δD δQ m q cG)
noncomputable def EG (c δD δQ m q cG δC κ δK ν δν δB M : ℝ) : ℝ :=
  (1 / 4) * ν * nW c δD δQ m q cG ^ 2 + 5 * δCW c δD δQ m q cG δC κ δK ^ 2 + 5 * dT c δD δQ m q cG ^ 2
    + 5 * M * δB ^ 2 + EA2 c δD δQ m q cG ν δν

/-! ### the Schur-complement level, in terms of the `G⁻¹`-level values -/
noncomputable def X0 (cg qb : ℝ) : ℝ := qb / cg
noncomputable def Y0 (cg qb δB : ℝ) : ℝ := (2 / cg) * (qb + δB)
noncomputable def Ex (cg qb : ℝ) : ℝ := qb * X0 cg qb
noncomputable def Ey (EGv cg qb δB : ℝ) : ℝ := (4 / 3) * (EGv * Y0 cg qb δB ^ 2 + Y0 cg qb δB * (qb + δB))
noncomputable def Px (ν nWv cg qb : ℝ) : ℝ := Real.sqrt (Ex cg qb + ν * nWv ^ 2 * X0 cg qb ^ 2)
noncomputable def Py (EGv ν nWv cg qb δB : ℝ) : ℝ := Real.sqrt (Ey EGv cg qb δB + ν * nWv ^ 2 * Y0 cg qb δB ^ 2)
noncomputable def KD (dWv nWv ν δν : ℝ) : ℝ :=
  dWv * ((ν + δν) * (nWv + dWv)) + nWv * (δν * (nWv + dWv) + ν * dWv)
noncomputable def EN (EGv nWv dWv δCWv dTv ν δν δB M cg qb : ℝ) : ℝ :=
  δB * Y0 cg qb δB + X0 cg qb * δB
  + (δCWv * X0 cg qb * (Py EGv ν nWv cg qb δB + δCWv * Y0 cg qb δB) + Px ν nWv cg qb * (δCWv * Y0 cg qb δB))
  + KD dWv nWv ν δν * X0 cg qb * Y0 cg qb δB
  + (dTv * X0 cg qb * (Py EGv ν nWv cg qb δB + dTv * Y0 cg qb δB) + Px ν nWv cg qb * (dTv * Y0 cg qb δB))
  + (δB * X0 cg qb * (Real.sqrt M * Py EGv ν nWv cg qb δB) + M * δB ^ 2 * X0 cg qb * Y0 cg qb δB
    + Real.sqrt M * Px ν nWv cg qb * δB * Y0 cg qb δB)

end FF

/-! ### the bridges (definitional, for every structure) -/
section bridges
variable {S E Y P B : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [CompleteSpace P] [CompleteSpace B]

theorem site_epsX_FF (H : SiteHyp S E Y) (q : ℝ) : H.epsX q = FF.epsX H.c H.δD H.δQ H.m q := rfl

theorem gam_dT_FF (G : GamHyp S E Y) : G.dT = FF.dT G.c G.δD G.δQ G.m G.q G.cG := rfl
theorem gam_dW_FF (G : GamHyp S E Y) : G.dW = FF.dW G.c G.δD G.δQ G.m G.q G.cG := rfl
theorem gam_kZ_FF (G : GamHyp S E Y) : G.kZ = FF.kZ G.c G.δD G.δQ G.m G.q G.cG := rfl
theorem gam_dZ_FF (G : GamHyp S E Y) : G.dZ = FF.dZ G.c G.δD G.δQ G.m G.q G.cG := rfl

theorem ginv_nW_FF (I : GinvHyp S E Y P B) : I.nW = FF.nW I.c I.δD I.δQ I.m I.q I.cG := rfl
theorem ginv_δCW_FF (I : GinvHyp S E Y P B) : I.δCW = FF.δCW I.c I.δD I.δQ I.m I.q I.cG I.δC I.κ I.δK := rfl
theorem ginv_EG_FF (I : GinvHyp S E Y P B) :
    I.EG = FF.EG I.c I.δD I.δQ I.m I.q I.cG I.δC I.κ I.δK I.ν I.δν I.δB I.M := rfl

theorem n_EN_FF (J : NHyp S E Y P B) :
    J.EN = FF.EN J.Iv.EG J.Iv.nW J.Iv.Gm.dW J.Iv.δCW J.Iv.Gm.dT J.ν J.δν J.δB J.M J.cg J.qb := rfl

end bridges

/-! ### the k-free model constants of DL38/DL52/DL82, as explicit functions -/

/-- `EGM0 = FF.EG` at the model parameters -/
theorem EGM0_FF (ell : ℕ) (a ρ θ : ℝ) (hc : CondM0 ell a ρ θ) :
    EGM0 ell a ρ θ hc = FF.EG (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ) (δCS θ) (κS ρ) (δKS ρ θ) (νS ρ)
      (δνS ρ θ) (δBS ell a ρ θ) 1 := rfl

theorem nW_model_FF (ell : ℕ) (a ρ θ : ℝ) (hc : CondM0 ell a ρ θ) :
    hc.ginv.nW = FF.nW (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ) := rfl

theorem ENfree_FF (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (hK : 0 < KhatM0 ell a t ρ)
    (hEG : 4 * EGM0 ell a ρ θ hc ≤ 1 / KhatM0 ell a t ρ) :
    ENfree ell a t ρ θ hc hK hEG
      = FF.EN (FF.EG (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ) (δCS θ) (κS ρ) (δKS ρ θ) (νS ρ) (δνS ρ θ)
          (δBS ell a ρ θ) 1)
        (FF.nW (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ))
        (FF.dW (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ))
        (FF.δCW (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ) (δCS θ) (κS ρ) (δKS ρ θ))
        (FF.dT (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ))
        (νS ρ) (δνS ρ θ) (δBS ell a ρ θ) 1 (1 / KhatM0 ell a t ρ) (qBS ell a ρ) := rfl

theorem EGM1_FF (ell : ℕ) (a ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (νψ δψ : ℝ) (hν : 0 ≤ νψ) (hδ : 0 ≤ δψ) :
    EGM1 ell a ρ θ hc νψ δψ hν hδ = FF.EG (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ) (δCS θ) (κS ρ) (δKS ρ θ)
      (νS ρ + νψ) (δνS ρ θ + δψ) (δBS ell a ρ θ) 1 := rfl

theorem EN1free_FF (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (νψ δψ : ℝ) (hν : 0 ≤ νψ) (hδ : 0 ≤ δψ)
    (hK : 0 < KhatM0 ell a t ρ) (hcg : 0 < cg1 ell a t ρ θ hc νψ)
    (hEG : 4 * EGM1 ell a ρ θ hc νψ δψ hν hδ ≤ cg1 ell a t ρ θ hc νψ) :
    EN1free ell a t ρ θ hc νψ δψ hν hδ hK hcg hEG
      = FF.EN (FF.EG (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ) (δCS θ) (κS ρ) (δKS ρ θ) (νS ρ + νψ)
          (δνS ρ θ + δψ) (δBS ell a ρ θ) 1)
        (FF.nW (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ))
        (FF.dW (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ))
        (FF.δCW (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ) (δCS θ) (κS ρ) (δKS ρ θ))
        (FF.dT (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ))
        (νS ρ + νψ) (δνS ρ θ + δψ) (δBS ell a ρ θ) 1 (cg1 ell a t ρ θ hc νψ) (qBS ell a ρ) := rfl

theorem cg1_FF (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (νψ : ℝ) :
    cg1 ell a t ρ θ hc νψ = 1 / KhatM0 ell a t ρ - νψ * FF.nW (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ) ^ 2 :=
  rfl

theorem bN1_FF (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (νψ : ℝ) :
    bN1 ell a t ρ θ hc νψ = bNS a ρ (δS ell ρ)
      * (1 + νψ * FF.nW (cS a ρ) (δDS θ) (δQS a θ) 1 (qS a) (cGS ell a ρ θ) ^ 2 * KhatM0 ell a t ρ) := rfl

#print axioms EGM0_FF
#print axioms ENfree_FF
#print axioms EN1free_FF

end AdalyFormal.DLayer
