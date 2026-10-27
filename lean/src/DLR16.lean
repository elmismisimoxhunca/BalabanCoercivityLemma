import DLR15

/-!
# DL16 -- Combes–Thomas for `G⁻¹ = W*(C*C + Δ')W + T*T + M Q*Q` (abstract, FORM-relative)

`GinvHyp` = `GamHyp` + plaquette space `P`, unit-bond space `B`, curl `C : E → P`, `Δ' : E → E` (symmetric), bond averaging
`Qb : E → B`, `M ≥ 0`, weights `ωP, ωB`, and the commutator / size data
`‖C^± − C‖ ≤ δC`, `‖K‖ ≤ κ`, `‖K^± − K‖ ≤ δK` (`K = C∘D`, the CURVATURE operator: `C∘W = C − K∘Z`), `‖Δ'‖ ≤ ν`,
`‖Δ'^± − Δ'‖ ≤ δν`, `‖Qb^± − Qb‖ ≤ δB`.
* `CW_eq` : `C∘W = C − K∘Z`;  `CW_diff` : `‖(C∘W)^± − C∘W‖ ≤ δCW := δC + δK·kZ + κ·dZ`.
* `Ginv_form` : `⟪f,G⁻¹f⟫ = ‖CWf‖² + ⟪Wf,Δ'Wf⟫ + ‖Tf‖² + M‖Qb f‖²`.
* **`Ginv_CT`** : `⟪f, (G⁻¹)⁺ f⟫ ≥ ¾⟪f,G⁻¹f⟫ − E_G‖f‖²`,
  `E_G = ¼ν nW² + 5δCW² + 5 dT² + 5 M δB² + EA2`, `EA2 = nW ν dW + nW δν (nW+dW) + dW(ν+δν)(nW+dW)`, `nW = 1 + kDZ + dDZ`.
In the class scaling every term of `E_G` is `O((θ² + θρ + ρ)/n²)`, the scale of the `G⁻¹` coercivity `1/(n²K̂)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace

structure GinvHyp (S E Y P B : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [CompleteSpace P] [CompleteSpace B]
    extends GamHyp S E Y where
  C : E →L[ℝ] P
  Dp : E →L[ℝ] E
  Qb : E →L[ℝ] B
  M : ℝ
  ωP : WPair P
  ωB : WPair B
  δC : ℝ
  κ : ℝ
  δK : ℝ
  ν : ℝ
  δν : ℝ
  δB : ℝ
  hM : 0 ≤ M
  hδC : 0 ≤ δC
  hκ : 0 ≤ κ
  hδK : 0 ≤ δK
  hν : 0 ≤ ν
  hδν : 0 ≤ δν
  hδB : 0 ≤ δB
  hCp : ‖cjp ωE ωP C - C‖ ≤ δC
  hCm : ‖cjm ωE ωP C - C‖ ≤ δC
  hKn : ‖C ∘L D‖ ≤ κ
  hKp : ‖cjp ωS ωP (C ∘L D) - C ∘L D‖ ≤ δK
  hKm : ‖cjm ωS ωP (C ∘L D) - C ∘L D‖ ≤ δK
  hDpn : ‖Dp‖ ≤ ν
  hDpp : ‖cjp ωE ωE Dp - Dp‖ ≤ δν
  hDpm : ‖cjm ωE ωE Dp - Dp‖ ≤ δν
  hDps : ∀ x y, ⟪Dp x, y⟫ = ⟪x, Dp y⟫
  hBp : ‖cjp ωE ωB Qb - Qb‖ ≤ δB
  hBm : ‖cjm ωE ωB Qb - Qb‖ ≤ δB

namespace GinvHyp

variable {S E Y P B : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [CompleteSpace P] [CompleteSpace B]
variable (I : GinvHyp S E Y P B)

noncomputable abbrev Gm : GamHyp S E Y := I.toGamHyp

/-- the (abstract) `G⁻¹` -/
noncomputable def Ginv : E →L[ℝ] E :=
  ContinuousLinearMap.adjoint I.Gm.W ∘L (ContinuousLinearMap.adjoint I.C ∘L I.C + I.Dp) ∘L I.Gm.W
    + ContinuousLinearMap.adjoint I.Gm.T ∘L I.Gm.T + I.M • (ContinuousLinearMap.adjoint I.Qb ∘L I.Qb)

theorem Ginv_form (f : E) : ⟪f, I.Ginv f⟫
    = ‖I.C (I.Gm.W f)‖ ^ 2 + ⟪I.Gm.W f, I.Dp (I.Gm.W f)⟫ + ‖I.Gm.T f‖ ^ 2 + I.M * ‖I.Qb f‖ ^ 2 := by
  simp only [Ginv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    inner_add_right, real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right, inner_add_left,
    real_inner_self_eq_norm_sq]

theorem CW_eq : I.C ∘L I.Gm.W = I.C - (I.C ∘L I.D) ∘L I.Gm.Z := by
  ext v; simp [GamHyp.W, map_sub]

theorem cjp_CW_eq : cjp I.ωE I.ωP (I.C ∘L I.Gm.W) = cjp I.ωE I.ωP I.C - cjp I.ωS I.ωP (I.C ∘L I.D) ∘L cjp I.ωE I.ωS I.Gm.Z := by
  rw [CW_eq, cjp_sub, cjp_comp I.ωE I.ωS I.ωP]

noncomputable def nW : ℝ := 1 + I.Gm.kDZ + I.Gm.dDZ
noncomputable def δCW : ℝ := I.δC + I.δK * I.Gm.kZ + I.κ * I.Gm.dZ

theorem CW_diff (v : E) : ‖cjp I.ωE I.ωP (I.C ∘L I.Gm.W) v - (I.C ∘L I.Gm.W) v‖ ≤ I.δCW * ‖v‖ := by
  rw [cjp_CW_eq, CW_eq]
  obtain ⟨z1, -⟩ := I.Gm.Z_le v
  obtain ⟨z2, -⟩ := I.Gm.Z_diff v
  have e : (cjp I.ωE I.ωP I.C - cjp I.ωS I.ωP (I.C ∘L I.D) ∘L cjp I.ωE I.ωS I.Gm.Z) v - (I.C - (I.C ∘L I.D) ∘L I.Gm.Z) v
      = (cjp I.ωE I.ωP I.C - I.C) v - ((cjp I.ωS I.ωP (I.C ∘L I.D) - I.C ∘L I.D) (cjp I.ωE I.ωS I.Gm.Z v)
          + (I.C ∘L I.D) (cjp I.ωE I.ωS I.Gm.Z v - I.Gm.Z v)) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub]; abel
  rw [e]
  have a1 := SiteHyp.norm_op_le _ _ I.hCp v
  have a2 := (SiteHyp.norm_op_le _ _ I.hKp _).trans (mul_le_mul_of_nonneg_left z1 I.hδK)
  have a3 := (SiteHyp.norm_op_le _ _ I.hKn _).trans (mul_le_mul_of_nonneg_left z2 I.hκ)
  refine (norm_sub_le _ _).trans ?_
  have := norm_add_le ((cjp I.ωS I.ωP (I.C ∘L I.D) - I.C ∘L I.D) (cjp I.ωE I.ωS I.Gm.Z v))
    ((I.C ∘L I.D) (cjp I.ωE I.ωS I.Gm.Z v - I.Gm.Z v))
  calc _ ≤ I.δC * ‖v‖ + (I.δK * (I.Gm.kZ * ‖v‖) + I.κ * (I.Gm.dZ * ‖v‖)) := by linarith
    _ = I.δCW * ‖v‖ := by unfold δCW; ring

/-- the same statements for the inverse weights -/
noncomputable def inv : GinvHyp S E Y P B :=
  { I with
    toGamHyp := { I.toGamHyp with toSiteHyp := I.toSiteHyp.inv }
    ωP := I.ωP.inv, ωB := I.ωB.inv, hCp := I.hCm, hCm := I.hCp, hKp := I.hKm, hKm := I.hKp,
    hDpp := I.hDpm, hDpm := I.hDpp, hBp := I.hBm, hBm := I.hBp }

end GinvHyp

#print axioms GinvHyp.Ginv_form
#print axioms GinvHyp.CW_eq
#print axioms GinvHyp.cjp_CW_eq
#print axioms GinvHyp.CW_diff
#print axioms GinvHyp.inv

end AdalyFormal.DLayer
