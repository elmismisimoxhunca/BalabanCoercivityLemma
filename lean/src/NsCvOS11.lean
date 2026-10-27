import NsCvOS10

/-!
# CvOS11 -- the cleared data reproduce the true base data (lane omega/near2/struct)

For `gOf G U ≠ 0` (and a site outside `Om0`): `Ginv = (g²)⁻¹ • Ah`, `C2 x = ((g²)⁻¹ • Cbh) x x`, hence
`DstructG ≠ 0 ↔ gOf ≠ 0 ∧ BDUnits (baseData ..)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega.Struct

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {L : PeriodicLatticeExtent}

section Main
variable (G : TowerGeom L) (U : Cfg L) (a : ℝ) (S : BondSector G) (Jf : BondFnL2 L)

theorem Ginv_eq (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) (hg : gOf G U ≠ 0) :
    (baseData G U a S Jf).Ginv = ((gOf G U) ^ 2)⁻¹ • AhOf G U a S := by
  have hT := Tfull_eq G U hout hg
  have hW := Wop_eq G U a hout hg
  show (pE G).comp ((DpiFull G U a).comp (iE G))
      + (ContinuousLinearMap.adjoint ((Tfull G U).comp (iE G))).comp ((Tfull G U).comp (iE G))
      + (pE G).comp ((MassFull G a S).comp (iE G)) = _
  rw [hT]
  unfold DpiFull
  rw [hW]
  rw [adj_smul, adj_smul]
  ext1 x
  simp [AhOf, smul_smul, hg]
  have h2 : (gOf G U ^ 2)⁻¹ = (gOf G U)⁻¹ * (gOf G U)⁻¹ := by rw [pow_two, mul_inv]
  rw [h2]

theorem C2_eq (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) (hg : gOf G U ≠ 0) (x : ↥(bondSupp G)) :
    (baseData G U a S Jf).C2 x = (((gOf G U) ^ 2)⁻¹ • CbhOf G U a S) x x := by
  show S.C2full (Wop G U a (iE G x)) = _
  rw [Wop_eq G U a hout hg, ContinuousLinearMap.smul_apply, IsQuadMap.smul_sq S.C2_quad]
  simp only [ContinuousLinearMap.smul_apply, CbhOf_apply, cpolLM_diag]
  rw [inv_pow]

theorem Cb_symm (x y : ↥(bondSupp G)) : (((gOf G U) ^ 2)⁻¹ • CbhOf G U a S) x y = (((gOf G U) ^ 2)⁻¹ • CbhOf G U a S) y x := by
  simp only [ContinuousLinearMap.smul_apply, CbhOf_apply]
  rw [cpolLM_symm]

/-- **the cleared proxy detects exactly `g ≠ 0` and the four units of the genuine base data.** -/
theorem DstructG_ne_iff (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    DstructG G U a S Jf ≠ 0 ↔
      gOf G U ≠ 0 ∧ BDUnits (baseData G U a S Jf) (baseData_laws G U a S Jf) := by
  unfold DstructG
  rw [mul_ne_zero_iff]
  constructor
  · rintro ⟨hg, hD⟩
    refine ⟨hg, ?_⟩
    have hc : ((gOf G U) ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hg)
    exact (core_iff_baseData_scaled (baseData G U a S Jf) (baseData_laws G U a S Jf)
      (((gOf G U) ^ 2)⁻¹ • CbhOf G U a S) (C2_eq G U a S Jf hout hg) (Cb_symm G U a S)
      ((gOf G U) ^ 2)⁻¹ hc (AhOf G U a S) (CbhOf G U a S) (Ginv_eq G U a S Jf hout hg) rfl).mp hD
  · rintro ⟨hg, hU⟩
    refine ⟨hg, ?_⟩
    have hc : ((gOf G U) ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hg)
    exact (core_iff_baseData_scaled (baseData G U a S Jf) (baseData_laws G U a S Jf)
      (((gOf G U) ^ 2)⁻¹ • CbhOf G U a S) (C2_eq G U a S Jf hout hg) (Cb_symm G U a S)
      ((gOf G U) ^ 2)⁻¹ hc (AhOf G U a S) (CbhOf G U a S) (Ginv_eq G U a S Jf hout hg) rfl).mpr hU

end Main

end AdalyFormal.CoverOmega.Struct
