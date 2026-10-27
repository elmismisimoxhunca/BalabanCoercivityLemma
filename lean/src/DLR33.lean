import DLR32

/-!
# DL33 -- SCALED instances: the identities for `D' = s D_U`, `Q'_p = t Qtop`, `G'' = s⁻² G'` (k-uniformity device)

Running the abstract chain on the RESCALED genuine operators (`s = n = ℓ^k`) makes every input constant k-free (the
natural sizes `c ~ n⁻²`, `δD ~ θ/n`, `‖Qtop‖ ~ n^{-3/2}`, ... become `O(1)`), so every derived constant of DL10–DL20 is
k-free by construction (no symbolic homogeneity proof needed).  This module proves that the rescaling does not change
the objects:
* `Tfull_eq_T_scaled` : `G0.T = s • Tfull`;  `Wop_eq_W_scaled` : `G0.W = Wop`  (for any `GamHyp G0` with `G0.D = s•D_U`,
  `G0.Qp = t•Qtop`, `G0.Linv = s⁻²•Gp`, `s, t ≠ 0`), via `Rproj_eq` with `Γ⁻¹ := (t²/s⁴)•G0.Gami`.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)

section
variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

theorem adjoint_smul_real (c : ℝ) (A : X →L[ℝ] Y) :
    ContinuousLinearMap.adjoint (c • A) = c • ContinuousLinearMap.adjoint A := by
  ext1 y
  refine ext_inner_left ℝ (fun x => ?_)
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    real_inner_smul_left, real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
end

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
  (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)))
  (G0 : GamHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu)))
  (s t : ℝ) (hs : s ≠ 0) (ht : t ≠ 0)
  (hD : G0.D = s • gradL2 U) (hQ : G0.Qp = t • Qtop (GF ell k Lu) U)
  (hL : G0.Linv = s⁻¹ ^ 2 • Gp (GF ell k Lu) U a)
include hu hs ht hD hQ hL

theorem X_scaled : G0.H.X = (t / s ^ 2) • (Gp (GF ell k Lu) U a ∘L ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U)) := by
  ext1 u
  simp only [SiteHyp.X, hL, hQ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    adjoint_smul_real, map_smul, smul_smul]
  congr 1; field_simp

theorem Rproj_eq_scaled (v : SiteL2 (scaleUp ell k Lu)) :
    Rproj (GF ell k Lu) U v
      = v - (Gp (GF ell k Lu) U a ∘L ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U))
          (((t ^ 2 / s ^ 4) • G0.Gami)
            (ContinuousLinearMap.adjoint (Gp (GF ell k Lu) U a ∘L ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U)) v)) := by
  refine Rproj_eq ell k Lu U a hu _ (fun u => ?_) v
  have h1 := G0.hG1 u
  have hX := X_scaled ell k Lu U a hu G0 s t hs ht hD hQ hL
  have hX' : G0.Linv ∘L ContinuousLinearMap.adjoint G0.Qp
      = (t / s ^ 2) • (Gp (GF ell k Lu) U a ∘L ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U)) := hX
  have e : (ContinuousLinearMap.adjoint (G0.Linv ∘L ContinuousLinearMap.adjoint G0.Qp)
      ∘L (G0.Linv ∘L ContinuousLinearMap.adjoint G0.Qp)) (G0.Gami u)
      = (t ^ 2 / s ^ 4) • (ContinuousLinearMap.adjoint (Gp (GF ell k Lu) U a ∘L ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U))
          ∘L (Gp (GF ell k Lu) U a ∘L ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U))) (G0.Gami u) := by
    rw [hX', adjoint_smul_real]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul]
    congr 1; field_simp
  rw [e] at h1
  rw [ContinuousLinearMap.smul_apply, map_smul]
  exact h1

theorem Tfull_eq_T_scaled : G0.T = s • Tfull (GF ell k Lu) U := by
  ext1 A
  have hR := Rproj_eq_scaled ell k Lu U a hu G0 s t hs ht hD hQ hL (gradAdj U A)
  have hX := X_scaled ell k Lu U a hu G0 s t hs ht hD hQ hL
  set X := Gp (GF ell k Lu) U a ∘L ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U) with hXdef
  set DA := ContinuousLinearMap.adjoint (gradL2 U) A with hDA
  have h1 : ContinuousLinearMap.adjoint G0.D A = s • DA := by
    rw [hD, adjoint_smul_real, ContinuousLinearMap.smul_apply]
  have h2 : ContinuousLinearMap.adjoint G0.F A = (t / s) • ContinuousLinearMap.adjoint X DA := by
    show ContinuousLinearMap.adjoint (G0.D ∘L G0.H.X) A = _
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply, h1, hX, adjoint_smul_real,
      ContinuousLinearMap.smul_apply, map_smul, smul_smul]
    congr 1; field_simp
  have h3 : G0.T A = s • DA - (t / s ^ 2) • X (G0.Gami ((t / s) • ContinuousLinearMap.adjoint X DA)) := by
    show ContinuousLinearMap.adjoint G0.D A - G0.H.X (G0.Gami (ContinuousLinearMap.adjoint G0.F A)) = _
    rw [h1, h2, hX, ContinuousLinearMap.smul_apply]
  have e1 : gradAdj U A = DA := rfl
  rw [e1] at hR
  have hTA : (s • Tfull (GF ell k Lu) U) A = s • Rproj (GF ell k Lu) U DA := rfl
  rw [h3, hTA, hR]
  simp only [ContinuousLinearMap.smul_apply, map_smul, smul_sub, smul_smul]
  congr 2
  field_simp

theorem Wop_eq_W_scaled : G0.W = Wop (GF ell k Lu) U a := by
  have hT := Tfull_eq_T_scaled ell k Lu U a hu G0 s t hs ht hD hQ hL
  ext1 A
  have e1 : G0.W A = A - G0.D (G0.Linv (G0.T A)) := rfl
  have e2 : Wop (GF ell k Lu) U a A = A - gradL2 U (Gp (GF ell k Lu) U a (Tfull (GF ell k Lu) U A)) := rfl
  rw [e1, e2, hT, hD, hL]
  simp only [ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  have hc : s * s⁻¹ ^ 2 * s = 1 := by field_simp
  rw [hc, one_smul]

end

#print axioms X_scaled
#print axioms Rproj_eq_scaled
#print axioms Tfull_eq_T_scaled
#print axioms Wop_eq_W_scaled

end AdalyFormal.DLayer
