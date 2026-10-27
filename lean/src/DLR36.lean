import DLR35

/-!
# DL36 -- k-free constant functions via MODEL structures on the zero space

Every derived constant of the abstract chain (`epsX, dT, kZ, dZ, dW, nW, δCW, EG, ...`) depends only on the numeric fields of
the structure.  To state thresholds that are visibly free of `k`, `U`, `φ`, the same structures are instantiated on the
zero-dimensional space `Z0` with all operators `0`; their constants are then functions of the numeric parameters alone:
* `modelSite`, `modelGam`, `modelGinv` and `EGfree c δD δQ q b cG δC κ δK ν δν δB` (with `m = M = 1`);
* `EG_bridge` : the genuine SCALED instance (DL34) has `EG = EGfree` of its numeric parameters (definitional).
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace

/-- the zero-dimensional space -/
abbrev Z0 : Type := EuclideanSpace ℝ (Fin 0)

theorem Z0_eq (x y : Z0) : x = y := by
  ext i; exact Fin.elim0 i

theorem Z0_zero (x : Z0) : x = 0 := Z0_eq x 0

theorem norm_zero_op {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] (ωX : WPair X) (ωY : WPair Y) (δ : ℝ) (hδ : 0 ≤ δ) :
    ‖cjp ωX ωY (0 : X →L[ℝ] Y) - 0‖ ≤ δ := by
  have : cjp ωX ωY (0 : X →L[ℝ] Y) = 0 := by ext x; simp [cjp]
  rw [this, sub_zero, norm_zero]; exact hδ

theorem norm_zero_opm {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] (ωX : WPair X) (ωY : WPair Y) (δ : ℝ) (hδ : 0 ≤ δ) :
    ‖cjm ωX ωY (0 : X →L[ℝ] Y) - 0‖ ≤ δ := by
  have : cjm ωX ωY (0 : X →L[ℝ] Y) = 0 := by ext x; simp [cjm]
  rw [this, sub_zero, norm_zero]; exact hδ

/-- the model site structure -/
noncomputable def modelSite (c δD δQ : ℝ) (hc : 0 < c) (hδD : 0 ≤ δD) (hδQ : 0 ≤ δQ)
    (hsmall : 24 * (δD ^ 2 + 1 * δQ ^ 2) ≤ c) (hsmallD : 4 * δD ^ 2 ≤ c) : SiteHyp Z0 Z0 Z0 where
  D := 0
  Qp := 0
  m := 1
  Linv := 0
  ωS := WPair.one Z0
  ωE := WPair.one Z0
  ωY := WPair.one Z0
  c := c
  δD := δD
  δQ := δQ
  hm := zero_le_one
  hc := hc
  hδD := hδD
  hδQ := hδQ
  hL1 := fun x => Z0_eq _ _
  hL2 := fun x => Z0_eq _ _
  hcoer := fun f => by rw [Z0_zero f]; simp
  hDp := norm_zero_op _ _ _ hδD
  hDm := norm_zero_opm _ _ _ hδD
  hQp := norm_zero_op _ _ _ hδQ
  hQm := norm_zero_opm _ _ _ hδQ
  hsmall := hsmall
  hsmallD := hsmallD

/-- the model `Γ` structure -/
noncomputable def modelGam (c δD δQ : ℝ) (hc : 0 < c) (hδD : 0 ≤ δD) (hδQ : 0 ≤ δQ)
    (hsmall : 24 * (δD ^ 2 + 1 * δQ ^ 2) ≤ c) (hsmallD : 4 * δD ^ 2 ≤ c) (q b cG : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b)
    (hcG : 0 < cG) (hcGdef : cG ≤ 1 / (2 * (q * b) ^ 2) - 3 * (modelSite c δD δQ hc hδD hδQ hsmall hsmallD).epsX q ^ 2) :
    GamHyp Z0 Z0 Z0 where
  toSiteHyp := modelSite c δD δQ hc hδD hδQ hsmall hsmallD
  q := q
  b := b
  Gami := 0
  cG := cG
  hq := hq
  hb := hb
  hQ := by show ‖(0 : Z0 →L[ℝ] Z0)‖ ≤ q; rw [norm_zero]; exact hq
  ext := fun u => ⟨0, Z0_eq _ _, by rw [Z0_zero u]; simp⟩
  hG1 := fun u => Z0_eq _ _
  hG2 := fun u => Z0_eq _ _
  hcG := hcG
  hcGdef := hcGdef

/-- the model `G⁻¹` structure -/
noncomputable def modelGinv (c δD δQ : ℝ) (hc : 0 < c) (hδD : 0 ≤ δD) (hδQ : 0 ≤ δQ)
    (hsmall : 24 * (δD ^ 2 + 1 * δQ ^ 2) ≤ c) (hsmallD : 4 * δD ^ 2 ≤ c) (q b cG : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b)
    (hcG : 0 < cG) (hcGdef : cG ≤ 1 / (2 * (q * b) ^ 2) - 3 * (modelSite c δD δQ hc hδD hδQ hsmall hsmallD).epsX q ^ 2)
    (δC κ δK ν δν δB : ℝ) (hδC : 0 ≤ δC) (hκ : 0 ≤ κ) (hδK : 0 ≤ δK) (hν : 0 ≤ ν) (hδν : 0 ≤ δν) (hδB : 0 ≤ δB) :
    GinvHyp Z0 Z0 Z0 Z0 Z0 where
  toGamHyp := modelGam c δD δQ hc hδD hδQ hsmall hsmallD q b cG hq hb hcG hcGdef
  C := 0
  Dp := 0
  Qb := 0
  M := 1
  ωP := WPair.one Z0
  ωB := WPair.one Z0
  δC := δC
  κ := κ
  δK := δK
  ν := ν
  δν := δν
  δB := δB
  hM := zero_le_one
  hδC := hδC
  hκ := hκ
  hδK := hδK
  hν := hν
  hδν := hδν
  hδB := hδB
  hCp := norm_zero_op _ _ _ hδC
  hCm := norm_zero_opm _ _ _ hδC
  hKn := by rw [ContinuousLinearMap.zero_comp, norm_zero]; exact hκ
  hKp := by rw [ContinuousLinearMap.zero_comp]; exact norm_zero_op _ _ _ hδK
  hKm := by rw [ContinuousLinearMap.zero_comp]; exact norm_zero_opm _ _ _ hδK
  hDpn := by rw [norm_zero]; exact hν
  hDpp := norm_zero_op _ _ _ hδν
  hDpm := norm_zero_opm _ _ _ hδν
  hDps := fun x y => by simp
  hBp := norm_zero_op _ _ _ hδB
  hBm := norm_zero_opm _ _ _ hδB

end AdalyFormal.DLayer
