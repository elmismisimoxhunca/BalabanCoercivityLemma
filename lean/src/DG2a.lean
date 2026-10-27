import DM1
import DC8

/-!
# DG2a -- weights on `E = bondSupp`, and the BILINEAR decomposition of the genuine `Ginv` (M1 D-layer lane, 2026-10-14)

* `pE_iE`, `iE_pE`, `bondWt_mem` : the carrier `E₀` is stable under bond weights; `eW φ = pE ∘ e^{φ} ∘ iE`, `EWP φ` (a DL9
  `WPair` on `E₀`), `rowWP φ` (rows at `rowBase`), `plaqMaskC` (the plaquette mask as a CLM).
* The pieces on `E₀` at `P = gparams … U a Λ`: `Y1 = χ_P C ι`, `Y2 = T ι`, `Y3 = √w Q ι`, `Kz = χ_P C Dm G' T ι`,
  `Wb = W ι`, and `Δg x y = −⟪Y1 x, Kz y⟫ − ⟪Kz x, Y1 y⟫ + ⟪Kz x, Kz y⟫ + Δ'_P(Wb x, Wb y)`.
* **`ginv_bil`** : `⟪x, Ginv y⟫ = ⟪Y1x,Y1y⟫ + ⟪Y2x,Y2y⟫ + ⟪Y3x,Y3y⟫ + Δg x y` (MI18 `ginv_form` is its diagonal).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply plaqMask_symm deltaPrimeBilL2NormLoc deltaKLocCLM inner_deltaKLocCLM)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

section E
variable {L : PeriodicLatticeExtent} (G : TowerGeom L)

theorem pE_iE (z : ↥(bondSupp G)) : pE G (iE G z) = z := by
  refine ext_inner_right ℝ (fun u => ?_)
  rw [pE_inner_left]
  exact (Submodule.coe_inner (bondSupp G) z u).symm

theorem iE_pE (y : BondFnL2 L) (hy : y ∈ bondSupp G) : iE G (pE G y) = y := by
  have e : y = iE G ⟨y, hy⟩ := rfl
  rw [e, pE_iE]

theorem bondWt_mem (φ : PeriodicLatticeSite L → ℝ) (x : ↥(bondSupp G)) : bondWt φ (iE G x) ∈ bondSupp G := by
  intro b hb
  show (bondWt φ (iE G x)) b = 0
  rw [bondWt_apply]
  have : (iE G x) b = 0 := x.2 b hb
  rw [this, smul_zero]

/-- the bond weight on `E₀` -/
noncomputable def eW (φ : PeriodicLatticeSite L → ℝ) : ↥(bondSupp G) →L[ℝ] ↥(bondSupp G) :=
  pE G ∘L bondWt φ ∘L iE G

theorem iE_eW (φ : PeriodicLatticeSite L → ℝ) (x : ↥(bondSupp G)) : iE G (eW G φ x) = bondWt φ (iE G x) := by
  unfold eW
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, iE_pE G _ (bondWt_mem G φ x)]

theorem norm_E (x : ↥(bondSupp G)) : ‖x‖ = ‖iE G x‖ := rfl

theorem inner_E (x y : ↥(bondSupp G)) : ⟪x, y⟫ = ⟪iE G x, iE G y⟫ := Submodule.coe_inner (bondSupp G) x y

/-- the weight pair on `E₀` -/
noncomputable def EWP (φ : PeriodicLatticeSite L → ℝ) : WPair ↥(bondSupp G) where
  w := eW G φ
  wi := eW G (-φ)
  w_wi := fun x => by
    apply Subtype.ext
    show iE G (eW G φ (eW G (-φ) x)) = iE G x
    rw [iE_eW, iE_eW, bondWt_neg_cancel]
  wi_w := fun x => by
    apply Subtype.ext
    show iE G (eW G (-φ) (eW G φ x)) = iE G x
    rw [iE_eW, iE_eW, bondWt_cancel_neg]
  w_sym := fun x y => by rw [inner_E, inner_E, iE_eW, iE_eW, bondWt_symm]
  wi_sym := fun x y => by rw [inner_E, inner_E, iE_eW, iE_eW, bondWt_symm]

theorem rowWt_apply (φ : PeriodicLatticeSite L → ℝ) (f : FSp G) (p : BIdx G) :
    rowWt G φ f p = Real.exp (φ (rowBase G p)) • f p := rfl

theorem rowWt_cancel (φ : PeriodicLatticeSite L → ℝ) (f : FSp G) : rowWt G φ (rowWt G (-φ) f) = f := by
  refine PiLp.ext (fun p => ?_)
  rw [rowWt_apply, rowWt_apply, smul_smul, ← Real.exp_add]
  simp

theorem rowWt_symm (φ : PeriodicLatticeSite L → ℝ) (f g : FSp G) : ⟪rowWt G φ f, g⟫ = ⟪f, rowWt G φ g⟫ :=
  diagW_symm G _ f g

/-- the row weight pair -/
noncomputable def rowWP (φ : PeriodicLatticeSite L → ℝ) : WPair (FSp G) where
  w := rowWt G φ
  wi := rowWt G (-φ)
  w_wi := rowWt_cancel G φ
  wi_w := fun f => by have := rowWt_cancel G (-φ) f; rwa [neg_neg] at this
  w_sym := rowWt_symm G φ
  wi_sym := rowWt_symm G (-φ)

end E

/-- the plaquette mask as a CLM -/
noncomputable def plaqMaskC {L : PeriodicLatticeExtent} (P : Set (PeriodicLatticePlaquette L)) :
    PlaqFnL2 L →L[ℝ] PlaqFnL2 L :=
  LinearMap.toContinuousLinearMap (plaqMask P)

theorem plaqMaskC_apply {L : PeriodicLatticeExtent} (P : Set (PeriodicLatticePlaquette L)) (f : PlaqFnL2 L) :
    plaqMaskC P f = plaqMask P f := rfl

theorem plaqWt_eq_plaqMul {L : PeriodicLatticeExtent} (ξ : PeriodicLatticeSite L → ℝ) (f : PlaqFnL2 L) :
    plaqWt ξ f = plaqMul (fun q => Real.exp (ξ q.1)) f := by
  refine PiLp.ext (fun p => ?_)
  rw [plaqWt_apply, plaqMul_apply]

/-! ## the pieces -/

section pieces
variable {Lf : PeriodicLatticeExtent} (G : TowerGeom Lf) (U : Cfg Lf) (a : ℝ) (Pq : Set (PeriodicLatticePlaquette Lf))

noncomputable def Y1 : ↥(bondSupp G) →L[ℝ] PlaqFnL2 Lf := plaqMaskC Pq ∘L curlC U ∘L iE G
noncomputable def Y2 : ↥(bondSupp G) →L[ℝ] SiteL2 Lf := Tfull G U ∘L iE G
noncomputable def Y3 : ↥(bondSupp G) →L[ℝ] FSp G := Ymass G U a ∘L iE G
noncomputable def Kz : ↥(bondSupp G) →L[ℝ] PlaqFnL2 Lf :=
  plaqMaskC Pq ∘L curlC U ∘L Dm G U ∘L Gp G U a ∘L Tfull G U ∘L iE G
noncomputable def Wb : ↥(bondSupp G) →L[ℝ] BondFnL2 Lf := Wop G U a ∘L iE G

/-- the remainder of the split -/
noncomputable def Δg (x y : ↥(bondSupp G)) : ℝ :=
  -⟪Y1 G U Pq x, Kz G U a Pq y⟫ - ⟪Kz G U a Pq x, Y1 G U Pq y⟫ + ⟪Kz G U a Pq x, Kz G U a Pq y⟫
    + deltaPrimeBilL2NormLoc U Pq (Wb G U a x) (Wb G U a y)

/-- `⟪f, w g⟫ = ⟪√w f, √w g⟫` for diagonal nonnegative row weights -/
theorem inner_diagW_sqrt (w : BIdx G → ℝ) (hw : ∀ p, 0 ≤ w p) (f g : FSp G) :
    ⟪f, diagW G w g⟫ = ⟪diagW G (fun p => Real.sqrt (w p)) f, diagW G (fun p => Real.sqrt (w p)) g⟫ := by
  simp only [PiLp.inner_apply, diagW, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, WithLp.ofLp_toLp]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [inner_smul_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real, ← mul_assoc,
    Real.mul_self_sqrt (hw p)]

end pieces

/-- **the bilinear decomposition of the genuine `Ginv`** -/
theorem ginv_bil {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 ≤ a) (Lam : Set (PeriodicLatticeSite Lu))
    (hu : IsUnit (LP (geomOf ell k S) U a)) (x y : ↥(bondSupp (geomOf ell k S))) :
    ⟪x, (gparams ell k Lu hell0 S U a Lam).data.Ginv y⟫
      = ⟪Y1 (geomOf ell k S) U (plaqIn (S.Om 0)) x, Y1 (geomOf ell k S) U (plaqIn (S.Om 0)) y⟫
        + ⟪Y2 (geomOf ell k S) U x, Y2 (geomOf ell k S) U y⟫
        + ⟪Y3 (geomOf ell k S) U a x, Y3 (geomOf ell k S) U a y⟫
        + Δg (geomOf ell k S) U a (plaqIn (S.Om 0)) x y := by
  have h1 : ⟪x, (gparams ell k Lu hell0 S U a Lam).data.Ginv y⟫
      = ⟪x, (gparams ell k Lu hell0 S U a Lam).data.Dpi y⟫
        + ⟪(gparams ell k Lu hell0 S U a Lam).data.T x, (gparams ell k Lu hell0 S U a Lam).data.T y⟫
        + ⟪x, (gparams ell k Lu hell0 S U a Lam).data.Mass y⟫ := by
    simp only [AdalyFormal.IngredientFamilyR2.BaseDataS.Ginv, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, inner_add_right]
    rw [← (gparams ell k Lu hell0 S U a Lam).data.T_adj]
  have h2 : ⟪x, (gparams ell k Lu hell0 S U a Lam).data.Dpi y⟫
      = ⟪Wop (geomOf ell k S) U a (iE (geomOf ell k S) x), Delta (geomOf ell k S) U (Wop (geomOf ell k S) U a (iE (geomOf ell k S) y))⟫ := by
    show ⟪x, pE (geomOf ell k S) (DpiFull (geomOf ell k S) U a (iE (geomOf ell k S) y))⟫ = _
    rw [pE_inner_right]
    simp only [DpiFull, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  have h3 : ⟪Wop (geomOf ell k S) U a (iE (geomOf ell k S) x), Delta (geomOf ell k S) U (Wop (geomOf ell k S) U a (iE (geomOf ell k S) y))⟫
      = ⟪plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (Wop (geomOf ell k S) U a (iE (geomOf ell k S) x))),
          plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (Wop (geomOf ell k S) U a (iE (geomOf ell k S) y)))⟫
        + deltaPrimeBilL2NormLoc U (plaqIn (S.Om 0)) (Wop (geomOf ell k S) U a (iE (geomOf ell k S) x)) (Wop (geomOf ell k S) U a (iE (geomOf ell k S) y)) := by
    rw [show Delta (geomOf ell k S) U = deltaKLocCLM U (plaqIn (S.Om 0)) from rfl, inner_deltaKLocCLM]
  have h4 : ∀ z : ↥(bondSupp (geomOf ell k S)), plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (Wop (geomOf ell k S) U a (iE (geomOf ell k S) z)))
      = Y1 (geomOf ell k S) U (plaqIn (S.Om 0)) z - Kz (geomOf ell k S) U a (plaqIn (S.Om 0)) z := by
    intro z
    rw [Wop_eq_gen (geomOf ell k S) U a hu, map_sub, map_sub]
    rfl
  have h5 : ⟪x, (gparams ell k Lu hell0 S U a Lam).data.Mass y⟫
      = ⟪Y3 (geomOf ell k S) U a x, Y3 (geomOf ell k S) U a y⟫ := by
    show ⟪x, pE (geomOf ell k S) (MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) U) (iE (geomOf ell k S) y))⟫ = _
    rw [pE_inner_right]
    simp only [MassFull, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    rw [inner_diagW_sqrt (geomOf ell k S) (massW (geomOf ell k S) a) (fun p => by unfold massW; positivity)]
    rfl
  have hT : ∀ z : ↥(bondSupp (geomOf ell k S)), (gparams ell k Lu hell0 S U a Lam).data.T z = Y2 (geomOf ell k S) U z := fun z => rfl
  rw [h1, h2, h3, h4, h4, h5, hT, hT]
  unfold Δg Wb
  simp only [inner_sub_left, inner_sub_right, ContinuousLinearMap.comp_apply]
  ring

#print axioms pE_iE
#print axioms iE_pE
#print axioms bondWt_mem
#print axioms eW
#print axioms iE_eW
#print axioms norm_E
#print axioms inner_E
#print axioms EWP
#print axioms rowWt_apply
#print axioms rowWt_cancel
#print axioms rowWt_symm
#print axioms rowWP
#print axioms plaqMaskC
#print axioms plaqMaskC_apply
#print axioms plaqWt_eq_plaqMul
#print axioms Y1
#print axioms Y2
#print axioms Y3
#print axioms Kz
#print axioms Wb
#print axioms Δg
#print axioms inner_diagW_sqrt
#print axioms ginv_bil

end AdalyFormal.M1DStrat
