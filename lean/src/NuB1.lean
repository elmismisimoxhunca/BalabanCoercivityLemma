import NuK6
import NtCvO44

/-!
# NuB1 -- the reflections `TE`, `TF` of the constant Cartan gauge as continuous linear maps; `τ*` preserves sigma_3 (lane ncwdh_ell2_20261018)
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
open scoped RealInnerProductSpace

section
variable [CfData]
variable {L : PeriodicLatticeExtent}

/-- `Ad_h` on `E₀` as a continuous linear map. -/
noncomputable def TEc (G : TowerGeom L) : ↥(bondSupp G) →L[ℝ] ↥(bondSupp G) :=
  (adEL (hGauge L) G).toContinuousLinearEquiv.toContinuousLinearMap

/-- `Ad_h` on the constraint space as a continuous linear map. -/
noncomputable def TFc (G : TowerGeom L) : FSp G →L[ℝ] FSp G :=
  (adFL (hGauge L) G).toContinuousLinearEquiv.toContinuousLinearMap

theorem TEc_apply (G : TowerGeom L) (x : ↥(bondSupp G)) : TEc G x = adEL (hGauge L) G x := rfl
theorem TFc_apply (G : TowerGeom L) (y : FSp G) : TFc G y = adFL (hGauge L) G y := rfl

theorem TEc_sq (G : TowerGeom L) (x : ↥(bondSupp G)) : TEc G (TEc G x) = x := adEL_hGauge_sq G x

theorem TEc_sym (G : TowerGeom L) (x y : ↥(bondSupp G)) : ⟪TEc G x, y⟫ = ⟪x, TEc G y⟫ := by
  have := (adEL (hGauge L) G).inner_map_map x (TEc G y)
  rw [TEc_apply, adEL_hGauge_sq] at this
  exact this

theorem adFL_hGauge_sq (G : TowerGeom L) (y : FSp G) : adFL (hGauge L) G (adFL (hGauge L) G y) = y := by
  refine PiLp.ext (fun p => ?_)
  rw [adFL_apply, adFL_apply]
  exact RMap_h_sq _

theorem TFc_sq (G : TowerGeom L) (y : FSp G) : TFc G (TFc G y) = y := adFL_hGauge_sq G y

theorem TFc_sym (G : TowerGeom L) (x y : FSp G) : ⟪TFc G x, y⟫ = ⟪x, TFc G y⟫ := by
  have := (adFL (hGauge L) G).inner_map_map x (TFc G y)
  rw [TFc_apply, adFL_hGauge_sq] at this
  exact this

theorem TFc_fixed_iff (G : TowerGeom L) (y : FSp G) : TFc G y = y ↔ ∀ p, diagP (y p) = y p := by
  constructor
  · intro h p
    have := congrArg (fun z : FSp G => z p) h
    simp only [TFc_apply, adFL_apply] at this
    exact (RMap_h_fixed_iff _).mp this
  · intro h
    refine PiLp.ext (fun p => ?_)
    rw [TFc_apply, adFL_apply]
    exact (RMap_h_fixed_iff _).mpr (h p)

theorem TEc_fixed_iff (G : TowerGeom L) (x : ↥(bondSupp G)) : TEc G x = x ↔ SigB (WithLp.ofLp (x : BondFnL2 L)) :=
  adEL_hGauge_fixed_iff G x

/-- `τ` intertwines the constant Cartan gauge. -/
theorem tau_equivariant (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (f : FSp (geomOf ell k S)) :
    tauExt ell k Lu hell S (TFc (geomOf ell k S) f) = adBL (hGauge Lu) (tauExt ell k Lu hell S f) := by
  classical
  refine PiLp.ext (fun e => ?_)
  show (if hb : unitBondEmb ell k Lu hell e ∈ bondsLam (geomOf ell k S) k
      then WithLp.ofLp (TFc (geomOf ell k S) f) ⟨Fin.last k, ⟨unitBondEmb ell k Lu hell e, hb⟩⟩ else 0) =
    RMap (cartan (Real.pi / 2)) (if hb : unitBondEmb ell k Lu hell e ∈ bondsLam (geomOf ell k S) k
      then WithLp.ofLp f ⟨Fin.last k, ⟨unitBondEmb ell k Lu hell e, hb⟩⟩ else 0)
  by_cases hb : unitBondEmb ell k Lu hell e ∈ bondsLam (geomOf ell k S) k
  · rw [dif_pos hb, dif_pos hb]
    rfl
  · rw [dif_neg hb, dif_neg hb, map_zero]


theorem adBL_sym (Lu : PeriodicLatticeExtent) (x y : BondFnL2 Lu) :
    ⟪adBL (hGauge Lu) x, y⟫ = ⟪x, adBL (hGauge Lu) y⟫ := by
  have := (adBL (hGauge Lu)).inner_map_map x (adBL (hGauge Lu) y)
  rw [adBL_hGauge_sq] at this
  exact this

/-- `τ*` of a sigma_3 field is `Ad_h`-fixed. -/
theorem tauStar_fixed (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    {B : BondFnL2 Lu} (hB : SigB (WithLp.ofLp B)) :
    TFc (geomOf ell k S) (ContinuousLinearMap.adjoint (tauExt ell k Lu hell S) B) =
      ContinuousLinearMap.adjoint (tauExt ell k Lu hell S) B := by
  apply ext_inner_left ℝ
  intro f
  rw [← TFc_sym, ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right, tau_equivariant,
    adBL_sym, (adBL_hGauge_fixed_iff B).mpr hB]

end

end AdalyFormal.NcwdhTwo
