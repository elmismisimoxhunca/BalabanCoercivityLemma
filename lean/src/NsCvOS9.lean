import NsCvOS8
import ZXR2Ops4

/-!
# CvOS9 -- `Rproj` as a cleared formula, and the cleared base data (lane omega/near2/struct)

`gOf = det (C m C*)`, `RhOf = Rhat`, `Rproj = g⁻¹ • RhOf` when `g ≠ 0`.
Cleared data: `WhOf = g • 1 - D G' Rh D*`, `AhOf = pE (Wh* Δ Wh) iE + Th* Th + g² Mass`, `CbhOf x y = Cpol (Wh x) (Wh y)`.
`DstructG = g * Dcore AhOf Q CbhOf J`;  `DstructG ≠ 0 ↔ g ≠ 0 ∧ BDUnits (baseData ..)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega.Struct

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

/-- row index set of the constraints `Q'_j λ(y) = 0, y ∈ Λ_j`. -/
def RowIdx {L : PeriodicLatticeExtent} (G : TowerGeom L) : Type :=
  {p : Fin (G.k + 1) × PeriodicLatticeSite L // p.2 ∈ G.Lam (p.1 : ℕ)}

noncomputable instance rowIdxFintype {L : PeriodicLatticeExtent} (G : TowerGeom L) : Fintype (RowIdx G) := by
  classical
  unfold RowIdx
  infer_instance

abbrev WQ {L : PeriodicLatticeExtent} (G : TowerGeom L) : Type := PiLp 2 (fun _ : RowIdx G => SuTwo)

variable {L : PeriodicLatticeExtent}

/-- the constraint operator `λ ↦ (Q'_j(U)λ(y))_{j, y ∈ Λ_j}`. -/
noncomputable def Bq (G : TowerGeom L) (U : Cfg L) : SiteL2 L →L[ℝ] WQ G :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun p : RowIdx G => Qlev G U (p.1.1 : ℕ) p.1.2 f)
      map_add' := fun f g => by ext p; simp
      map_smul' := fun c f => by ext p; simp }

theorem Bq_apply (G : TowerGeom L) (U : Cfg L) (f : SiteL2 L) (p : RowIdx G) :
    Bq G U f p = Qlev G U (p.1.1 : ℕ) p.1.2 f := rfl

theorem NQp_eq (G : TowerGeom L) (U : Cfg L) : NQp G U = Nsub (siteMask G.Om0) (Bq G U) := by
  ext f
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · ext x
      rw [siteMask_apply]
      by_cases hx : x ∈ G.Om0
      · rw [if_pos hx]
      · rw [if_neg hx, h1 x hx]
    · refine PiLp.ext (fun p => ?_)
      exact h2 (p.1.1 : ℕ) (by have := p.1.1.2; omega) p.1.2 p.2
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun j hj y hy => ?_⟩
    · have := congrFun (congrArg WithLp.ofLp h1) x
      rw [siteMask_apply, if_neg hx] at this
      exact this.symm
    · have := congrFun (congrArg WithLp.ofLp h2) ⟨(⟨j, by omega⟩, y), hy⟩
      exact this

/-- `Gm` for the genuine geometry. -/
noncomputable def GmOf (G : TowerGeom L) (U : Cfg L) : WQ G →L[ℝ] WQ G :=
  Gm (siteMask G.Om0) (LmOf G U) (Bq G U)

noncomputable def gOf (G : TowerGeom L) (U : Cfg L) : ℝ := cdet (GmOf G U)

noncomputable def RhOf (G : TowerGeom L) (U : Cfg L) : SiteL2 L →L[ℝ] SiteL2 L :=
  Rhat (siteMask G.Om0) (LmOf G U) (Bq G U)

theorem Rproj_eq (G : TowerGeom L) (U : Cfg L) (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0)
    (hg : gOf G U ≠ 0) : Rproj G U = (gOf G U)⁻¹ • RhOf G U := by
  have hms := siteMask_symm (L := L) G.Om0
  have hmi := siteMask_idem (L := L) G.Om0
  have hLd : ∀ f, LmOf G U f = lapDir G U f + (f - siteMask G.Om0 f) := fun f => by
    simp [LmOf]
  have hl1 : ∀ f, siteMask G.Om0 (lapDir G U f) = lapDir G U f := fun f => by
    unfold lapDir
    simp only [ContinuousLinearMap.comp_apply]
    exact hmi _
  have hl2 : ∀ f, lapDir G U (siteMask G.Om0 f) = lapDir G U f := fun f => by
    unfold lapDir
    simp only [ContinuousLinearMap.comp_apply]
    rw [hmi]
  have key : ∀ (K : Submodule ℝ (SiteL2 L)) [K.HasOrthogonalProjection],
      K = Submodule.map (lapDir G U : SiteL2 L →ₗ[ℝ] SiteL2 L) (Nsub (siteMask G.Om0) (Bq G U)) →
      K.starProjection = (gOf G U)⁻¹ • RhOf G U := by
    intro K _ hK
    subst hK
    exact starProjection_eq_Rhat (siteMask G.Om0) (lapDir G U) (LmOf G U) (Bq G U) hms hmi (LmOf_unit G U hout) hLd hl1 hl2 hg
  exact key (RImage G U) (by unfold RImage; rw [NQp_eq])

end AdalyFormal.CoverOmega.Struct
