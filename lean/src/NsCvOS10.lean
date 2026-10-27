import NsCvOS9

/-!
# CvOS10 -- cleared base data and `DstructG` for a general geometry (lane omega/near2/struct)

`DstructG G U a S Jf = gOf G U * Dcore (AhOf ..) (S.Qfull ∘ iE) (CbhOf ..) (pE Jf)` and
`DstructG ≠ 0 ↔ gOf ≠ 0 ∧ BDUnits (baseData G U a S Jf) _`   (needs a site outside `Om0`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega.Struct

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {L : PeriodicLatticeExtent}

section Cleared
variable (G : TowerGeom L) (U : Cfg L) (a : ℝ)

/-- `Wh = g • 1 - D G' Rh D*` (`= g • Wop`). -/
noncomputable def WhOf : BondFnL2 L →L[ℝ] BondFnL2 L :=
  gOf G U • (1 : BondFnL2 L →L[ℝ] BondFnL2 L) -
    (gradL2 U).comp ((Gp G U a).comp ((RhOf G U).comp (gradAdj U)))

theorem Wop_eq (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) (hg : gOf G U ≠ 0) :
    Wop G U a = (gOf G U)⁻¹ • WhOf G U a := by
  unfold Wop WhOf
  rw [Rproj_eq G U hout hg]
  ext1 A
  simp [smul_sub, smul_smul, hg]

/-- `Th = Rh D* ι` (`= g • T`). -/
noncomputable def ThOf : ↥(bondSupp G) →L[ℝ] SiteL2 L := (RhOf G U).comp ((gradAdj U).comp (iE G))

theorem Tfull_eq (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) (hg : gOf G U ≠ 0) :
    (Tfull G U).comp (iE G) = (gOf G U)⁻¹ • ThOf G U := by
  unfold Tfull ThOf
  rw [Rproj_eq G U hout hg]
  ext1 A
  simp

variable (S : BondSector G)

/-- `Ah = pE (Wh* Δ Wh) ι + Th* Th + g² Mass` (`= g² Ginv`). -/
noncomputable def AhOf : ↥(bondSupp G) →L[ℝ] ↥(bondSupp G) :=
  (pE G).comp (((ContinuousLinearMap.adjoint (WhOf G U a)).comp ((Delta G U).comp (WhOf G U a))).comp (iE G))
    + (ContinuousLinearMap.adjoint (ThOf G U)).comp (ThOf G U)
    + (gOf G U ^ 2) • ((pE G).comp ((MassFull G a S).comp (iE G)))

/-- the symmetric bilinear map of the quadratic `C2full`. -/
noncomputable def cpolLM : BondFnL2 L →ₗ[ℝ] BondFnL2 L →ₗ[ℝ] FSp G :=
  (1 / 2 : ℝ) • (S.C2_quad.choose + S.C2_quad.choose.flip)

theorem cpolLM_symm (x y : BondFnL2 L) : cpolLM G S x y = cpolLM G S y x := by
  simp only [cpolLM, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply]
  rw [add_comm]

theorem cpolLM_diag (x : BondFnL2 L) : cpolLM G S x x = S.C2full x := by
  have h := S.C2_quad.choose_spec x
  simp only [cpolLM, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply]
  rw [h, ← two_smul ℝ, smul_smul]; norm_num

noncomputable def cpolCLM : BondFnL2 L →L[ℝ] BondFnL2 L →L[ℝ] FSp G :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => LinearMap.toContinuousLinearMap (cpolLM G S x)
      map_add' := fun x y => by ext z; simp
      map_smul' := fun c x => by ext z; simp }

theorem cpolCLM_apply (x y : BondFnL2 L) : cpolCLM G S x y = cpolLM G S x y := rfl

/-- `Cbh x y = Cpol (Wh x) (Wh y)` on `E₀` (`= g² Cb`). -/
noncomputable def CbhOf : ↥(bondSupp G) →L[ℝ] ↥(bondSupp G) →L[ℝ] FSp G :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => LinearMap.toContinuousLinearMap
        ((cpolLM G S (WhOf G U a (iE G x))).comp ((WhOf G U a).comp (iE G) : ↥(bondSupp G) →ₗ[ℝ] BondFnL2 L))
      map_add' := fun x y => by ext z; simp
      map_smul' := fun c x => by ext z; simp }

theorem CbhOf_apply (x y : ↥(bondSupp G)) :
    CbhOf G U a S x y = cpolLM G S (WhOf G U a (iE G x)) (WhOf G U a (iE G y)) := rfl

/-- THE STRUCTURAL PROXY for a general geometry. -/
noncomputable def DstructG (Jf : BondFnL2 L) : ℝ :=
  gOf G U * Dcore (AhOf G U a S) (S.Qfull.comp (iE G)) (CbhOf G U a S) (pE G Jf)

end Cleared

end AdalyFormal.CoverOmega.Struct
