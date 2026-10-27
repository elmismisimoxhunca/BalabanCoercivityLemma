import GN5

/-!
# GN6 -- the genuine operators satisfy SL2's structural hypotheses (whole torus)

* `coarseC G`: `L²` fields on the top-level centres `Λ_k`; `Qtop G U : SiteL2 → coarseC G`, `f ↦ (Q'_k(U) f)|_{Λ_k}`.
* `mem_NQp_of_Qtop` (full tower): `Qtop f = 0 → f ∈ N(Q'(U))`.
* `Rproj_norm_sq`: `‖R s‖² = ⟪s, R s⟫`;  `Rproj_mem_lap` (`Ω₀ = univ`): `R s = D*D ν` for some `ν ∈ N(Q')`.
* `gradAdj_adj`: `⟪x, D s⟫ = ⟪D* x, s⟫`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.StatementLane (scaleUp)

variable {L : PeriodicLatticeExtent}

/-- `L²(Λ_k)`. -/
abbrev coarseC (G : TowerGeom L) : Type := PiLp 2 (fun _ : {y // y ∈ G.Lam G.k} => SuTwo)

open Classical in
noncomputable instance (G : TowerGeom L) : Fintype {y // y ∈ G.Lam G.k} := Subtype.fintype _

/-- top-level constraint map `f ↦ (Q'_k(U) f)|_{Λ_k}`. -/
noncomputable def Qtop (G : TowerGeom L) (U : Cfg L) : SiteL2 L →L[ℝ] coarseC G :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun y => Qlev G U G.k y.1 f)
      map_add' := fun f g => by refine PiLp.ext (fun y => ?_); simp
      map_smul' := fun c f => by refine PiLp.ext (fun y => ?_); simp }

theorem mem_NQp_of_Qtop (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu))
    (f : SiteL2 (scaleUp ell k Lu)) (hf : Qtop (geomOf ell k (fullTower ell k Lu)) U f = 0) :
    f ∈ NQp (geomOf ell k (fullTower ell k Lu)) U := by
  refine ⟨fun x hx => absurd (by rw [fullTower_Om0]; trivial) hx, fun j hj y hy => ?_⟩
  rcases lt_or_eq_of_le hj with hlt | heq
  · rw [fullTower_lam_lt ell k Lu j hlt] at hy; exact absurd hy (Set.notMem_empty y)
  · subst heq
    have := congrArg (fun g : coarseC (geomOf ell j (fullTower ell j Lu)) => g ⟨y, hy⟩) hf
    simp only [Qtop, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk] at this
    exact this

theorem Rproj_norm_sq (G : TowerGeom L) (U : Cfg L) (s : SiteL2 L) :
    ‖Rproj G U s‖ ^ 2 = ⟪s, Rproj G U s⟫ := by
  rw [← real_inner_self_eq_norm_sq, Rproj_symm, Rproj_idem]

theorem Rproj_mem_lap (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (s : SiteL2 L) :
    ∃ ν ∈ NQp G U, Rproj G U s = gradAdj U (gradL2 U ν) := by
  have hR : Rproj G U s ∈ RImage G U := Submodule.starProjection_apply_mem _ _
  obtain ⟨ν, hν, hνR⟩ := Submodule.mem_map.mp hR
  refine ⟨ν, hν, ?_⟩
  rw [← hνR]
  show lapDir G U ν = lapFull U ν
  exact lapDir_univ G hOm U ν

theorem gradAdj_adj (U : Cfg L) (x : BondFnL2 L) (s : SiteL2 L) :
    ⟪x, gradL2 U s⟫ = ⟪gradAdj U x, s⟫ := by
  rw [gradAdj, ContinuousLinearMap.adjoint_inner_left]

#print axioms mem_NQp_of_Qtop
#print axioms Rproj_norm_sq
#print axioms Rproj_mem_lap
#print axioms gradAdj_adj

end AdalyFormal.SliceCoerc
