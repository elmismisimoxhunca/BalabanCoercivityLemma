import CvR2
import R2Ops1

/-!
# CvR3 -- L^2 level: `gradL2`, `gradAdj`, `lapFull` on a Cartan-valued configuration (lane cover_jacobi_20261016)

`pwDiagS`, `pwDiagB`: the pointwise `sigma_3` projections on site fields and on bond fields (continuous linear, self-adjoint).
For a Cartan-valued configuration `U` (`CartanCfg U`):
* `gradL2 U o pwDiagS = pwDiagB o gradL2 U` and both equal `gradL2 1 o pwDiagS` (flat);
* `gradAdj U o pwDiagB = pwDiagS o gradAdj U`, and equals `pwDiagS o gradAdj 1`;
* **`pwDiagS o lapFull U = lapFull U o pwDiagS = lapFull 1 o pwDiagS`**: the `sigma_3` block of `Delta_U = D* D` is the FLAT Laplacian.
This is the pilot of the colour-split theorem for the genuine stack; `Delta` (the plaquette form), `Q_j`, `W`, `R`, `T` are NOT covered.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open scoped RealInnerProductSpace
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2

theorem diagP_symm (X Y : SuTwo) : ⟪diagP X, Y⟫ = ⟪X, diagP Y⟫ := by
  rw [AdalyFormal.Balaban.SuTwoInner.inner_eq_trace, AdalyFormal.Balaban.SuTwoInner.inner_eq_trace]
  simp [diagP_coe, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]

variable {L : PeriodicLatticeExtent}

/-- pointwise `sigma_3` projection on any `L^2`-wrapped `su(2)`-valued field over a finite index type. -/
noncomputable def pwDiag (ι : Type) [Fintype ι] : PiLp 2 (fun _ : ι => SuTwo) →L[ℝ] PiLp 2 (fun _ : ι => SuTwo) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun x => diagP (WithLp.ofLp f x))
      map_add' := fun f g => by ext x; simp [map_add]
      map_smul' := fun c f => by ext x; simp [map_smul] }

theorem pwDiag_apply (ι : Type) [Fintype ι] (f : PiLp 2 (fun _ : ι => SuTwo)) (x : ι) : (pwDiag ι f) x = diagP (f x) := rfl

theorem pwDiag_symm (ι : Type) [Fintype ι] (f g : PiLp 2 (fun _ : ι => SuTwo)) : ⟪pwDiag ι f, g⟫ = ⟪f, pwDiag ι g⟫ := by
  simp only [PiLp.inner_apply, pwDiag_apply]
  exact Finset.sum_congr rfl (fun x _ => diagP_symm _ _)

theorem pwDiag_adjoint (ι : Type) [Fintype ι] : ContinuousLinearMap.adjoint (pwDiag ι) = pwDiag ι := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  exact (pwDiag_symm ι f g)

/-- the two projections used below. -/
noncomputable abbrev pwDiagS (L : PeriodicLatticeExtent) : SiteL2 L →L[ℝ] SiteL2 L := pwDiag (PeriodicLatticeSite L)
noncomputable abbrev pwDiagB (L : PeriodicLatticeExtent) : BondFnL2 L →L[ℝ] BondFnL2 L := pwDiag (Bond L)

theorem gradL2_pwDiag {U : Cfg L} (hU : CartanCfg U) (f : SiteL2 L) :
    gradL2 U (pwDiagS L f) = pwDiagB L (gradL2 U f) := by
  refine PiLp.ext (fun b => ?_)
  have h1 : (gradL2 U (pwDiagS L f)) b = gradValueCovariant U (fun x => diagP (WithLp.ofLp f x)) b :=
    congrFun (gradL2_apply U (pwDiagS L f)) b
  have h2 : (gradL2 U f) b = gradValueCovariant U (WithLp.ofLp f) b := congrFun (gradL2_apply U f) b
  rw [pwDiag_apply, h1, h2]
  exact grad_diagP_comm hU _ b

/-- on the `sigma_3` block the covariant gradient is the flat gradient. -/
theorem gradL2_pwDiag_flat {U : Cfg L} (hU : CartanCfg U) (f : SiteL2 L) :
    gradL2 U (pwDiagS L f) = gradL2 (fun _ : Bond L => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) (pwDiagS L f) := by
  refine PiLp.ext (fun b => ?_)
  have h1 : (gradL2 U (pwDiagS L f)) b = gradValueCovariant U (fun x => diagP (WithLp.ofLp f x)) b :=
    congrFun (gradL2_apply U (pwDiagS L f)) b
  have h2 : (gradL2 (fun _ : Bond L => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) (pwDiagS L f)) b =
      gradValueCovariant (fun _ : Bond L => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) (fun x => diagP (WithLp.ofLp f x)) b :=
    congrFun (gradL2_apply _ (pwDiagS L f)) b
  rw [h1, h2]
  exact grad_diagP_flat hU _ b

theorem gradAdj_pwDiag {U : Cfg L} (hU : CartanCfg U) (A : BondFnL2 L) :
    gradAdj U (pwDiagB L A) = pwDiagS L (gradAdj U A) := by
  have hc : (gradL2 U).comp (pwDiagS L) = (pwDiagB L).comp (gradL2 U) := by
    ext1 f; exact gradL2_pwDiag hU f
  have := congrArg ContinuousLinearMap.adjoint hc
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, pwDiag_adjoint, pwDiag_adjoint] at this
  have h := congrArg (fun T => T A) this
  simpa [gradAdj] using h.symm

theorem lapFull_pwDiag {U : Cfg L} (hU : CartanCfg U) (f : SiteL2 L) :
    lapFull U (pwDiagS L f) = pwDiagS L (lapFull U f) := by
  simp only [lapFull, ContinuousLinearMap.comp_apply]
  rw [gradL2_pwDiag hU, gradAdj_pwDiag hU]

theorem pwDiag_idem (ι : Type) [Fintype ι] (f : PiLp 2 (fun _ : ι => SuTwo)) : pwDiag ι (pwDiag ι f) = pwDiag ι f := by
  refine PiLp.ext (fun x => ?_)
  show diagP (diagP (f x)) = diagP (f x)
  exact diagP_idem _

theorem pwDiagS_gradAdj_flat {U : Cfg L} (hU : CartanCfg U) (A : BondFnL2 L) :
    pwDiagS L (gradAdj U A) = pwDiagS L (gradAdj (fun _ : Bond L => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) A) := by
  have hc : (gradL2 U).comp (pwDiagS L) = (gradL2 (fun _ : Bond L => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))).comp (pwDiagS L) := by
    ext1 f; exact gradL2_pwDiag_flat hU f
  have := congrArg ContinuousLinearMap.adjoint hc
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, pwDiag_adjoint] at this
  have h := congrArg (fun T => T A) this
  simpa [gradAdj] using h

/-- **the `sigma_3` block of `Delta_U = D* D` on a Cartan configuration is the flat Laplacian.** -/
theorem lapFull_pwDiag_flat {U : Cfg L} (hU : CartanCfg U) (f : SiteL2 L) :
    lapFull U (pwDiagS L f) = lapFull (fun _ : Bond L => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) (pwDiagS L f) := by
  have h1 := cartanCfg_one (L := L)
  simp only [lapFull, ContinuousLinearMap.comp_apply]
  rw [gradL2_pwDiag_flat hU f]
  have hX : gradL2 (fun _ : Bond L => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) (pwDiagS L f) =
      pwDiagB L (gradL2 (fun _ : Bond L => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) (pwDiagS L f)) := by
    rw [← gradL2_pwDiag h1, pwDiag_idem]
  rw [hX, gradAdj_pwDiag hU, gradAdj_pwDiag h1, pwDiagS_gradAdj_flat hU]


#print axioms diagP_symm
#print axioms pwDiag
#print axioms pwDiag_apply
#print axioms pwDiag_symm
#print axioms pwDiag_adjoint
#print axioms pwDiagS
#print axioms pwDiagB
#print axioms gradL2_pwDiag
#print axioms gradL2_pwDiag_flat
#print axioms gradAdj_pwDiag
#print axioms lapFull_pwDiag
#print axioms pwDiag_idem
#print axioms pwDiagS_gradAdj_flat
#print axioms lapFull_pwDiag_flat

end AdalyFormal.CoverJacobi
