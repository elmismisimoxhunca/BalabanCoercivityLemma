import DrEquiv
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {L : PeriodicLatticeExtent}

example (f : ℝ → SiteL2 L →L[ℝ] SuTwo) (h : ∀ y, Continuous fun x => f x y) : Continuous f :=
  continuous_clm_apply.mpr h

example (f : ℝ → SiteL2 L →L[ℝ] SuTwo) (h : ∀ y, Continuous fun x => f x y) : Continuous f :=
  (continuous_clm_apply (𝕜 := ℝ) (E := SiteL2 L) (F := SuTwo)).mpr h

example (g : ℝ → SuTwo) (h : Continuous fun x => ((g x : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) : Continuous g :=
  continuous_induced_rng.mpr h

example (g : ℝ → SuTwo) (h : Continuous g) : Continuous fun x => ((g x : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) :=
  continuous_subtype_val.comp h

#synth TopologicalSpace SuTwo
