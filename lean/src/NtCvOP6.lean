import NtCvOP6a
import NtCvOP5

/-!
# CvOP6 -- entrywise analyticity calculus for `M₂(ℂ)`-valued families and the `SuTwo` conversions; `RMap` (lane omega/near2/struct)

No Frobenius scope here: the `SuTwo`/`BondFnL2` instances of the tree are the only normed structures in play.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo RMap RMap_coe_apply)

section EAcalc
variable {t0 : ℝ}

theorem EA.const (c : M2) : EA (fun _ => c) t0 := fun _ _ => analyticAt_const

theorem EA.add {f g : ℝ → M2} (hf : EA f t0) (hg : EA g t0) : EA (fun t => f t + g t) t0 :=
  fun i j => (hf i j).add (hg i j)

theorem EA.sub {f g : ℝ → M2} (hf : EA f t0) (hg : EA g t0) : EA (fun t => f t - g t) t0 :=
  fun i j => (hf i j).sub (hg i j)

theorem EA.neg {f : ℝ → M2} (hf : EA f t0) : EA (fun t => - f t) t0 :=
  fun i j => (hf i j).neg

theorem EA.mul {f g : ℝ → M2} (hf : EA f t0) (hg : EA g t0) : EA (fun t => f t * g t) t0 := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hf i 0).mul (hg 0 j)).add ((hf i 1).mul (hg 1 j))

theorem EA.smul_real {a : ℝ → ℝ} {f : ℝ → M2} (ha : AnalyticAt ℝ a t0) (hf : EA f t0) :
    EA (fun t => a t • f t) t0 := by
  intro i j
  simp only [Matrix.smul_apply]
  exact ha.smul (hf i j)

theorem EA.smul_const (c : ℂ) {f : ℝ → M2} (hf : EA f t0) : EA (fun t => c • f t) t0 := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact analyticAt_const.mul (hf i j)

theorem EA.conjTranspose {f : ℝ → M2} (hf : EA f t0) : EA (fun t => (f t)ᴴ) t0 := by
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact (Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp (hf j i)

theorem EA.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → M2} (h : ∀ i ∈ s, EA (f i) t0) :
    EA (fun t => ∑ i ∈ s, f i t) t0 := by
  intro i j
  simp only [Matrix.sum_apply]
  exact Finset.analyticAt_fun_sum _ (fun k hk => h k hk i j)

theorem EA.trace {f : ℝ → M2} (hf : EA f t0) : AnalyticAt ℝ (fun t => Matrix.trace (f t)) t0 := by
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  exact (hf 0 0).add (hf 1 1)

theorem EA.trace_re {f : ℝ → M2} (hf : EA f t0) : AnalyticAt ℝ (fun t => (Matrix.trace (f t)).re) t0 :=
  (Complex.reCLM.analyticAt _).comp hf.trace

theorem EA.trace_im {f : ℝ → M2} (hf : EA f t0) : AnalyticAt ℝ (fun t => (Matrix.trace (f t)).im) t0 :=
  (Complex.imCLM.analyticAt _).comp hf.trace

end EAcalc

section SuTwoConv
variable {t0 : ℝ}

/-- entry functional on `SuTwo`. -/
noncomputable def entSu (i j : Fin 2) : SuTwo →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (X : M2) i j
      map_add' := fun X Y => by simp
      map_smul' := fun c X => by simp }

theorem EA_of_suTwo {h : ℝ → SuTwo} (ha : AnalyticAt ℝ h t0) : EA (fun t => ((h t : SuTwo) : M2)) t0 :=
  fun i j => (((entSu i j).analyticAt _).comp ha :)

/-- a left inverse of the entry embedding, as a continuous linear map. -/
theorem exists_entInv : ∃ g : (Fin 2 → Fin 2 → ℂ) →L[ℝ] SuTwo, ∀ X : SuTwo, g (fun i j => (X : M2) i j) = X := by
  let E : SuTwo →ₗ[ℝ] (Fin 2 → Fin 2 → ℂ) :=
    { toFun := fun X i j => (X : M2) i j
      map_add' := fun X Y => by ext i j; simp
      map_smul' := fun c X => by ext i j; simp }
  have hinj : Function.Injective E := by
    intro X Y h
    apply Subtype.ext
    ext i j
    exact congrFun (congrFun h i) j
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective E (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toContinuousLinearMap g, fun X => ?_⟩
  have := congrArg (fun T : SuTwo →ₗ[ℝ] SuTwo => T X) hg
  exact this

theorem analyticAt_suTwo {h : ℝ → SuTwo} (hc : EA (fun t => ((h t : SuTwo) : M2)) t0) : AnalyticAt ℝ h t0 := by
  obtain ⟨g, hg⟩ := exists_entInv
  have h1 : AnalyticAt ℝ (fun t => (fun i j => (((h t : SuTwo) : M2)) i j)) t0 :=
    analyticAt_pi_iff.2 (fun i => analyticAt_pi_iff.2 (fun j => hc i j))
  have h2 := (g.analyticAt _).comp h1
  have : h = fun t => g (fun i j => (((h t : SuTwo) : M2)) i j) := by funext t; rw [hg]
  rw [this]; exact h2

/-- `R(W) X = W X Wᴴ`: analytic in `(W, X)`. -/
theorem RMap_analytic {W : ℝ → SU2} {X : ℝ → SuTwo} (hW : EA (fun t => ((W t : SU2) : M2)) t0)
    (hX : AnalyticAt ℝ X t0) : AnalyticAt ℝ (fun t => RMap (W t) (X t)) t0 := by
  apply analyticAt_suTwo
  have h : (fun t => ((RMap (W t) (X t) : SuTwo) : M2))
      = fun t => ((W t : SU2) : M2) * ((X t : SuTwo) : M2) * ((W t : SU2) : M2)ᴴ := by
    funext t; exact RMap_coe_apply (W t) (X t)
  rw [h]
  exact (hW.mul (EA_of_suTwo hX)).mul hW.conjTranspose

end SuTwoConv

end AdalyFormal.CoverOmega.Struct
