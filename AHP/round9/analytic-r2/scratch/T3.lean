import DrEquiv
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped Topology
open Filter

theorem tA (f : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (h : Tendsto f (𝓝 0) (𝓝 (f 0))) :
    Tendsto (fun x => Matrix.trace (f x)) (𝓝 0) (𝓝 (Matrix.trace (f 0))) :=
  ((continuous_id.matrix_trace).tendsto _).comp h

section
open scoped Matrix.Norms.Frobenius
example (f : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (h : ContDiffAt ℝ ⊤ f 0) :
    Tendsto (fun x => Matrix.trace (f x)) (𝓝 0) (𝓝 (Matrix.trace (f 0))) :=
  tA f h.continuousAt.tendsto

example (f : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (h : ContDiffAt ℝ ⊤ f 0) :
    Tendsto (fun t : ℝ => t⁻¹ • (f (0 + t) - f 0)) (𝓝[≠] 0) (𝓝 (deriv f 0)) :=
  (h.differentiableAt (by simp)).hasDerivAt.tendsto_slope_zero

example (g h : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (hg : ContDiffAt ℝ ⊤ g 0) (hh : ContDiffAt ℝ ⊤ h 0) :
    ContDiffAt ℝ ⊤ (fun x => g x * h x) 0 := hg.mul hh

example (g : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (hg : ContDiffAt ℝ ⊤ g 0) :
    ContDiffAt ℝ ⊤ (fun x => (Complex.I) • g x) 0 := hg.const_smul _

example (g : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (hg : ContDiffAt ℝ ⊤ g 0) :
    ContDiffAt ℝ ⊤ (fun x => Matrix.trace (g x)) 0 := by
  have : ContDiffAt ℝ ⊤ (fun X : Matrix (Fin 2) (Fin 2) ℂ => Matrix.trace X) (g 0) :=
    ((Matrix.traceLinearMap (Fin 2) ℝ ℂ).toContinuousLinearMap).contDiff.contDiffAt
  exact this.comp 0 hg
end
