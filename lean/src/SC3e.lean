import SC3d

/-!
# SC3e -- the abstract cell theorems (trivial and non-trivial twist) with explicit constants.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped ComplexInnerProductSpace
open AdalyFormal.FlatCoercivity
open Finset

namespace AdalyFormal.ScaledCoercivity

/-- the `N`-coercivity constant -/
noncomputable def lamN (κ G A q0 : ℝ) : ℝ := min (κ * q0 ^ 2 / 4) (G * q0 ^ 2 / (4 * A ^ 2 + q0 ^ 2))

/-- the margin constant -/
noncomputable def mu0c (κ G2 S2 : ℝ) : ℝ := κ * G2 / (1 + κ * S2)

section Main
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {sd : SymData V}

/-- trivial twist -/
theorem cell_abstract_trivial (md : ModeData sd) (κ A q0 : ℝ) (hκ : 0 ≤ κ) (hA : 0 < A) (hq0 : 0 ≤ q0)
    (hq : ∀ μ, q0 ≤ ‖sd.Qm μ md.e0‖) (hAq : ∀ μ x, ‖sd.Qm μ x‖ ≤ A * ‖x‖)
    (hall : ∀ μ, sd.ph μ = 1) (w : Fin 3 → V) (S : ℝ) (hS0 : 0 ≤ S)
    (hS : ∀ u, ⟪sd.eps, u⟫ = 0 → ‖⟪sd.Dstar w, sd.Lap u⟫‖ ^ 2 ≤ S * ‖sd.Lap u‖ ^ 2) :
    lamN κ md.G A q0 * ∑ μ, ‖w μ‖ ^ 2 ≤ g1b sd w + κ * g2b sd w + S := by
  have h1 := S_ge_trivial sd hall w S hS0 hS
  have h2 := weitz_b sd w
  have h3 := N_coercive md κ A q0 hκ hA hq0 hq hAq w
  unfold lamN
  linarith

end Main

end AdalyFormal.ScaledCoercivity
