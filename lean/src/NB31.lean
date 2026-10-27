import CB2
/-!
# NB31 -- bridge: the fine plaquette hypothesis `∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0` is equivalent to a bound on
the tree's `periodicPlaquetteHolonomy` over all plaquettes (both orientations via inverse; `ν = μ` trivial).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2)

variable {L : PeriodicLatticeExtent}

theorem pw_one_of_plaq (U : PeriodicLinkConfiguration SU2 L) (q0 : ℝ) (hq0 : 0 ≤ q0)
    (h : ∀ p : PeriodicLatticePlaquette L, dv (periodicPlaquetteHolonomy U p) ≤ q0) :
    ∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0 := by
  intro y ν μ
  rcases lt_trichotomy ν μ with hlt | heq | hgt
  · have e : pw 1 U y ν μ = periodicPlaquetteHolonomy U (y, ⟨(ν, μ), hlt⟩) := rfl
    rw [e]; exact h _
  · subst heq
    have e : pw 1 U y ν ν = 1 := by unfold pw; group
    rw [e, dv_one]; exact hq0
  · have e : pw 1 U y ν μ = (periodicPlaquetteHolonomy U (y, ⟨(μ, ν), hgt⟩))⁻¹ := by
      show _ = (U (y, μ) * U (periodicLatticeShift y μ, ν) * (U (periodicLatticeShift y ν, μ))⁻¹
        * (U (y, ν))⁻¹)⁻¹
      unfold pw
      show U (y, ν) * U (periodicLatticeShift y ν, μ) * (U (periodicLatticeShift y μ, ν))⁻¹
        * (U (y, μ))⁻¹ = _
      group
    rw [e, dv_inv]; exact h _

theorem plaq_of_pw_one (U : PeriodicLinkConfiguration SU2 L) (q0 : ℝ)
    (h : ∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0) :
    ∀ p : PeriodicLatticePlaquette L, dv (periodicPlaquetteHolonomy U p) ≤ q0 := by
  intro p
  exact h p.1 p.2.1.1 p.2.1.2

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.pw_one_of_plaq
#print axioms AdalyFormal.CurvBlock.plaq_of_pw_one
