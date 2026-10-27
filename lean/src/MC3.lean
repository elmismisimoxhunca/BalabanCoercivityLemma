import MC2
import CB9
import NB31

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

/-!
# MC3 -- clauses 1 and 2 of the printed class give the M0 regime (links, plaquettes); clause 3 is NOT used.
-/
namespace AdalyFormal.M0Corollary

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLaneG AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.CurvBlock

/-- clauses 1 and 2 only (clause 3, the `ddA` bound, dropped) -/
def GlobalRegular12 {L : PeriodicLatticeExtent} (ell M f k : ℕ) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ e : Bond L, HT (A e) ∧
        ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
          = NormedSpace.exp (((η : ℂ) * Complex.I) • A e) ∧
        frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ k * η)⁻¹ ^ 1)) ∧
    (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L),
        frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ k * η)⁻¹ ^ 2))

theorem GlobalRegular2.toRegular12 {L : PeriodicLatticeExtent} {ell M f k : ℕ} {α₀ η : ℝ} {U : LinkCfg L}
    (h : GlobalRegular2 ell M f k α₀ η U) : GlobalRegular12 ell M f k α₀ η U := by
  obtain ⟨g, A, h1, h2, -⟩ := h
  exact ⟨g, A, h1, h2⟩

/-- **the M0 regime from the printed class (clauses 1, 2), in the class gauge `g`**, with the class scaling `η = ell⁻ᵏ`:
fine links `dv ≤ α/ellᵏ`, fine plaquettes `dv ≤ (2α + (4π+2)α²)/ell²ᵏ`, `α = f M α₀`. -/
theorem regime_of_regular12 {ell M f k : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent} {α₀ : ℝ}
    {U : LinkCfg (scaleUp ell k Lu)} (h : GlobalRegular12 ell M f k α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hα0 : 0 ≤ (f : ℝ) * M * α₀) (hα : (f : ℝ) * M * α₀ ≤ 1) :
    ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ,
      (∀ b, dv (periodicGaugeTransform g U b) ≤ (f : ℝ) * M * α₀ / (ell : ℝ) ^ k) ∧
      (∀ p : PeriodicLatticePlaquette (scaleUp ell k Lu),
        dv (periodicPlaquetteHolonomy (periodicGaugeTransform g U) p)
          ≤ (2 * ((f : ℝ) * M * α₀) + (4 * Real.pi + 2) * ((f : ℝ) * M * α₀) ^ 2) / ((ell : ℝ) ^ k) ^ 2) := by
  obtain ⟨g, A, h1, h2⟩ := h
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  have hn1 : (1 : ℝ) ≤ (ell : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hell)
  have hη0 : 0 < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hnη : (ell : ℝ) ^ k * ((ell : ℝ) ^ k)⁻¹ = 1 := mul_inv_cancel₀ hn.ne'
  have hc1 : (f : ℝ) * M * α₀ * (((ell : ℝ) ^ k * ((ell : ℝ) ^ k)⁻¹)⁻¹ ^ 1) = (f : ℝ) * M * α₀ := by rw [hnη]; simp
  have hc2 : (f : ℝ) * M * α₀ * (((ell : ℝ) ^ k * ((ell : ℝ) ^ k)⁻¹)⁻¹ ^ 2) = (f : ℝ) * M * α₀ := by rw [hnη]; simp
  let K : CubeChart U (fun _ => True) ((ell : ℝ) ^ k)⁻¹
      ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ k * ((ell : ℝ) ^ k)⁻¹)⁻¹ ^ 1))
      ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ k * ((ell : ℝ) ^ k)⁻¹)⁻¹ ^ 2)) :=
    ⟨g, A, fun e _ => h1 e, fun μ ν x _ _ => h2 μ ν x⟩
  have hsmall : ((ell : ℝ) ^ k)⁻¹ * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ k * ((ell : ℝ) ^ k)⁻¹)⁻¹ ^ 1)) ≤ 1 := by
    rw [hc1]
    have : ((ell : ℝ) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
    nlinarith
  refine ⟨g, fun b => ?_, ?_⟩
  · have := cube_link hη0 K b trivial
    refine this.trans (le_of_eq ?_)
    rw [hc1, div_eq_inv_mul]
  · apply plaq_of_pw_one (periodicGaugeTransform g U)
    intro y ν μ
    have := cube_plaq hη0 K hsmall (y, ν, μ) ⟨trivial, trivial, trivial, trivial⟩
    refine this.trans (le_of_eq ?_)
    rw [hc1, hc2]
    field_simp

#print axioms regime_of_regular12

end AdalyFormal.M0Corollary
