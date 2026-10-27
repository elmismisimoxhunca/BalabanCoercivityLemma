import MS12

/-!
# MS13 -- the plaquette clause on the statement's `periodicPlaquetteHolonomy`

`hplaq_of_holonomy` : a bound `dv(periodicPlaquetteHolonomy U p) ≤ ρ/ℓ^{2 j0}` for every plaquette `p` (ordered directions `d₁ < d₂`)
whose four corners lie in `Ω_{j0}` implies MS9's `hplaq` on the plaquette words `pw 1 U y ν μ` (all `ν, μ`: `ν < μ` is the holonomy,
`ν = μ` is `1`, `ν > μ` is the inverse holonomy — the identities of curvature_blocking NB31, pointwise).
**`site_coercive_M1_hol`** : S1 under `hlink` and this holonomy-form plaquette clause.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1Site

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.CurvBlock (dv pw)

variable {Lf : PeriodicLatticeExtent}

theorem coarseShift_one (y : PeriodicLatticeSite Lf) (ν : Fin 3) : coarseShift y 1 ν = periodicLatticeShift y ν := rfl

theorem hplaq_of_holonomy (ell k : ℕ) (hell : 0 < ell) {S : Tower Lf} (U : Cfg Lf) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (h : ∀ j0, j0 ≤ k → ∀ p : PeriodicLatticePlaquette Lf,
      p.1 ∈ S.Om j0 → periodicLatticeShift p.1 p.2.1.1 ∈ S.Om j0 → periodicLatticeShift p.1 p.2.1.2 ∈ S.Om j0 →
      periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∈ S.Om j0 →
      dv (periodicPlaquetteHolonomy U p) ≤ ρ / (ell : ℝ) ^ (2 * j0)) :
    ∀ j0, j0 ≤ k → ∀ (y : PeriodicLatticeSite Lf) (ν μ : Fin 3),
      y ∈ S.Om j0 → coarseShift y 1 ν ∈ S.Om j0 → coarseShift y 1 μ ∈ S.Om j0 →
      coarseShift (coarseShift y 1 ν) 1 μ ∈ S.Om j0 → dv (pw 1 U y ν μ) ≤ ρ / (ell : ℝ) ^ (2 * j0) := by
  intro j0 hj0 y ν μ h1 h2 h3 h4
  rcases lt_trichotomy ν μ with hlt | heq | hgt
  · have e : pw 1 U y ν μ = periodicPlaquetteHolonomy U (y, ⟨(ν, μ), hlt⟩) := rfl
    rw [e]
    exact h j0 hj0 _ h1 h2 h3 h4
  · subst heq
    have e : pw 1 U y ν ν = 1 := by unfold pw; group
    rw [e, AdalyFormal.CurvBlock.dv_one]
    exact div_nonneg hρ (by positivity)
  · have e : pw 1 U y ν μ = (periodicPlaquetteHolonomy U (y, ⟨(μ, ν), hgt⟩))⁻¹ := by
      show _ = (U (y, μ) * U (periodicLatticeShift y μ, ν) * (U (periodicLatticeShift y ν, μ))⁻¹
        * (U (y, ν))⁻¹)⁻¹
      unfold pw
      show U (y, ν) * U (periodicLatticeShift y ν, μ) * (U (periodicLatticeShift y μ, ν))⁻¹
        * (U (y, μ))⁻¹ = _
      group
    rw [e, AdalyFormal.CurvBlock.dv_inv]
    have hc : coarseShift (coarseShift y 1 μ) 1 ν = coarseShift (coarseShift y 1 ν) 1 μ :=
      AdalyFormal.Balaban.U1AnchorPoincare.coarseShift_comm_gen y 1 1 μ ν
    exact h j0 hj0 (y, ⟨(μ, ν), hgt⟩) h1 h3 h2 (by show coarseShift (coarseShift y 1 μ) 1 ν ∈ S.Om j0; rw [hc]; exact h4)

/-- **S1 with the holonomy-form plaquette clause** -/
theorem site_coercive_M1_hol (ell M R k : ℕ) (hell : 2 ≤ ell) {S : Tower Lf} (hS : Admissible ell M R k S)
    (hRM : 18 ≤ R * M) (hbig : ∀ σ, 4 * ell ^ k < Lf σ + 1)
    (U : Cfg Lf) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ) (hsmall : 4000000 * (ell : ℝ) ^ 2 * ρ ≤ 1)
    (hlink : ∀ j0, j0 ≤ k → ∀ b : Bond Lf, b.1 ∈ S.Om j0 → periodicLatticeShift b.1 b.2 ∈ S.Om j0 →
      dv (U b) ≤ ρ / (ell : ℝ) ^ j0)
    (hhol : ∀ j0, j0 ≤ k → ∀ p : PeriodicLatticePlaquette Lf,
      p.1 ∈ S.Om j0 → periodicLatticeShift p.1 p.2.1.1 ∈ S.Om j0 → periodicLatticeShift p.1 p.2.1.2 ∈ S.Om j0 →
      periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∈ S.Om j0 →
      dv (periodicPlaquetteHolonomy U p) ≤ ρ / (ell : ℝ) ^ (2 * j0))
    (f : SiteL2 Lf) :
    (1 - 216 * (((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ) ^ 2) * wNormSq (geomOf ell k S) f
      ≤ max 6 (16 / (3 * a)) * ⟪f, DelpA (geomOf ell k S) U a f⟫ :=
  site_coercive_M1 ell M R k hell hS hRM hbig U a ha ρ hρ hsmall hlink
    (hplaq_of_holonomy ell k (by omega) U ρ hρ hhol) f

#print axioms coarseShift_one
#print axioms hplaq_of_holonomy
#print axioms site_coercive_M1_hol

end AdalyFormal.M1Site
