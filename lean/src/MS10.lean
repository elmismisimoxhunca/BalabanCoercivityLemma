import MS9

/-!
# MS10 -- S1 under the PLAN §1.1 `M1Regime`-shaped clauses (strata of the endpoints / corners)

PLAN §1.1 writes the link clause as `dv(U_b) ≤ ρ/ℓ^{bstrat b}` with `bstrat b = min(strat b₋, strat b₊)` and the plaquette clause with
`pstrat` (minimum over the boundary bonds).  With `strat = stratG (geomOf ℓ k S)` (MS7 `stratG_geomOf`: equal to the sketch's
`sSup {j ≤ k | x ∈ Ω_j}`):
* `le_stratG_of_mem` : `x ∈ Ω_{j0}`, `j0 ≤ k` ⇒ `j0 ≤ stratG x`;
* `hlink_of_strat`, `hplaq_of_strat` : the strata-form clauses imply MS9's `hlink`, `hplaq`;
* **`site_coercive_M1_strat`** : S1 (weighted, k-free) from the strata-form clauses alone (+ collar `18 ≤ RM`, no wrap,
  `4·10⁶ ℓ² ρ ≤ 1`).  The plaquette clause is on the fine plaquette word `pw 1 U y ν μ` (curvature_blocking CB2) with the strata of its
  four corners.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1Site

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.CurvBlock (dv pw)

variable {Lf : PeriodicLatticeExtent}

theorem le_stratG_of_mem {ell M R k : ℕ} (hell : 0 < ell) {S : Tower Lf} (hS : Admissible ell M R k S)
    {j0 : ℕ} (hj0 : j0 ≤ k) {x : PeriodicLatticeSite Lf} (hx : x ∈ S.Om j0) : j0 ≤ stratG (geomOf ell k S) x := by
  rw [stratG_geomOf hell hS]
  exact le_csSup ⟨k, fun j hj => hj.1⟩ ⟨hj0, hx⟩

theorem div_pow_mono (ρ : ℝ) (hρ : 0 ≤ ρ) (ell : ℕ) (hell : 0 < ell) {m n : ℕ} (hmn : m ≤ n) :
    ρ / (ell : ℝ) ^ n ≤ ρ / (ell : ℝ) ^ m := by
  have h1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  exact div_le_div_of_nonneg_left hρ (by positivity) (pow_le_pow_right₀ h1 hmn)

theorem hlink_of_strat {ell M R k : ℕ} (hell : 0 < ell) {S : Tower Lf} (hS : Admissible ell M R k S)
    (U : Cfg Lf) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (h : ∀ b : Bond Lf, b.1 ∈ S.Om 0 → periodicLatticeShift b.1 b.2 ∈ S.Om 0 →
      dv (U b) ≤ ρ / (ell : ℝ) ^ (min (stratG (geomOf ell k S) b.1) (stratG (geomOf ell k S) (periodicLatticeShift b.1 b.2)))) :
    ∀ j0, j0 ≤ k → ∀ b : Bond Lf, b.1 ∈ S.Om j0 → periodicLatticeShift b.1 b.2 ∈ S.Om j0 →
      dv (U b) ≤ ρ / (ell : ℝ) ^ j0 := by
  intro j0 hj0 b h1 h2
  have hnest := hS.1
  have h1' := om_antitone S hnest (Nat.zero_le j0) h1
  have h2' := om_antitone S hnest (Nat.zero_le j0) h2
  refine (h b h1' h2').trans (div_pow_mono ρ hρ ell hell ?_)
  exact le_min (le_stratG_of_mem hell hS hj0 h1) (le_stratG_of_mem hell hS hj0 h2)

/-- the corner stratum of a fine plaquette word -/
noncomputable def cornerStrat (G : TowerGeom Lf) (y : PeriodicLatticeSite Lf) (ν μ : Fin 3) : ℕ :=
  min (min (stratG G y) (stratG G (coarseShift y 1 ν)))
    (min (stratG G (coarseShift y 1 μ)) (stratG G (coarseShift (coarseShift y 1 ν) 1 μ)))

theorem hplaq_of_strat {ell M R k : ℕ} (hell : 0 < ell) {S : Tower Lf} (hS : Admissible ell M R k S)
    (U : Cfg Lf) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (h : ∀ (y : PeriodicLatticeSite Lf) (ν μ : Fin 3),
      y ∈ S.Om 0 → coarseShift y 1 ν ∈ S.Om 0 → coarseShift y 1 μ ∈ S.Om 0 →
      coarseShift (coarseShift y 1 ν) 1 μ ∈ S.Om 0 →
      dv (pw 1 U y ν μ) ≤ ρ / (ell : ℝ) ^ (2 * cornerStrat (geomOf ell k S) y ν μ)) :
    ∀ j0, j0 ≤ k → ∀ (y : PeriodicLatticeSite Lf) (ν μ : Fin 3),
      y ∈ S.Om j0 → coarseShift y 1 ν ∈ S.Om j0 → coarseShift y 1 μ ∈ S.Om j0 →
      coarseShift (coarseShift y 1 ν) 1 μ ∈ S.Om j0 → dv (pw 1 U y ν μ) ≤ ρ / (ell : ℝ) ^ (2 * j0) := by
  intro j0 hj0 y ν μ h1 h2 h3 h4
  have hnest := hS.1
  have a : ∀ x, x ∈ S.Om j0 → x ∈ S.Om 0 := fun x hx => om_antitone S hnest (Nat.zero_le j0) hx
  refine (h y ν μ (a _ h1) (a _ h2) (a _ h3) (a _ h4)).trans (div_pow_mono ρ hρ ell hell ?_)
  have hc : j0 ≤ cornerStrat (geomOf ell k S) y ν μ := by
    unfold cornerStrat
    exact le_min (le_min (le_stratG_of_mem hell hS hj0 h1) (le_stratG_of_mem hell hS hj0 h2))
      (le_min (le_stratG_of_mem hell hS hj0 h3) (le_stratG_of_mem hell hS hj0 h4))
  omega

/-- **S1 under the `M1Regime`-shaped clauses** -/
theorem site_coercive_M1_strat (ell M R k : ℕ) (hell : 2 ≤ ell) {S : Tower Lf} (hS : Admissible ell M R k S)
    (hRM : 18 ≤ R * M) (hbig : ∀ σ, 4 * ell ^ k < Lf σ + 1)
    (U : Cfg Lf) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ) (hsmall : 4000000 * (ell : ℝ) ^ 2 * ρ ≤ 1)
    (hl : ∀ b : Bond Lf, b.1 ∈ S.Om 0 → periodicLatticeShift b.1 b.2 ∈ S.Om 0 →
      dv (U b) ≤ ρ / (ell : ℝ) ^ (min (stratG (geomOf ell k S) b.1) (stratG (geomOf ell k S) (periodicLatticeShift b.1 b.2))))
    (hp : ∀ (y : PeriodicLatticeSite Lf) (ν μ : Fin 3),
      y ∈ S.Om 0 → coarseShift y 1 ν ∈ S.Om 0 → coarseShift y 1 μ ∈ S.Om 0 →
      coarseShift (coarseShift y 1 ν) 1 μ ∈ S.Om 0 →
      dv (pw 1 U y ν μ) ≤ ρ / (ell : ℝ) ^ (2 * cornerStrat (geomOf ell k S) y ν μ))
    (f : SiteL2 Lf) :
    (1 - 216 * (((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * ρ) ^ 2) * wNormSq (geomOf ell k S) f
      ≤ max 6 (16 / (3 * a)) * ⟪f, DelpA (geomOf ell k S) U a f⟫ :=
  site_coercive_M1 ell M R k hell hS hRM hbig U a ha ρ hρ hsmall
    (hlink_of_strat (by omega) hS U ρ hρ hl) (hplaq_of_strat (by omega) hS U ρ hρ hp) f

#print axioms le_stratG_of_mem
#print axioms div_pow_mono
#print axioms hlink_of_strat
#print axioms hplaq_of_strat
#print axioms site_coercive_M1_strat

end AdalyFormal.M1Site
