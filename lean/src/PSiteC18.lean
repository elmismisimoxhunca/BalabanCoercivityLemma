import PSiteC17
import PSiteC8

/-!
# SiteC18 -- PROPER-TOWER site coercivity (Dirichlet on `Ω₀`), the masked-form bound, `hu` and `‖G'‖`, and the k-uniform tower-class instance.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.SiteCoercivity

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

/-- **PROPER-TOWER (Dirichlet) SITE COERCIVITY**, masked form.  Only the links with head in `Ω₀` and the tower links based in `Ω₀` are controlled. -/
theorem site_coercive_proper (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
    {G : TowerGeom L} (hP : ProperTower G ell k) (U : Cfg L) (a : ℝ) (ha : 0 < a) (α E : ℝ) (hα : 0 ≤ α)
    (hU : ∀ b : Bond L, periodicLatticeShift b.1 b.2 ∈ G.Om0 →
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α / (ell : ℝ) ^ k)
    (δ : ℕ → ℝ) (hδ0 : ∀ i, 0 ≤ δ i)
    (hT : ∀ i, i < k → ∀ z ∈ G.Om0, ∀ μ : Fin 3,
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ i)
    (hE : ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i ≤ E) (f : SiteL2 L) :
    (1 - 72 * α ^ 2 - 4 * E ^ 2) * ‖siteMask G.Om0 f‖ ^ 2
      ≤ max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 * ⟪f, DelpA G U a f⟫ := by
  have h := site_coercive_proper_core ell k hell hdvd hP U a ha α E hα hU δ hδ0 hT hE (siteMask G.Om0 f)
    (by
      intro x hx
      classical
      show (if x ∈ G.Om0 then f x else 0) = 0
      rw [if_neg hx])
  rw [inner_DelpA_mask G U a f]
  exact h

/-- `hu` and `‖G'‖ ≤ 1/c` for the proper tower, `c = (1 − 72α² − 4E²)/(max(6,16/(3a))·n²)`. -/
theorem proper_unit_Gp (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
    {G : TowerGeom L} (hP : ProperTower G ell k) (U : Cfg L) (a : ℝ) (ha : 0 < a) (α E : ℝ) (hα : 0 ≤ α)
    (hU : ∀ b : Bond L, periodicLatticeShift b.1 b.2 ∈ G.Om0 →
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α / (ell : ℝ) ^ k)
    (δ : ℕ → ℝ) (hδ0 : ∀ i, 0 ≤ δ i)
    (hT : ∀ i, i < k → ∀ z ∈ G.Om0, ∀ μ : Fin 3,
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ i)
    (hE : ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i ≤ E) (hpos : 72 * α ^ 2 + 4 * E ^ 2 < 1) :
    IsUnit (DelpA G U a + (1 - siteMask G.Om0)) ∧
      ∀ s : SiteL2 L, ‖Gp G U a s‖ ≤
        (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 / (1 - 72 * α ^ 2 - 4 * E ^ 2)) * ‖s‖ := by
  have hm : 6 ≤ max 6 (16 / (3 * a)) := le_max_left _ _
  have hn1 : (1 : ℝ) ≤ ((ell : ℝ) ^ k) ^ 2 := by
    have : (1 : ℝ) ≤ (ell : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ ell))
    nlinarith
  have hden : 0 < 1 - 72 * α ^ 2 - 4 * E ^ 2 := by linarith
  set m := max 6 (16 / (3 * a)) with hmdef
  set n2 : ℝ := ((ell : ℝ) ^ k) ^ 2 with hn2
  have hmn : 0 < m * n2 := by positivity
  set c : ℝ := (1 - 72 * α ^ 2 - 4 * E ^ 2) / (m * n2) with hcdef
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hcdef, div_le_one hmn]
    have : 1 - 72 * α ^ 2 - 4 * E ^ 2 ≤ 1 := by nlinarith [sq_nonneg α, sq_nonneg E]
    nlinarith
  have hc : ∀ f : SiteL2 L, c * ‖siteMask G.Om0 f‖ ^ 2 ≤ ⟪f, DelpA G U a f⟫ := by
    intro f
    have h := site_coercive_proper ell k hell hdvd hP U a ha α E hα hU δ hδ0 hT hE f
    rw [hcdef, div_mul_eq_mul_div, div_le_iff₀ hmn]
    nlinarith [h]
  obtain ⟨hu, hG⟩ := unit_Gp_of_masked_coercive G U a hc0 hc1 hc
  refine ⟨hu, fun s => ?_⟩
  have e : 1 / c = m * n2 / (1 - 72 * α ^ 2 - 4 * E ^ 2) := by rw [hcdef]; field_simp
  rw [← e]
  exact hG s

/-- **k-UNIFORM proper-tower site coercivity** under the tower class `δ_i = ρ ell^i/ell^k`. -/
theorem site_coercive_proper_towerclass (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
    {G : TowerGeom L} (hP : ProperTower G ell k) (U : Cfg L) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hU : ∀ b : Bond L, periodicLatticeShift b.1 b.2 ∈ G.Om0 →
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ k)
    (hT : ∀ i, i < k → ∀ z ∈ G.Om0, ∀ μ : Fin 3,
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ k)
    (f : SiteL2 L) :
    (1 - 216 * ρ ^ 2) * ‖siteMask G.Om0 f‖ ^ 2
      ≤ max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 * ⟪f, DelpA G U a f⟫ := by
  have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast (by omega : 1 ≤ ell)
  have h := site_coercive_proper ell k hell hdvd hP U a ha ρ (6 * ρ) hρ hU
    (fun i => ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ k)
    (fun i => by have : (0 : ℝ) ≤ (ell : ℝ) ^ i / (ell : ℝ) ^ k := by positivity
                 have e : ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ k = ρ * ((ell : ℝ) ^ i / (ell : ℝ) ^ k) := by ring
                 rw [e]; positivity)
    hT (geom_tower_sum ell k hell ρ hρ) f
  nlinarith [h]

#print axioms site_coercive_proper_towerclass
#print axioms site_coercive_proper_core
#print axioms site_coercive_proper
#print axioms proper_unit_Gp

end AdalyFormal.SiteCoercivity
