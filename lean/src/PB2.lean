import PSiteC8
import PSiteC21
import PB4c
import AdalyFormal.Balaban.RegularUDomainWitness

/-!
# PB2 -- item (2): site invertibility `hu`, the covariant Poincare inequality on `N(Q'(U))`, and the site coercivity bound,
delivered on the slice carrier (`GF ell k Lu`) with the exact shapes GN10 consumes
(`hu : IsUnit (DelpA (GF ..) U a + (1 - siteMask (GF ..).Om0))`, `hPoincU/hPoinc1 : ∀ ν ∈ NQp .., ‖ν‖ ≤ P * ‖gradL2 U ν‖`).

Ported chain (text-ports on r7, modules `PSiteC1..PSiteC8, PSiteC12..PSiteC18, PSiteC21`): `site_coercive_towerclass` (SiteC8, k- and
volume-uniform under the tower class `δ_i = ρ ell^i/ell^k`), `unit_of_site_coercive` (SiteC2), `Qpa_form_zero_of_NQp` (SiteC21).
Bridge copied from SiteC9 (which cannot be imported: it imports NF6): `geomOf_eq_fullGeom` and `scaleUp_dvd`.
Standard axioms only (each declaration's printed axiom line).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.PortSlice

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp Tower)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.SiteCoercivity (fullGeom fullGeom_Lam_k fullGeom_Lam_lt)
open AdalyFormal.SliceCoerc (GF fullTower_Om0)

theorem scaleUp_dvd (ell k : ℕ) (hell : 0 < ell) (Lu : PeriodicLatticeExtent) :
    ∀ μ, ell ^ k ∣ scaleUp ell k Lu μ + 1 := by
  intro μ
  unfold scaleUp
  have : 1 ≤ (Lu μ + 1) * ell ^ k := Nat.mul_pos (Nat.succ_pos _) (pow_pos hell k)
  rw [Nat.sub_add_cancel this]
  exact Dvd.intro_left _ rfl

/-- the statement lane's `geomOf` at the WHOLE-TORUS full tower (`Ω_j = univ` for `j ≤ k`, `∅` after) is `fullGeom`. -/
theorem geomOf_eq_fullGeom {L : PeriodicLatticeExtent} (ell k : ℕ) (S : Tower L)
    (hle : ∀ j, j ≤ k → S.Om j = Set.univ) (hgt : ∀ j, k < j → S.Om j = ∅) :
    geomOf ell k S = fullGeom L ell k := by
  have hLam : ∀ j, (geomOf ell k S).Lam j = (fullGeom L ell k).Lam j := by
    intro j
    show {x | (∀ μ : Fin 3, ell ^ j ∣ (x μ).val) ∧ x ∈ S.Om j ∧ x ∉ S.Om (j + 1)} = _
    by_cases hjk : j = k
    · subst hjk
      rw [fullGeom_Lam_k, hle j le_rfl, hgt (j + 1) (Nat.lt_succ_self j)]
      ext x
      simp [mem_CoarseLattice, Nat.dvd_iff_mod_eq_zero]
    · rw [fullGeom_Lam_lt ell k hjk]
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ h1 h2
      by_cases hj : j < k
      · rw [hle (j + 1) (by omega)] at h2
        exact h2 (Set.mem_univ x)
      · rw [hgt j (by omega)] at h1
        exact h1
  have hOm : (geomOf ell k S).Om0 = (fullGeom L ell k).Om0 := by
    show S.Om 0 = Set.univ
    exact hle 0 (Nat.zero_le k)
  cases h1 : geomOf ell k S with
  | mk e1 k1 o1 l1 =>
    cases h2 : fullGeom L ell k with
    | mk e2 k2 o2 l2 =>
      rw [h1, h2] at hOm
      have hL : l1 = l2 := by
        funext j
        have := hLam j
        rw [h1, h2] at this
        exact this
      have he : e1 = e2 := by
        have a1 : (geomOf ell k S).ell = ell := rfl
        have a2 : (fullGeom L ell k).ell = ell := rfl
        rw [h1] at a1; rw [h2] at a2
        exact a1.trans a2.symm
      have hk : k1 = k2 := by
        have a1 : (geomOf ell k S).k = k := rfl
        have a2 : (fullGeom L ell k).k = k := rfl
        rw [h1] at a1; rw [h2] at a2
        exact a1.trans a2.symm
      simp only at hOm
      subst he hk hOm hL
      rfl


theorem GF_eq_fullGeom (ell k : ℕ) (Lu : PeriodicLatticeExtent) :
    GF ell k Lu = fullGeom (scaleUp ell k Lu) ell k :=
  geomOf_eq_fullGeom ell k (fullTower ell k Lu) (fun j hj => by simp [fullTower, hj])
    (fun j hj => by simp [fullTower, not_le.mpr hj])

/-- site coercivity on the slice carrier (statement of `site_coercive_towerclass`, `fullGeom` replaced by `GF`). -/
theorem site_coercive_GF (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hU : frobSupBond U ≤ ρ / (ell : ℝ) ^ k)
    (hT : ∀ i, i < k → frobSupBond (bgTower (GF ell k Lu) U i) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ k)
    (f : SiteL2 (scaleUp ell k Lu)) :
    (1 - 216 * ρ ^ 2) * ‖f‖ ^ 2
      ≤ max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 * ⟪f, DelpA (GF ell k Lu) U a f⟫ := by
  rw [GF_eq_fullGeom] at hT ⊢
  exact AdalyFormal.SiteCoercivity.site_coercive_towerclass ell k hell (scaleUp_dvd ell k (by omega) Lu) U a ha ρ hρ hU hT f

theorem mM_pos (a : ℝ) (ha : 0 < a) (ell k : ℕ) (hell : 2 ≤ ell) :
    0 < max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 := by
  have : (0 : ℝ) < ell := by exact_mod_cast (by omega : 0 < ell)
  have h6 : (0 : ℝ) < max 6 (16 / (3 * a)) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  positivity

/-- **ITEM (2a): `hu`** (site invertibility) for the slice carrier. -/
theorem hu_ported (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : 216 * ρ ^ 2 < 1)
    (hU : frobSupBond U ≤ ρ / (ell : ℝ) ^ k)
    (hT : ∀ i, i < k → frobSupBond (bgTower (GF ell k Lu) U i) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ k) :
    IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)) := by
  have hM := mM_pos a ha ell k hell
  refine AdalyFormal.SiteCoercivity.unit_of_site_coercive (GF ell k Lu) (fullTower_Om0 ell k Lu) U a
    (c := (1 - 216 * ρ ^ 2) / (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2)) (by apply div_pos <;> linarith) (fun f => ?_)
  have h := site_coercive_GF ell k Lu hell U a ha ρ hρ hU hT f
  rw [div_mul_eq_mul_div, div_le_iff₀ hM]
  linarith [h]

/-- **ITEM (2b): the covariant Poincare inequality on `N(Q'(U))`** (the (3.21) subspace), slice carrier, full tower,
constant `P_U = sqrt(max(6,16/(3a)) · n² / (1 - 216 ρ²))`, `n = ell^k`. -/
theorem poincare_ported (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : 216 * ρ ^ 2 < 1)
    (hU : frobSupBond U ≤ ρ / (ell : ℝ) ^ k)
    (hT : ∀ i, i < k → frobSupBond (bgTower (GF ell k Lu) U i) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ k) :
    ∀ ν ∈ NQp (GF ell k Lu) U,
      ‖ν‖ ≤ Real.sqrt (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 / (1 - 216 * ρ ^ 2))
        * ‖AdalyFormal.IngredientFamilyR2.gradL2 U ν‖ := by
  intro ν hν
  have hM := mM_pos a ha ell k hell
  have hpos : 0 < 1 - 216 * ρ ^ 2 := by linarith
  have h := site_coercive_GF ell k Lu hell U a ha ρ hρ hU hT ν
  have hq : ⟪ν, DelpA (GF ell k Lu) U a ν⟫ = ‖AdalyFormal.IngredientFamilyR2.gradL2 U ν‖ ^ 2 := by
    rw [AdalyFormal.SiteCoercivity.DelpA_univ _ (fullTower_Om0 ell k Lu), inner_add_right,
      AdalyFormal.SiteCoercivity.Qpa_form_zero_of_NQp (GF ell k Lu) U a hν, add_zero, inner_lapFull]
  rw [hq] at h
  have h2 : ‖ν‖ ^ 2 ≤ (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 / (1 - 216 * ρ ^ 2)) * ‖AdalyFormal.IngredientFamilyR2.gradL2 U ν‖ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    linarith [h]
  calc ‖ν‖ = Real.sqrt (‖ν‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 / (1 - 216 * ρ ^ 2))
          * ‖AdalyFormal.IngredientFamilyR2.gradL2 U ν‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 / (1 - 216 * ρ ^ 2))
          * ‖AdalyFormal.IngredientFamilyR2.gradL2 U ν‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- the flat (trivial) background satisfies the hypotheses with `ρ = 0`. -/
theorem trivialU_tower_zero (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (i : ℕ) :
    frobSupBond (bgTower (GF ell k Lu) (trivialU (scaleUp ell k Lu)) i) ≤ 0 := by
  have h := frobSup_bgTower_le (GF ell k Lu) (by omega : 0 < ell) (trivialU (scaleUp ell k Lu)) i
  rw [AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU, mul_zero] at h
  exact h

theorem hu_flat (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    IsUnit (DelpA (GF ell k Lu) (trivialU (scaleUp ell k Lu)) a + (1 - siteMask (GF ell k Lu).Om0)) :=
  hu_ported ell k Lu hell _ a ha 0 le_rfl (by norm_num)
    (by rw [AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU]; simp)
    (fun i _ => by have := trivialU_tower_zero ell k Lu (by omega) i; simpa using this)

theorem poincare_flat (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∀ ν ∈ NQp (GF ell k Lu) (trivialU (scaleUp ell k Lu)),
      ‖ν‖ ≤ Real.sqrt (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2)
        * ‖AdalyFormal.IngredientFamilyR2.gradL2 (trivialU (scaleUp ell k Lu)) ν‖ := by
  have h := poincare_ported ell k Lu hell (trivialU (scaleUp ell k Lu)) a ha 0 le_rfl (by norm_num)
    (by rw [AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU]; simp)
    (fun i _ => by have := trivialU_tower_zero ell k Lu (by omega) i; simpa using this)
  simpa using h

#print axioms GF_eq_fullGeom
#print axioms site_coercive_GF
#print axioms hu_ported
#print axioms poincare_ported
#print axioms hu_flat
#print axioms poincare_flat

end AdalyFormal.PortSlice
