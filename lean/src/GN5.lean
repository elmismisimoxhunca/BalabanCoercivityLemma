import GN4
import B0i

/-!
# GN5 -- full tower (whole torus): `Ginv` coercivity with B0 PROVED, conditional only on site invertibility,
Poincare on `N(Q'(U))`, slice coercivity, and regularity of the background tower

`ginv_coercive_fullTower`: `G = geomOf ell k (fullTower ell k Lu)`, the genuine bond sector `bondSectorOf G U`, any `Jf`:
`‖x‖² ≤ max(2/cs, 2P²) ⟪x, Ginv x⟫` given `RegTower` (jet of the raw composite exists), `hu`, `hPoinc`, `hslice`.
`ginv_coercive_ingr`: the same for `IngrBParams.data` of the statement carrier (`P.S = fullTower`), any `Λ`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.StatementLane (scaleUp)

theorem fullTower_Om0 (ell k : ℕ) (Lu : PeriodicLatticeExtent) :
    (geomOf ell k (fullTower ell k Lu)).Om0 = Set.univ := by
  simp [geomOf, fullTower]

theorem ginv_coercive_fullTower (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Jf : BondFnL2 (scaleUp ell k Lu))
    (hreg : RegTower ell (bgTower (geomOf ell k (fullTower ell k Lu)) U) k)
    (hu : IsUnit (DelpA (geomOf ell k (fullTower ell k Lu)) U a
      + (1 - siteMask (geomOf ell k (fullTower ell k Lu)).Om0)))
    (P : ℝ) (hP : 0 ≤ P)
    (hPoinc : ∀ ν ∈ NQp (geomOf ell k (fullTower ell k Lu)) U, ‖ν‖ ≤ P * ‖gradL2 U ν‖)
    (cs : ℝ) (hcs : 0 < cs)
    (hslice : ∀ x : BondFnL2 (scaleUp ell k Lu),
      Rproj (geomOf ell k (fullTower ell k Lu)) U (gradAdj U x) = 0 →
      cs * ‖x‖ ^ 2 ≤ ⟪x, Delta (geomOf ell k (fullTower ell k Lu)) U x⟫
        + ⟪x, MassFull (geomOf ell k (fullTower ell k Lu)) a
            (bondSectorOf (geomOf ell k (fullTower ell k Lu)) U) x⟫)
    (x : ↥(bondSupp (geomOf ell k (fullTower ell k Lu)))) :
    ‖x‖ ^ 2 ≤ max (2 / cs) (2 * P ^ 2) *
      ⟪x, (baseData (geomOf ell k (fullTower ell k Lu)) U a
        (bondSectorOf (geomOf ell k (fullTower ell k Lu)) U) Jf).Ginv x⟫ :=
  ginv_coercive_cond _ (fullTower_Om0 ell k Lu) U a _ Jf hu
    (B0_fullTower ell k Lu hell U hreg) P hP hPoinc cs hcs hslice x

theorem ginv_coercive_ingr (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hreg : RegTower ell (bgTower (geomOf ell k (fullTower ell k Lu)) U) k)
    (hu : IsUnit (DelpA (geomOf ell k (fullTower ell k Lu)) U a
      + (1 - siteMask (geomOf ell k (fullTower ell k Lu)).Om0)))
    (P : ℝ) (hP : 0 ≤ P)
    (hPoinc : ∀ ν ∈ NQp (geomOf ell k (fullTower ell k Lu)) U, ‖ν‖ ≤ P * ‖gradL2 U ν‖)
    (cs : ℝ) (hcs : 0 < cs)
    (hslice : ∀ x : BondFnL2 (scaleUp ell k Lu),
      Rproj (geomOf ell k (fullTower ell k Lu)) U (gradAdj U x) = 0 →
      cs * ‖x‖ ^ 2 ≤ ⟪x, Delta (geomOf ell k (fullTower ell k Lu)) U x⟫
        + ⟪x, MassFull (geomOf ell k (fullTower ell k Lu)) a
            (bondSectorOf (geomOf ell k (fullTower ell k Lu)) U) x⟫)
    (x : ↥(bondSupp (geomOf ell k (fullTower ell k Lu)))) :
    ‖x‖ ^ 2 ≤ max (2 / cs) (2 * P ^ 2) *
      ⟪x, (IngrBParams.data ⟨ell, k, Lu, hell, fullTower ell k Lu, U, a, Lam⟩).Ginv x⟫ :=
  ginv_coercive_fullTower ell k Lu hell U a _ hreg hu P hP hPoinc cs hcs hslice x

#print axioms fullTower_Om0
#print axioms ginv_coercive_fullTower
#print axioms ginv_coercive_ingr

end AdalyFormal.SliceCoerc
