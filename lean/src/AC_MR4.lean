import MR2
import AC_Base

/-!
# AC_MR4 -- `PatchCoercive` from `PatchCharts` (lane allc_20261016)

MR4 `patchCoercive_class_exists` took the per-cube class `PerCubeRegular2 .. 12 ..` and `InterfaceCharts`, built `PatchCharts` from them with the centred class cube
(MR3, cube factor 12), and applied MR2 `patchCoercive_charts_exists`.  Here `PatchCharts` (all patches, from `BallChartsAt`: AC_OG7) is the input; no cube
factor and no `3 * 12 <= R ell` hypothesis remain.  The proof is MR4's with the `patchCharts_class` step deleted.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2Route

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1 (IsPatch gsp M1Regular)
open AdalyFormal.M1IMS (HatPack HolRegime etaC nuC PatchCoercive)
open AdalyFormal.M1NonFlat (epsNF PkA thetaN)

theorem patchCoercive_class_existsAC {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ D : ℕ, 12 * ell + 10 ≤ D ∧
    (∀ d, D ≤ d → epsNF ell (PkA a) (thetaN ell) d ≤ cW / 2) ∧
    ∀ {M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
      {S : Tower (scaleUp ell k Lu)} (_hS : Admissible ell M R k S) (_hM : 0 < M) (_hR1 : 1 ≤ R)
      (_hR24 : 24 ≤ R)
      (_hR4 : (5 + 4) * 1 * ell ≤ R) (_hroom : 17 * ell ≤ R * M) {d : ℕ} (_hdD : D ≤ d)
      (_hdM : d + 64 * ell ^ 2 + 2 ≤ M)
      {W : ℕ} (_hW : 1 ≤ W) (_hWR : W ≤ R * M * ell)
      (U : LinkCfg (scaleUp ell k Lu)) (cs : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
      (_hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
      (ρ : ℝ) (_hρ : 0 ≤ ρ) (_hreg : HolRegime S ell k U ρ) (ε1 : ℝ) (_hε1 : 0 < ε1) (_hη : etaC ell W cs ρ ε1 < 1)
      (η : ℝ) (_hη0 : 0 < η)
      (a' : ℝ) (_ha'0 : 0 < a') (_ha'a : a' ≤ a₀)
      (_hI : PatchCharts ell M k 1 5 d S U η a'),
      PatchCoercive ell M k 1 5 Lu hell0 S U a Lam
        ((1 - etaC ell W cs ρ ε1) * min a (cW - epsNF ell (PkA a) (thetaN ell) d) - 2 * nuC ell ρ) := by
  obtain ⟨cW, hcW, a₀, ha₀, D, hD, hDle, hmain⟩ := patchCoercive_charts_exists hell ha
  refine ⟨cW, hcW, a₀, ha₀, D, hD, hDle, ?_⟩
  intro M R k Lu hell0 S hS hM hR1 hR24 hR4 hroom d hdD hdM W hW hWR U cs Lam hp ρ hρ hreg ε1 hε1 hη η hη0
    a' ha'0 ha'a hI
  have hdM' : d + 64 * ell ^ 2 ≤ 1 * M := by omega
  exact hmain hell0 hS one_pos hM hR1 hR4 hroom hdD hdM' hW hWR U cs Lam hp ρ hρ hreg ε1 hε1 hη η hη0 a' ha'0 ha'a hI

end AdalyFormal.M2Route

#print axioms AdalyFormal.M2Route.patchCoercive_class_existsAC
