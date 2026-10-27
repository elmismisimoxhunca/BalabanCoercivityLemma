import UNI_Red
import AC_NV

/-!
# UNI_NV -- non-vacuity of the union-class hypotheses (lane union_cubes_20261018)

On the full tower, for the smooth `Ufield η χ` (|χ| ≤ α₀ η²/10), the family `F = {(box, j, c)}` of grid-aligned boxes of the single factor `c ≥ 10` satisfies `ClassCoupledU`: coverage by r8 class cubes (`AllC.classHyps_nonvacuous`) which are class unions on an admissible tower (`boxClass_iff`);
regularity over class unions of `F`: a class union of `F` has box shape, hence is an r8 class cube (`boxClass_iff`), where the r8 regularity applies.  The hypotheses `10 ≤ f`, `Admissible`, `LambdaOK2` of the headline are also shown.
-/
set_option autoImplicit false

namespace UNI.Total

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.IngredientFamilyR2 (fullTower)
open UNI.AllC

theorem union_hyps_nonvacuous (ell M R k c : ℕ) (hell : 0 < ell) (hM : 0 < M) (hc : 10 ≤ c) (Lu : PeriodicLatticeExtent)
    (hT : ∀ μ : Fin 3, M ∣ Lu μ + 1) {α₀ : ℝ} (hα : 0 < α₀) (hk : 1 ≤ k)
    (χ : AdalyFormal.Balaban.AdmissibleSubspace.Bond (scaleUp ell k Lu) → ℝ) (hχ : ∀ e, |χ e| ≤ α₀ * (((ell : ℝ) ^ k)⁻¹) ^ 2 / 10) :
    ∃ F : CubeFam (scaleUp ell k Lu),
      (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F → 10 ≤ f) ∧
      Admissible ell M R k (fullTower ell k Lu) ∧
      AdalyFormal.StatementLaneG.LambdaOK2 (Lu := Lu) (Lf := scaleUp ell k Lu) ell M R k (fullTower ell k Lu) Set.univ ∧
      ClassCoupledU ell M F k (fullTower ell k Lu) α₀ (((ell : ℝ) ^ k)⁻¹) (Ufield (((ell : ℝ) ^ k)⁻¹) χ) := by
  obtain ⟨hadm, hlam, ⟨⟨hs, hp⟩, hreg⟩⟩ := AdalyFormal.AllC.classHyps_nonvacuous ell M R k c hell hM hc Lu hT hα hk χ hχ
  let F : CubeFam (scaleUp ell k Lu) := {t | t.2.2 = c ∧ boxShape (scaleUp ell k Lu) ell M c t.1 t.2.1}
  have hmem : ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
      IsClassCube ell M c k (fullTower ell k Lu) sites j → (sites, j, c) ∈ F := fun sites j hq =>
    ⟨rfl, hq.1.2.1⟩
  refine ⟨F, fun s j f hm => by have h1 : f = c := hm.1; rw [h1]; exact hc, hadm, hlam, ⟨fun x hx => ?_, fun p hp' => ?_, fun f sites j hm hu => ?_⟩⟩
  · obtain ⟨sites, j, hq, hx'⟩ := hs x hx
    exact ⟨sites, j, ⟨c, hmem sites j hq, ((boxClass_iff hadm c sites j).1 hq).1⟩, hx'⟩
  · obtain ⟨sites, j, hq, hb⟩ := hp p hp'
    exact ⟨sites, j, ⟨c, hmem sites j hq, ((boxClass_iff hadm c sites j).1 hq).1⟩, hb⟩
  · obtain ⟨hfc, hbox⟩ := hm
    have hf : f = c := hfc
    subst hf
    exact hreg sites j ((boxClass_iff hadm f sites j).2 ⟨hu, hbox⟩)

end UNI.Total

#print axioms UNI.Total.union_hyps_nonvacuous
