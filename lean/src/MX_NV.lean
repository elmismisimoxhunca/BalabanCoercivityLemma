import MX_Orig
import AC_NV

/-!
# MX_NV -- the hypotheses of the MIXED headline are satisfiable (lane mixed_20261017)

`classCoupledΦ_of_forall` : if `Φ` is nonempty and the fixed-factor class `ClassCoupled ell M f` holds for EVERY `f ∈ Φ`, then `ClassCoupledΦ ell M Φ` holds.
`mixed_hyps_nonvacuous` : for EVERY nonempty `Φ` of factors `≥ 10` (no upper bound), every `R`, `M > 0` dividing the torus, `k ≥ 1`, the full tower is `Admissible`, `Λ = univ` is `LambdaOK2`, and
every `Ufield η χ` with `|χ e| ≤ α₀ η²/10` for all bonds `e` (the case `χ = 0` included: the theorem states the class hypothesis only and does not assert non-flatness of `Ufield`) satisfies `ClassCoupledΦ` (imports `AllC.classHyps_nonvacuous` for each factor).
-/
set_option autoImplicit false
namespace MXP.AllC

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

theorem classCoupledΦ_of_forall {L : PeriodicLatticeExtent} {ell M k : ℕ} {Φ : Set ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (hne : Φ.Nonempty) (h : ∀ f ∈ Φ, ClassCoupled ell M f k S α₀ η U) : ClassCoupledΦ ell M Φ k S α₀ η U := by
  obtain ⟨f0, hf0⟩ := hne
  refine ⟨?_, fun f hf => (h f hf).2⟩
  have h0 := coversΦ_single.2 (h f0 hf0).1
  obtain ⟨hs, hp⟩ := h0
  refine ⟨fun x hx => ?_, fun p hp' => ?_⟩
  · obtain ⟨sites, j, hq, hx'⟩ := hs x hx
    obtain ⟨f, hf, hq'⟩ := hq
    rw [Set.mem_singleton_iff] at hf
    exact ⟨sites, j, ⟨f0, hf0, hf ▸ hq'⟩, hx'⟩
  · obtain ⟨sites, j, hq, hb⟩ := hp p hp'
    obtain ⟨f, hf, hq'⟩ := hq
    rw [Set.mem_singleton_iff] at hf
    exact ⟨sites, j, ⟨f0, hf0, hf ▸ hq'⟩, hb⟩

theorem mixed_hyps_nonvacuous (ell M R k : ℕ) (Φ : Set ℕ) (hne : Φ.Nonempty) (hΦ : ∀ f ∈ Φ, 10 ≤ f) (hell : 0 < ell) (hM : 0 < M)
    (Lu : PeriodicLatticeExtent) (hT : ∀ μ : Fin 3, M ∣ Lu μ + 1) {α₀ : ℝ} (hα : 0 < α₀) (hk : 1 ≤ k)
    (χ : Bond (scaleUp ell k Lu) → ℝ) (hχ : ∀ e, |χ e| ≤ α₀ * (((ell : ℝ) ^ k)⁻¹) ^ 2 / 10) :
    Admissible ell M R k (fullTower ell k Lu) ∧
    LambdaOK2 (Lu := Lu) (Lf := scaleUp ell k Lu) ell M R k (fullTower ell k Lu) Set.univ ∧
    ClassCoupledΦ ell M Φ k (fullTower ell k Lu) α₀ (((ell : ℝ) ^ k)⁻¹) (Ufield (((ell : ℝ) ^ k)⁻¹) χ) := by
  obtain ⟨f0, hf0⟩ := hne
  obtain ⟨h1, h2, -⟩ := AdalyFormal.AllC.classHyps_nonvacuous ell M R k f0 hell hM (hΦ f0 hf0) Lu hT hα hk χ hχ
  exact ⟨h1, h2, classCoupledΦ_of_forall ⟨f0, hf0⟩ (fun f hf =>
    (AdalyFormal.AllC.classHyps_nonvacuous ell M R k f hell hM (hΦ f hf) Lu hT hα hk χ hχ).2.2)⟩

end MXP.AllC

#print axioms MXP.AllC.mixed_hyps_nonvacuous
