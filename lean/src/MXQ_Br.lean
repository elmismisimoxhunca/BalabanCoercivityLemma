import MXQ_F
import MX_F
import MX_NV

/-!
# MXQ_Br -- `P428Target8Family ⟹ P428Target8Mixed ⟹ P428Target8Total` (lane mixed_20261017, round 2)

`famPhi Φ` is the family of ALL triples whose factor lies in `Φ`; `ClassCoupledΦ ell M Φ` (every cube of every admitted factor regular, MX_Orig) implies `ClassCoupledQ ell M (famPhi Φ)`.
-/
set_option autoImplicit false

namespace MXQ.Total

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open MXQ.AllC

def famPhi (Φ : Set ℕ) : CF := fun _ => {t | t.2.2 ∈ Φ}

theorem classCoupledΦ_toQ {L : PeriodicLatticeExtent} {ell M k : ℕ} {Φ : Set ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : MXP.AllC.ClassCoupledΦ ell M Φ k S α₀ η U) : ClassCoupledQ ell M (famPhi Φ) k S α₀ η U := by
  obtain ⟨⟨hs, hp⟩, hreg⟩ := h
  refine ⟨⟨fun x hx => ?_, fun p hp' => ?_⟩, fun f sites j hm hq => hreg f hm sites j hq⟩
  · obtain ⟨sites, j, ⟨f, hf, hq⟩, hx'⟩ := hs x hx
    exact ⟨sites, j, ⟨f, hf, hq⟩, hx'⟩
  · obtain ⟨sites, j, ⟨f, hf, hq⟩, hb⟩ := hp p hp'
    exact ⟨sites, j, ⟨f, hf, hq⟩, hb⟩

/-- `Family ⟹ Mixed`. -/
theorem P428Target8Family.toMixed (h : P428Target8Family) : MXP.Total.P428Target8Mixed := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hT⟩ := h ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun Φ hΦ m hm R hR k hk Lu α₀ hα h2 => ?_⟩
  intro hT' S hS Lam hL U hU
  exact hT (famPhi Φ) ⟨fun _ _ _ f hm' => hΦ f hm'⟩ m hm R hR k hk Lu α₀ hα (fun L s j f hm' => h2 f hm') hT' S hS Lam hL U (classCoupledΦ_toQ hU)

theorem p428Target8Mixed_fromFamily : MXP.Total.P428Target8Mixed := p428Target8Family.toMixed

/-- satisfiability of the CLASS hypothesis of the family headline: on the full tower, for every `Ufield η χ` with `|χ e| ≤ α₀ η²/10` (`χ = 0` included; non-flatness is not asserted here) and the family `famPhi Φ` of ALL triples with factor in a nonempty `Φ` (every member `≥ 10`): `CubeFamOK (famPhi Φ)` and `ClassCoupledQ`.  The smallness, `TorusOK`, `Admissible` (the latter proved in MX_NV) and `LambdaOK2` hypotheses are not part of this statement. -/
theorem family_hyps_nonvacuous (ell M R k : ℕ) (Φ : Set ℕ) (hne : Φ.Nonempty) (hΦ : ∀ f ∈ Φ, 10 ≤ f) (hell : 0 < ell) (hM : 0 < M)
    (Lu : PeriodicLatticeExtent) (hT : ∀ μ : Fin 3, M ∣ Lu μ + 1) {α₀ : ℝ} (hα : 0 < α₀) (hk : 1 ≤ k)
    (χ : AdalyFormal.Balaban.AdmissibleSubspace.Bond (scaleUp ell k Lu) → ℝ) (hχ : ∀ e, |χ e| ≤ α₀ * (((ell : ℝ) ^ k)⁻¹) ^ 2 / 10) :
    CubeFamOK (famPhi Φ) ∧
    ClassCoupledQ ell M (famPhi Φ) k (AdalyFormal.IngredientFamilyR2.fullTower ell k Lu) α₀ (((ell : ℝ) ^ k)⁻¹)
      (AdalyFormal.StatementLane2.Ufield (((ell : ℝ) ^ k)⁻¹) χ) := by
  obtain ⟨-, -, h⟩ := MXP.AllC.mixed_hyps_nonvacuous ell M R k Φ hne hΦ hell hM Lu hT hα hk χ hχ
  exact ⟨⟨fun _ _ _ f hm' => hΦ f hm'⟩, classCoupledΦ_toQ h⟩

end MXQ.Total

#print axioms MXQ.Total.p428Target8Mixed_fromFamily
#print axioms MXQ.Total.family_hyps_nonvacuous
