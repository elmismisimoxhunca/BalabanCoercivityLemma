import OG9

/-!
# OG10 -- small lemmas for the K-shifted assembly (lane m2_onegap_20261015)
* `classCoupled_mono` : `ClassCoupled` is monotone in the class constant `α₀` (`0 ≤ η`, `α₀ ≤ β`).
* `instIneq_empty` : for `Λ = ∅` the instantiated inequality `InstIneq` holds for every `U` (trivial: `OnLambdaT ∅ Bt` forces `Bt = 0`, and `D2in 0 = 0`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.OneGap

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK pdist IsClassCube CubeBond)
open AdalyFormal.StatementLane2 (ClassCoupled PerCubeRegular2)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

theorem classCoupled_mono {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L} {α₀ β η : ℝ} {U : LinkCfg L}
    (hη : 0 ≤ η) (hαβ : α₀ ≤ β) (h : ClassCoupled ell M c k S α₀ η U) : ClassCoupled ell M c k S β η U := by
  refine ⟨h.1, fun sites j hq => ?_⟩
  obtain ⟨g, A, hc1, hc2, hc3⟩ := h.2 sites j hq
  have hcM : (0 : ℝ) ≤ (c : ℝ) * M := by positivity
  have key : ∀ p : ℕ, (c : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ p) ≤ (c : ℝ) * M * β * (((ell : ℝ) ^ j * η)⁻¹ ^ p) := by
    intro p
    have hX : (0 : ℝ) ≤ ((ell : ℝ) ^ j * η)⁻¹ ^ p := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαβ hcM) hX
  refine ⟨g, A, fun e he => ⟨(hc1 e he).1, (hc1 e he).2.1, lt_of_lt_of_le (hc1 e he).2.2 (key 1)⟩,
    fun μ ν x h1 h2 => lt_of_lt_of_le (hc2 μ ν x h1 h2) (key 2), fun μ x hr => lt_of_lt_of_le (hc3 μ x hr) (key 3)⟩

theorem d2in_zero (P : IngrBParams) : P.D2in 0 = 0 := by
  unfold IngrBParams.D2in
  have h : C2tilde P.ell P.unitBgU
      (0 : AdalyFormal.Balaban.AdmissibleSubspace.Bond P.Lu → ↥AdalyFormal.Balaban.CovariantOperators.SuTwo) = 0 := by
    funext c
    unfold C2tilde C2StepL
    simp
  simp [h]

theorem instIneq_mono {ell k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent} {γ₀ γ₁ : ℝ}
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {U : LinkCfg (scaleUp ell k Lu)}
    (hγ : γ₁ ≤ γ₀) (h : InstIneq ell k hell a Lu γ₀ S Lam U) : InstIneq ell k hell a Lu γ₁ S Lam U := by
  intro Bt h1 h2
  have h3 := h Bt h1 h2
  have hE : 0 ≤ AdalyFormal.Balaban.RegularUPerturbation.bondEnergy Bt :=
    Finset.sum_nonneg (fun b _ => by positivity)
  nlinarith

theorem instIneq_empty (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu)) :
    InstIneq ell k hell a Lu γ₀ S (∅ : Set (PeriodicLatticeSite Lu)) U := by
  intro Bt _ hBt
  have h0 : Bt = 0 := by
    funext b
    exact hBt b (by simp)
  subst h0
  have hd := d2in_zero (gparams ell k Lu hell S U a ∅)
  simp [GenP.genForm, GenP.genC, GenP.firstTerm, AdalyFormal.Balaban.RegularUPerturbation.bondEnergy, hd]

/-- the headline block restricted to THIN tori (`∃ σ, Lu σ + 1 < 13 M`) and nonempty `Λ`: the case in which balls of radius `6 M ℓ^j` can wrap the torus -/
def ThinCore (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → ((12 : ℕ) : ℝ) * (M : ℝ) * α₀ ≤ a₀ →
      (∃ σ : Fin 3, Lu σ + 1 < 13 * M) → TorusOK ell M Lu →
      ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
      ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam → Lam.Nonempty →
      ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      InstIneq ell k hell a Lu γ₀ S Lam U

/-- the thin-torus residual, in the headline's quantifier order -/
def ThinTori : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R →
    ThinCore ell (ell ^ m) R (by omega) a

open AdalyFormal.M2Skel (ClassFam) in
/-- the fields of `RemainingInputs` that do not depend on the chart constant (`OpLayer` and `Q*`-injectivity), verbatim from SK1 -/
structure Residual : Prop where
  /-- (F5) the operator layer of the D-layer -/
  opLayer : ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ClassFam ell (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ)
      (fun M R c => 0 < c.1 ∧ (ell : ℝ) ^ 3 * Real.exp (-(c.1 * (R * M))) ≤ 1 / 2 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2.1 ∧
        0 ≤ c.2.2.2.1 ∧ 0 ≤ c.2.2.2.2.1 ∧ 0 ≤ c.2.2.2.2.2)
      (fun M R k Lu c S Lam U α₀ => AdalyFormal.M2DLayer.OpLayer ell M R k Lu (by omega) S U a Lam
        c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2)
  /-- (F6, exit part) injectivity of `Q_U*` (W6) when some level-0 row ball leaves `Ω_0` -/
  qsInjExit : ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ClassFam ell Unit (fun _ _ _ => True) (fun M R k Lu _ S Lam U α₀ =>
      ¬ ExitFree ell k Lu S → Function.Injective (gparams ell k Lu (by omega) S U a Lam).data.Qs)
  /-- thin tori (balls of radius `6 M ℓ^j` may wrap) -/
  thin : ThinTori

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.classCoupled_mono
#print axioms AdalyFormal.OneGap.d2in_zero
#print axioms AdalyFormal.OneGap.instIneq_empty
#print axioms AdalyFormal.OneGap.Residual
#print axioms AdalyFormal.OneGap.ThinTori
#print axioms AdalyFormal.OneGap.instIneq_mono
