import D2Final
import D1PGen

/-!
# D2Cons -- consequences for the both-endpoint reading, and the (undecided) invertibility-guarded literal statement.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NonVac
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- the localised headline holds, the both-endpoint sandwich of the all-plaquette `Δ` fails. -/
theorem localised_holds_both_fails : P428Target8S selIn selIn ∧ ¬ P428Target8LiteralBoth :=
  ⟨AdalyFormal.M2RightInv.p428Target8, not_P428Target8LiteralBoth⟩

/-- **junk-free form (both-endpoint sandwich).**  `ell ≥ 2`, `ell ∣ M`, `R ≥ 18`, `0 ≤ a`, `29 a < 12`: at the in-class `U_π` the masked literal quadratic form `G⁻¹` on `E₀` is negative somewhere. -/
theorem both_Ginv_indefinite (sJ : PlaqSel) {ell M R : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 18 ≤ R)
    {a : ℝ} (ha : 0 ≤ a) (ha' : 29 * a < 12) {α₀ : ℝ} (hα : 0 < α₀) :
    ClassCoupled ell M 12 2 (SlabNv ell M R) α₀ (((ell : ℝ)) ^ 2)⁻¹ (Uth ((SlabNv ell M R).Om 0) Real.pi) ∧
      ∃ v : ↥(bondSupp (geomOf ell 2 (SlabNv ell M R))),
        ⟪v, (dataM selAll sJ bothSel (gparams ell 2 (nvLu M R) (by omega) (SlabNv ell M R)
            (Uth ((SlabNv ell M R).Om 0) Real.pi) a (LamN M R))).Ginv v⟫ < 0 := by
  have hell0 : 0 < ell := by omega
  have G := slabGeo_inst (ell := ell) hell hM hdvd (show 1 ≤ R by omega)
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nv_widths (ell := ell) hell hM hR
  have hN : ∀ μ, scaleUp ell 2 (nvLu M R) μ + 1 = nvN ell M R := fun μ => scaleUp_nv hell0 hM μ
  have hAdm : Admissible ell M R 2 (SlabNv ell M R) := slab3_admissible G hN
  have hcov : CoversOm0p ell M 12 2 (SlabNv ell M R) := slab3_coversp G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  have hH := slabH_nv hell hdvd hM hR
  have hellM : ell ≤ M := Nat.le_of_dvd hM hdvd
  have hroom : 17 * ell ≤ R * M := by nlinarith
  have hηpos : (0 : ℝ) < (((ell : ℝ)) ^ 2)⁻¹ := inv_pos.mpr (pow_pos (by exact_mod_cast hell0) 2)
  refine ⟨⟨hcov, perCubeRegular2_of_one_on_om0 _ hAdm.1 hα hM (by norm_num) hell0 hηpos _
    (fun e he _ => Uth_in _ _ e he)⟩, ?_⟩
  exact FthM_both_pi_neg sJ hell0 a (LamN M R) hAdm hell hroom hH ha ha'
    AdalyFormal.Balaban.CovariantOperators.suTwoWitness AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero

/-! ### the invertibility-guarded literal statement (STATED, neither proved nor refuted in this lane) -/

/-- the inequality asserted only where the assembled `Ginv` is a unit (a weakening of `InstIneqS`). -/
def InstIneqSG (sD sJ : PlaqSel) (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) : Prop :=
  IsUnit (dataS sD sJ (gparams ell k Lu hell S U a Lam)).Ginv → InstIneqS sD sJ ell k hell a Lu γ₀ S Lam U

def CoercG8AtSG (sD sJ : PlaqSel) (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneqSG sD sJ ell k hell a Lu γ₀ S Lam U

/-- the headline with `Δ`, `J` selectors and the inequality guarded by `IsUnit Ginv`. -/
def P428Target8SG (sD sJ : PlaqSel) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * (ell ^ m : ℕ) * α₀ ≤ a₀ →
          CoercG8AtSG sD sJ ell (ell ^ m) R k (by omega) a Lu 12 α₀ γ₀

/-- the unguarded statement implies the guarded one (for any selectors). -/
theorem P428Target8S.toGuard {sD sJ : PlaqSel} (h : P428Target8S sD sJ) : P428Target8SG sD sJ := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR₀⟩ := hm m hm'
  refine ⟨R₀, fun R hR => ?_⟩
  obtain ⟨hs, a₀, ha₀, γ₀, hγ, hc⟩ := hR₀ R hR
  refine ⟨hs, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ hα h12 hT S hS Lam hL U hU _ => ?_⟩
  exact hc k hk Lu α₀ hα h12 hT S hS Lam hL U hU

/-- the localised guarded headline holds (consequence of `P428Target8`). -/
theorem localised_guarded_holds : P428Target8SG selIn selIn := P428Target8S.toGuard AdalyFormal.M2RightInv.p428Target8

#print axioms both_Ginv_indefinite
#print axioms localised_holds_both_fails
#print axioms localised_guarded_holds

end AdalyFormal.D1Literal
