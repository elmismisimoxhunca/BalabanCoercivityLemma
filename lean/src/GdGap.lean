import D2Cons

/-!
# GdGap -- what the invertibility guard `IsUnit Ginv` of `P428Target8SG` does and does not cover.

`genFormS` is built from FOUR `Ring.inverse` calls: `G = Ginv⁻¹` and `(Q G Q*)⁻¹` (both inside `H`, hence inside `G₁inv`), `G₁ = G₁inv⁻¹` and `(Q G₁ Q*)⁻¹`.
(The prosecutor's `Fourth.lean` shows `(Q G Q*)⁻¹` is subsumed by `WellDefAt`.)
The guard of `InstIneqSG` (lane `d1_literal_20261018`, `D2Cons.lean`) only asks `IsUnit Ginv`.
This module proves, for the actual data `dataS` / `G1invS` / `NmatS`:

* `genFormS_collapse_N`, `genFormS_collapse_G1inv`: if `N = Q G₁ Q*` or `G₁inv` is not a unit,
  `genFormS B = -a ⟨B,B⟩` (the `Ring.inverse` junk value), exactly as for `Ginv` (`genFormS_collapse`).
* `gap_of_instIneqSG`: the guarded inequality at a configuration with a positive-energy test field
  FORCES `IsUnit G₁inv ∧ IsUnit N` there (`GapAt`).
* `instIneqSG_iff`: `InstIneqSG ↔ GapAt ∧ InstIneqSG2`, with `InstIneqSG2` the inequality under the FULL guard.
* `SG_forces_gap_slab`: `P428Target8SG selAll sJ` forces `GapAt` at EVERY in-class configuration of
  the NV slab family, for every large `m`, `R` (ell = 2, a = 1, k = 2).
No claim is made here that `GapAt` fails or holds; that is the residual.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

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
open AdalyFormal.D1Literal

/-! ### 1. junk collapse when `N = Q G₁ Q*` or `G₁inv` is not a unit -/

theorem genFormS_collapse_N (sD sJ : PlaqSel) (P : IngrBParams) (h : ¬ IsUnit (GenS.NmatS sD sJ P))
    (B : BondFnL2 P.Lu) :
    GenS.genFormS sD sJ P B = -P.a * ⟪B, B⟫ := by
  have hH : H1inS sD sJ P = 0 := by
    unfold H1inS BaseDataS.H1
    have e : (((dataS sD sJ P).Q.comp ((dataS sD sJ P).G1 (G1invS sD sJ P))).comp (dataS sD sJ P).Qs)
        = GenS.NmatS sD sJ P := rfl
    rw [e, Ring.inverse_non_unit _ h]
    simp only [ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp]
  unfold GenS.genFormS GenS.firstTermS
  rw [hH, Ring.inverse_non_unit _ h]
  simp

theorem genFormS_collapse_G1inv (sD sJ : PlaqSel) (P : IngrBParams) (h : ¬ IsUnit (G1invS sD sJ P))
    (B : BondFnL2 P.Lu) :
    GenS.genFormS sD sJ P B = -P.a * ⟪B, B⟫ := by
  have hG1 : (dataS sD sJ P).G1 (G1invS sD sJ P) = 0 := by
    unfold BaseDataS.G1
    exact Ring.inverse_non_unit _ h
  have hN : GenS.NmatS sD sJ P = 0 := by
    unfold GenS.NmatS
    rw [hG1]
    simp only [ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp]
  have hH : H1inS sD sJ P = 0 := by
    unfold H1inS BaseDataS.H1
    rw [hG1]
    simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  unfold GenS.genFormS GenS.firstTermS
  rw [hN, hH, Ring.inverse_zero]
  simp

/-! ### 2. the guard gap -/

/-- the three unit conditions `Ginv`, `G1inv`, `Q G1 Q*` (which cover all four inverses of the print's right-hand side) hold. -/
def WellDefAt (sD sJ : PlaqSel) (P : IngrBParams) : Prop :=
  IsUnit (dataS sD sJ P).Ginv ∧ IsUnit (G1invS sD sJ P) ∧ IsUnit (GenS.NmatS sD sJ P)

/-- the guard gap: `Ginv` a unit already forces `G₁inv` and `Q G₁ Q*` to be units. -/
def GapAt (sD sJ : PlaqSel) (P : IngrBParams) : Prop :=
  IsUnit (dataS sD sJ P).Ginv → IsUnit (G1invS sD sJ P) ∧ IsUnit (GenS.NmatS sD sJ P)

/-- the inequality asserted under the FULL guard (the three unit conditions of `WellDefAt`, covering all four inverses). -/
def InstIneqSG2 (sD sJ : PlaqSel) (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) : Prop :=
  WellDefAt sD sJ (gparams ell k Lu hell S U a Lam) → InstIneqS sD sJ ell k hell a Lu γ₀ S Lam U

theorem instIneqSG2_of_SG (sD sJ : PlaqSel) (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (γ₀ : ℝ) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (h : InstIneqSG sD sJ ell k hell a Lu γ₀ S Lam U) : InstIneqSG2 sD sJ ell k hell a Lu γ₀ S Lam U :=
  fun hw => h hw.1

/-- a junk value contradicts the inequality when a positive-energy test field exists. -/
theorem not_InstIneqS_of_collapse (sD sJ : PlaqSel) (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 ≤ a)
    (Lu : PeriodicLatticeExtent) (γ₀ : ℝ) (hγ : 0 < γ₀)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (hcol : ∀ B : BondFnL2 Lu, GenS.genFormS sD sJ (gparams ell k Lu hell S U a Lam) B = -a * ⟪B, B⟫)
    (Bt : Bond Lu → SuTwo) (h1 : OnLambdaTildeIn Lam ell Bt) (h2 : OnLambdaT Lam Bt)
    (hE : 0 < bondEnergy Bt) :
    ¬ InstIneqS sD sJ ell k hell a Lu γ₀ S Lam U := by
  intro hI
  have h := hI Bt h1 h2
  rw [hcol] at h
  have hB : 0 ≤ ⟪(WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt) : BondFnL2 Lu),
      WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt)⟫ := real_inner_self_nonneg
  nlinarith [mul_pos hγ hE, mul_nonneg ha hB]

theorem gap_of_instIneqSG (sD sJ : PlaqSel) (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 ≤ a)
    (Lu : PeriodicLatticeExtent) (γ₀ : ℝ) (hγ : 0 < γ₀)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (Bt : Bond Lu → SuTwo) (h1 : OnLambdaTildeIn Lam ell Bt) (h2 : OnLambdaT Lam Bt)
    (hE : 0 < bondEnergy Bt)
    (hI : InstIneqSG sD sJ ell k hell a Lu γ₀ S Lam U) :
    GapAt sD sJ (gparams ell k Lu hell S U a Lam) := by
  intro hg
  have hI' := hI hg
  have ha' : (gparams ell k Lu hell S U a Lam).a = a := rfl
  constructor
  · by_contra hn
    refine not_InstIneqS_of_collapse sD sJ ell k hell a ha Lu γ₀ hγ S Lam U (fun B => ?_) Bt h1 h2 hE hI'
    have := genFormS_collapse_G1inv sD sJ (gparams ell k Lu hell S U a Lam) hn B
    rwa [ha'] at this
  · by_contra hn
    refine not_InstIneqS_of_collapse sD sJ ell k hell a ha Lu γ₀ hγ S Lam U (fun B => ?_) Bt h1 h2 hE hI'
    have := genFormS_collapse_N sD sJ (gparams ell k Lu hell S U a Lam) hn B
    rwa [ha'] at this

theorem instIneqSG_of_gap (sD sJ : PlaqSel) (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (γ₀ : ℝ) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (hgap : GapAt sD sJ (gparams ell k Lu hell S U a Lam))
    (h2 : InstIneqSG2 sD sJ ell k hell a Lu γ₀ S Lam U) :
    InstIneqSG sD sJ ell k hell a Lu γ₀ S Lam U :=
  fun hg => h2 ⟨hg, hgap hg⟩

/-- **decomposition**: with a positive-energy test field, the guarded inequality is the conjunction of the gap and the
inequality under the full guard. -/
theorem instIneqSG_iff (sD sJ : PlaqSel) (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 ≤ a)
    (Lu : PeriodicLatticeExtent) (γ₀ : ℝ) (hγ : 0 < γ₀)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (Bt : Bond Lu → SuTwo) (h1 : OnLambdaTildeIn Lam ell Bt) (h2 : OnLambdaT Lam Bt)
    (hE : 0 < bondEnergy Bt) :
    InstIneqSG sD sJ ell k hell a Lu γ₀ S Lam U ↔
      (GapAt sD sJ (gparams ell k Lu hell S U a Lam) ∧ InstIneqSG2 sD sJ ell k hell a Lu γ₀ S Lam U) :=
  ⟨fun h => ⟨gap_of_instIneqSG sD sJ ell k hell a ha Lu γ₀ hγ S Lam U Bt h1 h2 hE h,
      instIneqSG2_of_SG sD sJ ell k hell a Lu γ₀ S Lam U h⟩,
   fun h => instIneqSG_of_gap sD sJ ell k hell a Lu γ₀ S Lam U h.1 h.2⟩

/-! ### 3. headline level: the full-guard headline, and the gap forced on the NV slab family -/

def CoercG8AtSG2 (sD sJ : PlaqSel) (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneqSG2 sD sJ ell k hell a Lu γ₀ S Lam U

/-- the headline with the FULL guard (`Ginv`, `G₁inv` and `Q G₁ Q*` all units, i.e. all four inverses honest). -/
def P428Target8SG2 (sD sJ : PlaqSel) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * (ell ^ m : ℕ) * α₀ ≤ a₀ →
          CoercG8AtSG2 sD sJ ell (ell ^ m) R k (by omega) a Lu 12 α₀ γ₀

theorem P428Target8SG.toSG2 {sD sJ : PlaqSel} (h : P428Target8SG sD sJ) : P428Target8SG2 sD sJ := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR₀⟩ := hm m hm'
  refine ⟨R₀, fun R hR => ?_⟩
  obtain ⟨hs, a₀, ha₀, γ₀, hγ, hc⟩ := hR₀ R hR
  refine ⟨hs, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ hα h12 hT S hS Lam hL U hU => ?_⟩
  exact instIneqSG2_of_SG sD sJ ell k _ a Lu γ₀ S Lam U (hc k hk Lu α₀ hα h12 hT S hS Lam hL U hU)

/-- the localised full-guard headline holds (it is implied by the proved `P428Target8`). -/
theorem localised_SG2_holds : P428Target8SG2 selIn selIn :=
  P428Target8SG.toSG2 localised_guarded_holds

/-- the guard gap at every in-class configuration of every admissible tower, for ALL real `a`, `α₀` and all `c` (far stronger than the headline needs; it is a convenient sufficient hypothesis, NOT presented as the natural reduction). -/
def GapEverywhere (sD sJ : PlaqSel) : Prop :=
  ∀ (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (c : ℕ) (α₀ : ℝ),
    TorusOK ell M Lu →
    ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)),
      ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      GapAt sD sJ (gparams ell k Lu hell S U a Lam)

/-- **decomposition at headline level (the sufficient direction).**  The full-guard headline together with the gap
everywhere gives the `IsUnit Ginv`-guarded headline. -/
theorem P428Target8SG_of_SG2_gap {sD sJ : PlaqSel} (h2 : P428Target8SG2 sD sJ) (hg : GapEverywhere sD sJ) :
    P428Target8SG sD sJ := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h2 ell hell a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR₀⟩ := hm m hm'
  refine ⟨R₀, fun R hR => ?_⟩
  obtain ⟨hs, a₀, ha₀, γ₀, hγ, hc⟩ := hR₀ R hR
  refine ⟨hs, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ hα h12 hT S hS Lam hL U hU => ?_⟩
  exact instIneqSG_of_gap sD sJ ell k _ a Lu γ₀ S Lam U
    (hg ell (ell ^ m) R k _ a Lu 12 α₀ hT S hS Lam hL U hU) (hc k hk Lu α₀ hα h12 hT S hS Lam hL U hU)

/-- **`P428Target8SG selAll sJ` forces the guard gap on the whole in-class NV slab family.**
For `ell = 2`, `a = 1`, `k = 2`, all large `m`, `R ≥ 18`: with `a₀` supplied by the statement, every in-class
configuration `U` (any `α₀ > 0` with `12 M α₀ ≤ a₀`) satisfies `GapAt`: `Ginv` a unit forces `G₁inv` and `Q G₁ Q*` units. -/
theorem SG_forces_gap_slab (sJ : PlaqSel) (h : P428Target8SG selAll sJ) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 18 ≤ R →
      ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ α₀ : ℝ, 0 < α₀ → (12 : ℝ) * (2 ^ m : ℕ) * α₀ ≤ a₀ →
        ∀ U : LinkCfg (scaleUp 2 2 (nvLu (2 ^ m) R)),
          ClassCoupled 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R) α₀ (((2 : ℕ) : ℝ) ^ 2)⁻¹ U →
            GapAt selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R) U 1 (LamN (2 ^ m) R)) := by
  obtain ⟨m₀, hm₀, hm⟩ := h 2 le_rfl 1 one_pos
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR₀⟩ := hm m hm'
  refine ⟨R₀, fun R hR hR18 => ?_⟩
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hcore⟩ := hR₀ R hR
  refine ⟨a₀, ha₀, fun α₀ hα hαS U hU => ?_⟩
  have hM : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hM2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (le_trans hm₀ hm')
  have hdvd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hell : 2 ≤ 2 := le_rfl
  have hell0 : 0 < 2 := by norm_num
  have G := slabGeo_inst (ell := 2) hell hM hdvd (show 1 ≤ R by omega)
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nv_widths (ell := 2) hell hM hR18
  have hN : ∀ μ, scaleUp 2 2 (nvLu (2 ^ m) R) μ + 1 = nvN 2 (2 ^ m) R := fun μ => scaleUp_nv hell0 hM μ
  have hAdm : Admissible 2 (2 ^ m) R 2 (SlabNv 2 (2 ^ m) R) := slab3_admissible G hN
  have hineq := hcore 2 (by norm_num) (nvLu (2 ^ m) R) α₀ hα (by simpa using hαS) (torusOK_nv hell hdvd hM)
    (SlabNv 2 (2 ^ m) R) hAdm (LamN (2 ^ m) R) (lambdaOK2_nv hell hdvd hM (show 1 ≤ R by omega)) U hU
  obtain ⟨hB1, hB2, hB3, hB4⟩ := BseedNv_props (R := R) hell hdvd hM
  exact gap_of_instIneqSG selAll sJ 2 2 hell0 1 zero_le_one (nvLu (2 ^ m) R) γ₀ hγ (SlabNv 2 (2 ^ m) R)
    (LamN (2 ^ m) R) U _ hB1 hB2 hB3 hineq

/-- **what would decide the guarded literal reading negatively.**  If for every large `m`, `R ≥ 18` and every smallness
`α₀ > 0` there is an in-class configuration of the NV slab with `Ginv` a unit but `G₁inv` or `Q G₁ Q*` not a unit, then
`P428Target8SG selAll sJ` is false.  (No such configuration is exhibited in this lane.) -/
theorem not_SG_of_gapfail (sJ : PlaqSel)
    (hfail : ∀ m : ℕ, 1 ≤ m → ∀ R : ℕ, 18 ≤ R → ∀ α₀ : ℝ, 0 < α₀ →
      ∃ U : LinkCfg (scaleUp 2 2 (nvLu (2 ^ m) R)),
        ClassCoupled 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R) α₀ (((2 : ℕ) : ℝ) ^ 2)⁻¹ U ∧
          ¬ GapAt selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R) U 1 (LamN (2 ^ m) R))) :
    ¬ P428Target8SG selAll sJ := by
  intro h
  obtain ⟨m₀, hm₀, hm⟩ := SG_forces_gap_slab sJ h
  obtain ⟨R₀, hR₀⟩ := hm m₀ le_rfl
  have hR18 : 18 ≤ max R₀ 18 := le_max_right _ _
  obtain ⟨a₀, ha₀, hall⟩ := hR₀ (max R₀ 18) (le_max_left _ _) hR18
  have hM : (0 : ℝ) < ((2 ^ m₀ : ℕ) : ℝ) := by positivity
  obtain ⟨α₀, hα₀, hαle⟩ : ∃ α₀ : ℝ, 0 < α₀ ∧ (12 : ℝ) * ((2 ^ m₀ : ℕ) : ℝ) * α₀ ≤ a₀ :=
    ⟨a₀ / (12 * ((2 ^ m₀ : ℕ) : ℝ)), by positivity, by field_simp; exact le_refl _⟩
  obtain ⟨U, hU, hnU⟩ := hfail m₀ hm₀ (max R₀ 18) hR18 α₀ hα₀
  exact hnU (hall α₀ hα₀ hαle U hU)

#print axioms genFormS_collapse_N
#print axioms instIneqSG2_of_SG
#print axioms not_InstIneqS_of_collapse
#print axioms instIneqSG_of_gap
#print axioms P428Target8SG.toSG2
#print axioms not_SG_of_gapfail
#print axioms genFormS_collapse_G1inv
#print axioms gap_of_instIneqSG
#print axioms instIneqSG_iff
#print axioms localised_SG2_holds
#print axioms P428Target8SG_of_SG2_gap
#print axioms SG_forces_gap_slab

end AdalyFormal.D1Guarded
