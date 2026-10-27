import M1A
import MC4
import ZT5D2

/-!
# M1B -- the M1 STATEMENT against the r8 contract (node S-stmt; M1 lane B, 2026-10-13)

M1 = proper admissible towers (`Ω₀ ≠` torus allowed), a NON-FLAT `U` in ONE global gauge with STRATUM-SCALED smallness:
`U^g = exp(iηA)` on every bond, `A` Hermitian-traceless, and on a bond / gradient pair / `∂*∂` stencil all of whose bonds have
both-endpoint stratum `≥ j` (`bstrat`, M1A):
  `|A| < f M α₀ (ell^j η)⁻¹`,  `|η⁻¹ ∇A| < f M α₀ (ell^j η)⁻²`,  `|∂^{η*}∂^η A| < f M α₀ (ell^j η)⁻³`
(`M1Bounds`), i.e. the three clauses of the printed per-cube class `PerCubeRegular2` with the cube index replaced by the local stratum
(Lean units, `η = ell^-k`: link angle `< f M α₀ ell^-j` on stratum `j`; plan §1.1 of `compute/plan_m1m2_20261012/PLAN.md`).  Conclusion: the r8 `InstIneq` with `γ₀` chosen
before `k` (k-uniform).
* `M1Core` / `M1Target`: the M1 inner claim / outer quantification, with the headline's coverage `CoversOm0p 12` on the tower.
* `M1CoreAll`: the same over EVERY admissible tower (no coverage hypothesis) -- the plan §1.1 sketch.  `M1CoreAll.toCore`.
* `M1Core_of_headline : P428Genuine8 ell M R hell a → M1Core ell M R hell a`, `M1Target_of_target : P428Target8 → M1Target`
  (M1 is a special case of the frozen headline; the bridge is `perCube_of_M1`, a pure restriction).
* `M1CoreDL` (M1 modulo the D-layer: stratified `hD2`, `hJ` = `DLayerStrat`, tolerances chosen by the prover), `DLayerObligation`,
  `M1Core_of_DL : M1CoreDL → DLayerObligation → M1Core`, and `M1CoreDL_of_M1Core`.
Controls: `m1Regular_of_global` / `global_of_m1Regular_full` (on the full tower M1's regime IS M0's `GlobalRegular2`),
`M0Core_of_M1Core` (M1 extends M0), `dlayerStrat_of_dlayer_full` (M0's `DLayer` gives `DLayerStrat` on the full tower),
`ufield_M1Regular` + `m1_hyps_nonvacuous` (every hypothesis of `M1Core` at a PROPER tower with a non-flat, not-pure-gauge `U`),
`weights_bite` (the same spike is admissible on a stratum-0 bond and NOT on a stratum-1 bond, for the bound read off `M1Bounds`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.M0Corollary (GlobalRegular2 M0Core fullTower_admissible univ_lambdaOK2 fullTower_coversp DLayer)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.M0Finish (PU)

variable {L : PeriodicLatticeExtent}

/-! ## 1. the stratum-scaled one-gauge regime -/

/-- the four bonds read by the curl `curlA η A x a b` all have stratum `≥ j`. -/
def StratReads (S : Tower L) (k j : ℕ) (x : PeriodicLatticeSite L) (a b : Fin 3) : Prop :=
  j ≤ bstrat S k (periodicLatticeShift x a, b) ∧ j ≤ bstrat S k (x, b) ∧
  j ≤ bstrat S k (periodicLatticeShift x b, a) ∧ j ≤ bstrat S k (x, a)

/-- **stratum-scaled bounds on a field `A`** (the three printed clauses (3.35)+(3.36), cube index `j` replaced by any `j` below the
local both-endpoint stratum of every bond the clause reads). -/
def M1Bounds (S : Tower L) (ell M f k : ℕ) (α₀ η : ℝ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (∀ e : Bond L, HT (A e)) ∧
  (∀ (e : Bond L) (j : ℕ), j ≤ bstrat S k e →
      frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ∧
  (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L) (j : ℕ),
      j ≤ bstrat S k (x, ν) → j ≤ bstrat S k (periodicLatticeShift x μ, ν) →
      frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
        < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) ∧
  (∀ (μ : Fin 3) (x : PeriodicLatticeSite L) (j : ℕ),
      (∀ ν : Fin 3, ν ≠ μ → StratReads S k j (periodicLatticeShiftBack x ν) ν μ ∧ StratReads S k j x ν μ) →
      frobNorm (ddA η A x μ) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 3))

/-- **M1 regime**: ONE global gauge `g`, ONE field `A` on the whole torus, `U^g = exp(iηA)`, stratum-scaled bounds. -/
def M1Regular (ell M f k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
        = NormedSpace.exp (((η : ℂ) * Complex.I) • A e)) ∧
    M1Bounds S ell M f k α₀ η A

/-- sites of a class cube of index `j` lie in `Ω_j`. -/
theorem classCube_sub {ell M R f k : ℕ} {S : Tower L} (hA : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (hq : IsClassCube ell M f k S sites j) : sites ⊆ S.Om j := by
  intro x hx
  rcases hq.1.2.2.1 hx with h | h
  · exact h.1
  · exact hA.1 j h.1

/-- a bond of a class cube of index `j` has both-endpoint stratum `≥ j`. -/
theorem le_bstrat_of_cubeBond {ell M R f k : ℕ} {S : Tower L} (hA : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (hq : IsClassCube ell M f k S sites j) {e : Bond L}
    (he : CubeBond sites e) : j ≤ bstrat S k e :=
  le_bstrat_of_mem hq.1.1 e (classCube_sub hA hq he.1) (classCube_sub hA hq he.2)

/-- **the bridge (`perCube_of_M1`)**: the M1 regime restricts to the printed per-cube class on every admissible tower
(pure restriction: every class cube of index `j` reads only bonds of stratum `≥ j`). -/
theorem perCube_of_M1 {ell M R f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} (hA : Admissible ell M R k S)
    (h : M1Regular ell M f k S α₀ η U) : PerCubeRegular2 ell M f k S α₀ η U := by
  obtain ⟨g, A, hU, hHT, h1, h2, h3⟩ := h
  intro sites j hq
  have hb := fun e (he : CubeBond sites e) => le_bstrat_of_cubeBond hA hq he
  refine ⟨g, A, fun e he => ⟨hHT e, hU e, h1 e j (hb e he)⟩, fun μ ν x hx hy => h2 μ ν x j (hb _ hx) (hb _ hy), ?_⟩
  intro μ x hr
  refine h3 μ x j (fun ν hν => ?_)
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩ := hr ν hν
  exact ⟨⟨hb _ a1, hb _ a2, hb _ a3, hb _ a4⟩, ⟨hb _ b1, hb _ b2, hb _ b3, hb _ b4⟩⟩

/-! ## 2. the M1 statement -/

/-- **M1 inner claim** (ell, M, R, a fixed by the consumer exactly as in the headline; towers with the headline's coverage). -/
def M1Core (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
    TorusOK ell M Lu →
    ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S → CoversOm0p ell M 12 k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      InstIneq ell k hell a Lu γ₀ S Lam U

/-- **M1 over every admissible tower** (no coverage hypothesis; plan §1.1). -/
def M1CoreAll (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
    TorusOK ell M Lu →
    ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      InstIneq ell k hell a Lu γ₀ S Lam U

/-- the outer quantification, as the headline's: prover picks `m₀` and `R₀`. -/
def M1Target : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → M1Core ell (ell ^ m) R (by omega) a

theorem M1CoreAll.toCore {ell M R : ℕ} {hell : 0 < ell} {a : ℝ} (h : M1CoreAll ell M R hell a) :
    M1Core ell M R hell a := by
  obtain ⟨a₀, ha₀, γ₀, hγ₀, hall⟩ := h
  exact ⟨a₀, ha₀, γ₀, hγ₀, fun k hk Lu α₀ hα hsm hT S hS _ Lam hL U hU => hall k hk Lu α₀ hα hsm hT S hS Lam hL U hU⟩

/-- **M1 is a consequence of the frozen headline** (for every `R`). -/
theorem M1Core_of_headline {ell M R : ℕ} {hell : 0 < ell} {a : ℝ} (h : P428Genuine8 ell M R hell a) :
    M1Core ell M R hell a := by
  obtain ⟨-, a₀, ha₀, γ₀, hγ₀, hall⟩ := h
  exact ⟨a₀, ha₀, γ₀, hγ₀, fun k hk Lu α₀ hα hsm hT S hS hcov Lam hL U hU =>
    hall k hk Lu α₀ hα hsm hT S hS Lam hL U ⟨hcov, perCube_of_M1 hS hU⟩⟩

theorem M1Target_of_target (h : P428Target8) : M1Target := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hm'
  exact ⟨R₀, fun R hR' => M1Core_of_headline (hR R hR')⟩

/-! ## 3. M1 modulo the D-layer: stratified `hD2`, `hJ` -/

/-- stratum-weighted squared norm of a fine bond field: `Σ_b ell^{-2 bstrat b} |A_b|²` (plan §1.2 notation `‖A‖_w²`). -/
noncomputable def wnormSq (S : Tower L) (ell k : ℕ) (A : BondFnL2 L) : ℝ :=
  ∑ b : Bond L, (((ell : ℝ) ^ bstrat S k b)⁻¹) ^ 2 * ‖(WithLp.ofLp A) b‖ ^ 2

/-- **stratified D-layer premises** at one point (plan D1 weighted form of M0's `hD2`; `hJ` verbatim as M0's, scale-free). -/
def DLayerStrat (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (ε2s εJ : ℝ) : Prop :=
  (∀ x : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
      |⟪x, (gparams ell k Lu hell S U a Lam).data.Delta2 (gparams ell k Lu hell S U a Lam).data_laws x⟫|
        ≤ ε2s * wnormSq S ell k (x : BondFnL2 (scaleUp ell k Lu))) ∧
  ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
    |⟪(gparams ell k Lu hell S U a Lam).H1in ((gparams ell k Lu hell S U a Lam).D2in
        (WithLp.toLp 2 (Cop Lam (gparams ell k Lu hell S U a Lam).Q1 Bt))), (gparams ell k Lu hell S U a Lam).Jf⟫|
      ≤ εJ * ‖(WithLp.toLp 2 (Cop Lam (gparams ell k Lu hell S U a Lam).Q1 Bt) : BondFnL2 Lu)‖ ^ 2

/-- **M1 modulo the D-layer.**  The prover chooses `a₀, γ₀` and the D-layer tolerances `ε2s, εJ > 0` before every configuration. -/
def M1CoreDL (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ ε2s : ℝ, 0 < ε2s ∧ ∃ εJ : ℝ, 0 < εJ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
    TorusOK ell M Lu →
    ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S → CoversOm0p ell M 12 k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      DLayerStrat ell k Lu hell S U a Lam ε2s εJ →
      InstIneq ell k hell a Lu γ₀ S Lam U

/-- **the D-layer obligation** (lanes D1-D5): for EVERY pair of tolerances, a small enough `a₀` forces the stratified D-layer bounds
on the whole M1 regime. -/
def DLayerObligation (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∀ ε2s : ℝ, 0 < ε2s → ∀ εJ : ℝ, 0 < εJ → ∃ a₁ : ℝ, 0 < a₁ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₁ →
    TorusOK ell M Lu →
    ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S → CoversOm0p ell M 12 k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      DLayerStrat ell k Lu hell S U a Lam ε2s εJ

theorem M1Core_of_DL {ell M R : ℕ} {hell : 0 < ell} {a : ℝ} (h : M1CoreDL ell M R hell a)
    (hD : DLayerObligation ell M R hell a) : M1Core ell M R hell a := by
  obtain ⟨a₀, ha₀, γ₀, hγ₀, ε2s, hε2s, εJ, hεJ, hall⟩ := h
  obtain ⟨a₁, ha₁, hD'⟩ := hD ε2s hε2s εJ hεJ
  refine ⟨min a₀ a₁, lt_min ha₀ ha₁, γ₀, hγ₀, fun k hk Lu α₀ hα hsm hT S hS hcov Lam hL U hU => ?_⟩
  exact hall k hk Lu α₀ hα (hsm.trans (min_le_left _ _)) hT S hS hcov Lam hL U hU
    (hD' k hk Lu α₀ hα (hsm.trans (min_le_right _ _)) hT S hS hcov Lam hL U hU)

theorem M1CoreDL_of_M1Core {ell M R : ℕ} {hell : 0 < ell} {a : ℝ} (h : M1Core ell M R hell a) :
    M1CoreDL ell M R hell a := by
  obtain ⟨a₀, ha₀, γ₀, hγ₀, hall⟩ := h
  exact ⟨a₀, ha₀, γ₀, hγ₀, 1, one_pos, 1, one_pos,
    fun k hk Lu α₀ hα hsm hT S hS hcov Lam hL U hU _ => hall k hk Lu α₀ hα hsm hT S hS hcov Lam hL U hU⟩

/-! ## 4. controls: M1 on the full tower is M0 -/

theorem strat_fullTower (ell k : ℕ) (Lu : PeriodicLatticeExtent) (x : PeriodicLatticeSite (scaleUp ell k Lu)) :
    strat (fullTower ell k Lu) k x = k :=
  le_antisymm (strat_le _ k x) (le_strat_of_mem le_rfl (by simp [fullTower]))

theorem bstrat_fullTower (ell k : ℕ) (Lu : PeriodicLatticeExtent) (b : Bond (scaleUp ell k Lu)) :
    bstrat (fullTower ell k Lu) k b = k := by
  unfold bstrat; rw [strat_fullTower, strat_fullTower, min_self]

/-- `F < c X`, `X ≤ Y`, `0 ≤ F`, `0 ≤ X` ⟹ `F < c Y`. -/
theorem lt_of_lt_mono {F c X Y : ℝ} (hF : 0 ≤ F) (hX : 0 ≤ X) (h : F < c * X) (hXY : X ≤ Y) : F < c * Y := by
  have hc : 0 < c := by
    by_contra hc; push Not at hc
    have : c * X ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hX
    linarith
  linarith [mul_le_mul_of_nonneg_left hXY hc.le]

/-- the scale `(ell^j η)⁻¹` is antitone in `j` (`ell ≥ 1`, `η > 0`). -/
theorem scale_anti {ell : ℕ} (hell : 1 ≤ ell) {η : ℝ} (hη : 0 < η) {i j : ℕ} (hij : i ≤ j) (n : ℕ) :
    (((ell : ℝ) ^ j * η)⁻¹) ^ n ≤ (((ell : ℝ) ^ i * η)⁻¹) ^ n := by
  have hell' : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpi : 0 < (ell : ℝ) ^ i * η := by positivity
  have hle : (ell : ℝ) ^ i * η ≤ (ell : ℝ) ^ j * η :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hell' hij) hη.le
  exact pow_le_pow_left₀ (by positivity) ((inv_le_inv₀ (by positivity) hpi).mpr hle) n

/-- **control: M0's regime is M1's regime on the full tower.** -/
theorem m1Regular_of_global {ell M f k : ℕ} {Lu : PeriodicLatticeExtent} {α₀ η : ℝ} (hell : 1 ≤ ell) (hη : 0 < η)
    {U : LinkCfg (scaleUp ell k Lu)} (h : GlobalRegular2 ell M f k α₀ η U) :
    M1Regular ell M f k (fullTower ell k Lu) α₀ η U := by
  obtain ⟨g, A, h1, h2, h3⟩ := h
  have hnn : ∀ n : ℕ, 0 ≤ (((ell : ℝ) ^ k * η)⁻¹) ^ n := fun n => by positivity
  refine ⟨g, A, fun e => (h1 e).2.1, fun e => (h1 e).1, ?_, ?_, ?_⟩
  · intro e j hj
    rw [bstrat_fullTower] at hj
    exact lt_of_lt_mono (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _) (hnn 1) (h1 e).2.2 (scale_anti hell hη hj 1)
  · intro μ ν x j hj _
    rw [bstrat_fullTower] at hj
    exact lt_of_lt_mono (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _) (hnn 2) (h2 μ ν x) (scale_anti hell hη hj 2)
  · intro μ x j hr
    have hj : j ≤ k := by
      have := (hr (μ + 1) (by fin_cases μ <;> decide)).2.2.2.2
      rwa [bstrat_fullTower] at this
    exact lt_of_lt_mono (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _) (hnn 3) (h3 μ x) (scale_anti hell hη hj 3)

/-- **control (converse): on the full tower M1's regime gives M0's** (instantiate `j = k`). -/
theorem global_of_m1Regular_full {ell M f k : ℕ} {Lu : PeriodicLatticeExtent} {α₀ η : ℝ}
    {U : LinkCfg (scaleUp ell k Lu)} (h : M1Regular ell M f k (fullTower ell k Lu) α₀ η U) :
    GlobalRegular2 ell M f k α₀ η U := by
  obtain ⟨g, A, hU, hHT, h1, h2, h3⟩ := h
  refine ⟨g, A, fun e => ⟨hHT e, hU e, h1 e k (by rw [bstrat_fullTower])⟩,
    fun μ ν x => h2 μ ν x k (by rw [bstrat_fullTower]) (by rw [bstrat_fullTower]), fun μ x => h3 μ x k ?_⟩
  intro ν _
  simp only [StratReads, bstrat_fullTower, le_refl, and_self]

/-- **control: M1 extends M0** (`M1Core ⟹ M0Core`, at the full tower with `Λ = ` torus). -/
theorem M0Core_of_M1Core {ell M R : ℕ} {hell : 0 < ell} {a : ℝ} (hM : 0 < M) (h : M1Core ell M R hell a) :
    M0Core ell M hell a := by
  obtain ⟨a₀, ha₀, γ₀, hγ₀, hall⟩ := h
  refine ⟨a₀, ha₀, γ₀, hγ₀, fun k hk Lu hT α₀ hα hsm U hU => ?_⟩
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  exact hall k hk Lu α₀ hα hsm hT (fullTower ell k Lu) (fullTower_admissible ell M R k hell hk Lu hT.2.2)
    (fullTower_coversp ell M 12 k hell hM (by norm_num) Lu hT.2.2) Set.univ (univ_lambdaOK2 ell M R k hell Lu) U
    (m1Regular_of_global hell hη hU)

/-- **control: M0's D-layer premises give the stratified ones on the full tower** (`wnormSq = ell^{-2k} ‖·‖²` there). -/
theorem dlayerStrat_of_dlayer_full {ell k : ℕ} {Lu : PeriodicLatticeExtent} {hell : 0 < ell}
    {U : LinkCfg (scaleUp ell k Lu)} {a : ℝ} {Lam : Set (PeriodicLatticeSite Lu)} {ε2s εJ : ℝ}
    (h : DLayer ell k Lu hell U a Lam ε2s εJ) :
    DLayerStrat ell k Lu hell (fullTower ell k Lu) U a Lam ε2s εJ := by
  obtain ⟨hD, hJ⟩ := h
  refine ⟨fun x => ?_, hJ⟩
  have hw : wnormSq (fullTower ell k Lu) ell k (x : BondFnL2 (scaleUp ell k Lu))
      = ((((ell : ℝ) ^ k)⁻¹) ^ 2) * ‖x‖ ^ 2 := by
    unfold wnormSq
    simp only [bstrat_fullTower]
    rw [← Finset.mul_sum]
    congr 1
    exact (PiLp.norm_sq_eq_of_L2 _ (x : BondFnL2 (scaleUp ell k Lu))).symm
  rw [hw]
  have h2 : ‖(gparams ell k Lu hell (fullTower ell k Lu) U a Lam).data.Delta2
      (gparams ell k Lu hell (fullTower ell k Lu) U a Lam).data_laws‖ ≤ ε2s * ((((ell : ℝ) ^ k)⁻¹) ^ 2) := by
    have h' := hD
    rw [div_eq_mul_inv, ← inv_pow] at h'
    exact h'
  have h1 := abs_real_inner_le_norm x ((gparams ell k Lu hell (fullTower ell k Lu) U a Lam).data.Delta2
      (gparams ell k Lu hell (fullTower ell k Lu) U a Lam).data_laws x)
  have h3 := ((gparams ell k Lu hell (fullTower ell k Lu) U a Lam).data.Delta2
      (gparams ell k Lu hell (fullTower ell k Lu) U a Lam).data_laws).le_opNorm x
  have hx0 := norm_nonneg x
  have hop0 := norm_nonneg ((gparams ell k Lu hell (fullTower ell k Lu) U a Lam).data.Delta2
      (gparams ell k Lu hell (fullTower ell k Lu) U a Lam).data_laws)
  calc _ ≤ _ := h1
    _ ≤ ‖x‖ * (‖(gparams ell k Lu hell (fullTower ell k Lu) U a Lam).data.Delta2
          (gparams ell k Lu hell (fullTower ell k Lu) U a Lam).data_laws‖ * ‖x‖) := mul_le_mul_of_nonneg_left h3 hx0
    _ ≤ ‖x‖ * ((ε2s * ((((ell : ℝ) ^ k)⁻¹) ^ 2)) * ‖x‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hx0) hx0
    _ = ε2s * (((((ell : ℝ) ^ k)⁻¹) ^ 2) * ‖x‖ ^ 2) := by ring

/-! ## 5. controls: non-vacuity at a PROPER tower with a non-flat `U`; the weights bite -/

/-- every small real field gives a configuration in the M1 regime, on ANY tower (`|χ| ≤ α₀ η²/10`, `η = ell^-k`). -/
theorem ufield_M1Regular {ell M f k : ℕ} (hell : 1 ≤ ell) (hM : 1 ≤ M) (hf : 10 ≤ f) (S : Tower L) {α₀ : ℝ}
    (hα : 0 < α₀) (χ : Bond L → ℝ) (hχ : ∀ e, |χ e| ≤ α₀ * (((ell : ℝ) ^ k)⁻¹) ^ 2 / 10) :
    M1Regular ell M f k S α₀ (((ell : ℝ) ^ k)⁻¹) (Ufield (((ell : ℝ) ^ k)⁻¹) χ) := by
  set η : ℝ := ((ell : ℝ) ^ k)⁻¹ with hηdef
  have hell' : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpk : (1 : ℝ) ≤ (ell : ℝ) ^ k := one_le_pow₀ hell'
  have hη : 0 < η := by positivity
  have hη1 : η ≤ 1 := inv_le_one_of_one_le₀ hpk
  set c : ℝ := α₀ * η ^ 2 / 10 with hc
  have hc0 : 0 ≤ c := by positivity
  have hs2 : Real.sqrt 2 < 1.5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hfM : (10 : ℝ) ≤ (f : ℝ) * M := by
    have h1 : (10 : ℝ) ≤ f := by exact_mod_cast hf
    have h2 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  -- the bound at any `j ≤ k`
  have hB : ∀ j : ℕ, j ≤ k → ∀ n : ℕ, 10 * α₀ ≤ (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ n) := by
    intro j hjk n
    have hX : (1 : ℝ) ≤ ((ell : ℝ) ^ j * η)⁻¹ := by
      rw [one_le_inv₀ (by positivity)]
      have : (ell : ℝ) ^ j ≤ (ell : ℝ) ^ k := pow_le_pow_right₀ hell' hjk
      rw [hηdef]
      rw [mul_inv_le_iff₀ (by positivity)]; simpa using this
    have := one_le_pow₀ (n := n) hX
    have h1 : 10 * α₀ ≤ (f : ℝ) * M * α₀ := by nlinarith
    nlinarith
  refine ⟨fun _ => 1, fun e => χ e • sig, fun e => ?_, fun e => HT_rsmul_sig _, ?_, ?_, ?_⟩
  · rw [gauge_one]
    show NormedSpace.exp (Xm (η * χ e)) = _
    rw [smul_sig_eq]
  · intro e j hj
    have hjk : j ≤ k := hj.trans (bstrat_le S k e)
    have h1 : frobNorm (χ e • sig) ≤ c * Real.sqrt 2 := by
      rw [frobNorm_rsmul_sig]
      exact mul_le_mul_of_nonneg_right (hχ e) hs0.le
    have h2 : c * Real.sqrt 2 < 10 * α₀ := by
      have : c * Real.sqrt 2 ≤ α₀ * 1 * 1.5 / 10 := by
        rw [hc]
        have hη2 : η ^ 2 ≤ 1 := by nlinarith
        have : α₀ * η ^ 2 ≤ α₀ := by nlinarith
        nlinarith
      nlinarith
    have := hB j hjk 1
    linarith
  · intro μ ν x j hj _
    have hjk : j ≤ k := hj.trans (bstrat_le S k _)
    have e1 : (η⁻¹ : ℝ) • (χ (periodicLatticeShift x μ, ν) • sig - χ (x, ν) • sig)
        = (η⁻¹ * (χ (periodicLatticeShift x μ, ν) - χ (x, ν))) • sig := by module
    show frobNorm ((η⁻¹ : ℝ) • ((fun e => χ e • sig) (periodicLatticeShift x μ, ν)
      - (fun e => χ e • sig) (x, ν))) < _
    simp only []
    rw [e1, frobNorm_rsmul_sig]
    have hd : |χ (periodicLatticeShift x μ, ν) - χ (x, ν)| ≤ 2 * c := by
      have := abs_sub (χ (periodicLatticeShift x μ, ν)) (χ (x, ν))
      linarith [hχ (periodicLatticeShift x μ, ν), hχ (x, ν)]
    have hinv : |η⁻¹| = η⁻¹ := abs_of_pos (inv_pos.mpr hη)
    rw [abs_mul, hinv]
    have h3 : η⁻¹ * |χ (periodicLatticeShift x μ, ν) - χ (x, ν)| ≤ η⁻¹ * (2 * c) :=
      mul_le_mul_of_nonneg_left hd (inv_pos.mpr hη).le
    have h4 : η⁻¹ * (2 * c) = 2 * α₀ * η / 10 := by rw [hc]; field_simp
    have h5 : η⁻¹ * |χ (periodicLatticeShift x μ, ν) - χ (x, ν)| * Real.sqrt 2
        ≤ (2 * α₀ * η / 10) * Real.sqrt 2 := by
      rw [← h4]; exact mul_le_mul_of_nonneg_right h3 hs0.le
    have h6 : (2 * α₀ * η / 10) * Real.sqrt 2 < 10 * α₀ := by
      have hαη : α₀ * η ≤ α₀ := by nlinarith
      have := mul_le_mul_of_nonneg_left hs2.le (by positivity : 0 ≤ 2 * α₀ * η / 10)
      nlinarith
    have := hB j hjk 2
    linarith
  · intro μ x j hr
    have hjk : j ≤ k := ((hr (μ + 1) (by fin_cases μ <;> decide)).2.2.2.2).trans (bstrat_le S k _)
    show frobNorm (ddA η (fun e => χ e • sig) x μ) < _
    rw [ddA_rsmul, frobNorm_rsmul_sig]
    set SS := ∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ),
        (η⁻¹ * (χ (periodicLatticeShift (periodicLatticeShiftBack x ν) ν, μ)
            - χ (periodicLatticeShiftBack x ν, μ)
            - χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν)
            + χ (periodicLatticeShiftBack x ν, ν))
          - η⁻¹ * (χ (periodicLatticeShift x ν, μ) - χ (x, μ)
            - χ (periodicLatticeShift x μ, ν) + χ (x, ν))) with hSS
    have hterm : ∀ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ),
        |(η⁻¹ * (χ (periodicLatticeShift (periodicLatticeShiftBack x ν) ν, μ)
            - χ (periodicLatticeShiftBack x ν, μ)
            - χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν)
            + χ (periodicLatticeShiftBack x ν, ν))
          - η⁻¹ * (χ (periodicLatticeShift x ν, μ) - χ (x, μ)
            - χ (periodicLatticeShift x μ, ν) + χ (x, ν)))| ≤ η⁻¹ * (8 * c) := by
      intro ν _
      have a1 := abs_four_le (hχ (periodicLatticeShift (periodicLatticeShiftBack x ν) ν, μ))
        (hχ (periodicLatticeShiftBack x ν, μ))
        (hχ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν))
        (hχ (periodicLatticeShiftBack x ν, ν))
      have a2 := abs_four_le (hχ (periodicLatticeShift x ν, μ)) (hχ (x, μ))
        (hχ (periodicLatticeShift x μ, ν)) (hχ (x, ν))
      have hi : (0 : ℝ) < η⁻¹ := inv_pos.mpr hη
      rw [← mul_sub, abs_mul, abs_of_pos hi]
      apply mul_le_mul_of_nonneg_left _ hi.le
      have := abs_sub (χ (periodicLatticeShift (periodicLatticeShiftBack x ν) ν, μ)
            - χ (periodicLatticeShiftBack x ν, μ)
            - χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν)
            + χ (periodicLatticeShiftBack x ν, ν)) (χ (periodicLatticeShift x ν, μ) - χ (x, μ)
            - χ (periodicLatticeShift x μ, ν) + χ (x, ν))
      linarith
    have hsum : |SS| ≤ 3 * (η⁻¹ * (8 * c)) := by
      calc |SS| ≤ ∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ), |(η⁻¹ * (χ (periodicLatticeShift (periodicLatticeShiftBack x ν) ν, μ)
            - χ (periodicLatticeShiftBack x ν, μ)
            - χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν)
            + χ (periodicLatticeShiftBack x ν, ν))
          - η⁻¹ * (χ (periodicLatticeShift x ν, μ) - χ (x, μ)
            - χ (periodicLatticeShift x μ, ν) + χ (x, ν)))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ), η⁻¹ * (8 * c) :=
            Finset.sum_le_sum hterm
        _ = (Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ)).card • (η⁻¹ * (8 * c)) := by
            rw [Finset.sum_const]
        _ ≤ 3 * (η⁻¹ * (8 * c)) := by
            rw [nsmul_eq_mul]
            have hcard : (Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ)).card ≤ 3 := by
              calc _ ≤ Finset.univ.card := Finset.card_le_univ _
                _ = 3 := by simp
            have : ((Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ)).card : ℝ) ≤ 3 := by
              exact_mod_cast hcard
            have hnn : 0 ≤ η⁻¹ * (8 * c) := by positivity
            nlinarith
    have hinv : |η⁻¹| = η⁻¹ := abs_of_pos (inv_pos.mpr hη)
    rw [abs_mul, hinv]
    have h8 : η⁻¹ * |SS| ≤ η⁻¹ * (3 * (η⁻¹ * (8 * c))) :=
      mul_le_mul_of_nonneg_left hsum (inv_pos.mpr hη).le
    have h9 : η⁻¹ * (3 * (η⁻¹ * (8 * c))) = 24 * c / η ^ 2 := by field_simp; ring
    have h10 : 24 * c / η ^ 2 = 24 * α₀ / 10 := by rw [hc]; field_simp
    have h11 : η⁻¹ * |SS| * Real.sqrt 2 ≤ (24 * α₀ / 10) * Real.sqrt 2 := by
      rw [← h10, ← h9]; exact mul_le_mul_of_nonneg_right h8 hs0.le
    have h12 : (24 * α₀ / 10) * Real.sqrt 2 < 10 * α₀ := by
      have := mul_le_mul_of_nonneg_left hs2.le (by positivity : 0 ≤ 24 * α₀ / 10)
      nlinarith
    have := hB j hjk 3
    linarith

/-- **NON-VACUITY of M1's hypotheses at a PROPER tower** (`k = 1`, `ell = 2`, `M = 2 = ell^1`, `R = 6`, `TT`: `Ω₀ ≠ ` torus, both strata
nonempty; `Λ = LamT`, `Λ' ≠ ∅`): torus, admissibility, the headline's coverage, `LambdaOK2`, a NON-FLAT, NOT-pure-gauge `U` in the M1
regime, and a nonzero `B̃ ∈ Λ̃`.  The conclusion `InstIneq` is NOT proved here (that is M1). -/
theorem m1_hyps_nonvacuous {Lu Lf : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) (hLf : ∀ μ, Lf μ + 1 = 120)
    {α₀ : ℝ} (hα : 0 < α₀) (hα1 : α₀ ≤ 1 / 2) :
    TorusOK 2 2 Lu ∧ Admissible 2 2 6 1 (TT Lf) ∧ CoversOm0p 2 2 12 1 (TT Lf) ∧
    (∃ p : PeriodicLatticeSite Lf, p ∈ towerBj (TT Lf) 0) ∧
    (∃ p : PeriodicLatticeSite Lf, p ∈ towerBj (TT Lf) 1) ∧
    (∃ p : PeriodicLatticeSite Lf, p ∉ (TT Lf).Om 0) ∧
    LambdaOK2 (Lu := Lu) (Lf := Lf) 2 2 6 1 (TT Lf) (LamT Lu) ∧
    (∃ U : LinkCfg Lf, M1Regular 2 2 12 1 (TT Lf) α₀ (((2 : ℕ) : ℝ) ^ 1)⁻¹ U ∧
       ¬ ∃ g : PeriodicLatticeSite Lf → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
    (∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn (LamT Lu) 2 Bt ∧ OnLambdaT (LamT Lu) Bt ∧ 0 < bondEnergy Bt) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -, h10⟩ := proper_tower_hyps_p hLu hLf hα hα1
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, h10⟩
  set z0 : PeriodicLatticeSite Lf := fun μ => ⟨0, by have := hLf μ; omega⟩ with hz0
  have hηv : (((2 : ℕ) : ℝ) ^ 1)⁻¹ = 1 / 2 := by norm_num
  have hpos : 0 < α₀ * ((((2 : ℕ) : ℝ) ^ 1)⁻¹) ^ 2 / 10 := by rw [hηv]; positivity
  refine ⟨Ufield (((2 : ℕ) : ℝ) ^ 1)⁻¹ (spike (periodicLatticeShift z0 0, 1)
      (α₀ * ((((2 : ℕ) : ℝ) ^ 1)⁻¹) ^ 2 / 10)), ?_, ?_⟩
  · apply ufield_M1Regular (by norm_num) (by norm_num) (by norm_num) _ hα
    intro e
    unfold spike
    split_ifs
    · rw [abs_of_pos hpos]
    · simp; positivity
  · apply spike_not_pure_gauge (by have := hLf 0; omega)
    · rw [hηv]; norm_num; positivity
    · rw [hηv]; norm_num; linarith

/-- **the weights bite** (`TT`, `ell = 2`, `k = 1`, `η = 1/2`, `f M α₀ = 24 α₀`): clause 1 of `M1Bounds` at the field `A = t·σ₃` on ONE
bond allows `|A| < 48 α₀` on a stratum-0 bond and only `|A| < 24 α₀` on a stratum-1 bond: the spike of height `t = 30 α₀/√2` (so
`|A| = 30 α₀`) passes clause 1 on the stratum-0 bond `((10,0,0), direction 1)` and fails it on the stratum-1 bond `((50,0,0), direction 1)` (directions are the 0-based `Fin 3` indices). -/
theorem weights_bite {Lf : PeriodicLatticeExtent} (hLf : ∀ μ, Lf μ + 1 = 120) {α₀ : ℝ} (hα : 0 < α₀) :
    ∃ e0 e1 : Bond Lf, bstrat (TT Lf) 1 e0 = 0 ∧ bstrat (TT Lf) 1 e1 = 1 ∧
      (∀ j, j ≤ bstrat (TT Lf) 1 e0 → frobNorm ((30 * α₀ / Real.sqrt 2) • sig)
        < ((12 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * α₀ * ((((2 : ℕ) : ℝ) ^ j * (((2 : ℕ) : ℝ) ^ 1)⁻¹)⁻¹ ^ 1)) ∧
      ¬ (∀ j, j ≤ bstrat (TT Lf) 1 e1 → frobNorm ((30 * α₀ / Real.sqrt 2) • sig)
        < ((12 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * α₀ * ((((2 : ℕ) : ℝ) ^ j * (((2 : ℕ) : ℝ) ^ 1)⁻¹)⁻¹ ^ 1)) := by
  have hmk : ∀ (v : ℕ) (μ : Fin 3), v < 120 → v < Lf μ + 1 := fun v μ h => by have := hLf μ; omega
  set x0 : PeriodicLatticeSite Lf := fun μ => if μ = 0 then ⟨10, hmk 10 μ (by norm_num)⟩ else ⟨0, hmk 0 μ (by norm_num)⟩
  set x1 : PeriodicLatticeSite Lf := fun μ => if μ = 0 then ⟨50, hmk 50 μ (by norm_num)⟩ else ⟨0, hmk 0 μ (by norm_num)⟩
  have hTT : Admissible 2 2 6 1 (TT Lf) := TT2_admissible hLf
  -- the shift by `e₁` does not move coordinate 0
  have hsh : ∀ x : PeriodicLatticeSite Lf, (periodicLatticeShift x 1) 0 = x 0 := fun x => by
    simp [periodicLatticeShift]
  have hfr : frobNorm ((30 * α₀ / Real.sqrt 2) • sig) = 30 * α₀ := by
    rw [frobNorm_rsmul_sig, abs_of_pos (by positivity)]
    field_simp
  have hs0 : ∀ x : PeriodicLatticeSite Lf, (x 0).val = 10 → strat (TT Lf) 1 x = 0 := by
    intro x hx
    by_contra hne
    have h1 : 1 ≤ strat (TT Lf) 1 x := Nat.one_le_iff_ne_zero.mpr hne
    have := (le_strat_iff hTT le_rfl le_rfl x).mp h1
    simp [TT, OmB, hx] at this
  have hs1 : ∀ x : PeriodicLatticeSite Lf, (x 0).val = 50 → strat (TT Lf) 1 x = 1 := by
    intro x hx
    refine le_antisymm (strat_le _ 1 x) ((le_strat_iff hTT le_rfl le_rfl x).mpr ?_)
    simp [TT, OmB, hx]
  refine ⟨(x0, 1), (x1, 1), ?_, ?_, ?_, ?_⟩
  · unfold bstrat; rw [hs0 x0 (by simp [x0]), hs0 _ (by rw [hsh]; simp [x0])]; rfl
  · unfold bstrat; rw [hs1 x1 (by simp [x1]), hs1 _ (by rw [hsh]; simp [x1])]; rfl
  · intro j hj
    have hj0 : j = 0 := by
      have : bstrat (TT Lf) 1 (x0, 1) = 0 := by
        unfold bstrat; rw [hs0 x0 (by simp [x0]), hs0 _ (by rw [hsh]; simp [x0])]; rfl
      omega
    subst hj0
    rw [hfr]; norm_num; nlinarith
  · intro h
    have := h 1 (by unfold bstrat; rw [hs1 x1 (by simp [x1]), hs1 _ (by rw [hsh]; simp [x1])]; rfl)
    rw [hfr] at this; norm_num at this; nlinarith

#print axioms perCube_of_M1
#print axioms M1CoreAll.toCore
#print axioms M1Core_of_headline
#print axioms M1Target_of_target
#print axioms M1Core_of_DL
#print axioms M1CoreDL_of_M1Core
#print axioms m1Regular_of_global
#print axioms global_of_m1Regular_full
#print axioms M0Core_of_M1Core
#print axioms dlayerStrat_of_dlayer_full
#print axioms ufield_M1Regular
#print axioms m1_hyps_nonvacuous
#print axioms weights_bite
#print axioms M1Core
#print axioms M1CoreAll
#print axioms M1Target
#print axioms M1CoreDL
#print axioms DLayerObligation
#print axioms DLayerStrat
#print axioms M1Regular

end AdalyFormal.M1
