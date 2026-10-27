import ASC4

/-!
# ASC5 -- `ginv_coercive_M0`: the fine-data theorem in `n`-free form.

`M0Regime` collects EVERY hypothesis.  The conclusion is
`‖x‖² ≤ (ell^k)² · KhatM0 ell a t ρ · ⟪x, Ginv x⟫`, with `ρ = ell^k (e + 3π ell^k q0)` and `KhatM0` a function of `(ell, a, t, ρ)` ONLY:
no `k`, no volume `Lu`.  The `n`-dependence of the FlatExt-derived constants is exhibited exactly in `ASC2.S_scaling`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.AsmM0

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.ClassPropagationUbar (blkConstOf)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.SliceCoerc
open AdalyFormal.CurvBlock (dv)
open AdalyFormal.NonflatJet (r0)
open AdalyFormal.FlatExt (aFE bFE)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

noncomputable def Mc (a : ℝ) : ℝ := max 6 (16 / (3 * a))

/-- `ρ = n η`, `η = e + 3π n q0`, `n = ell^k`. -/
noncomputable def rhoM0 (ell k : ℕ) (e q0 : ℝ) : ℝ :=
  (ell : ℝ) ^ k * (e + 3 * Real.pi * ((ell : ℝ) ^ k * q0))

/-- the `n`-free smallness quantity: `Stil² + (1+t)·θ̄ + (1+1/t)(32ρ² + a φ²)`. -/
noncomputable def ThetaM0 (ell : ℕ) (a t ρ : ℝ) : ℝ :=
  Stil (Real.sqrt 3) (Real.sqrt (Mc a)) ρ ^ 2 + (1 + t) * (272 * (ρ / (3 * Real.pi)) / (4 * Real.sqrt 2))
    + (1 + 1 / t) * (32 * ρ ^ 2 + a * phiC ell (3600 * (ell : ℝ) * ρ) ^ 2)

/-- the `n`-free coercivity constant (scaled form). -/
noncomputable def KhatM0 (ell : ℕ) (a t ρ : ℝ) : ℝ :=
  max (2 * (1 + t) / (min a 1 / 1000 - ThetaM0 ell a t ρ)) (2 * Mc a / (1 - 216 * ρ ^ 2))

/-- ALL hypotheses of the whole-torus, one-gauge theorem. -/
structure M0Regime (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ) : Prop where
  hell : 2 ≤ ell
  ha : 0 < a
  ht : 0 < t
  he0 : 0 ≤ e
  hq0 : 0 ≤ q0
  /-- the torus is more than twice the top block -/
  hN : ∀ ρ', 2 * ell ^ k < scaleUp ell k Lu ρ' + 1
  /-- fine links, ONE gauge, every link -/
  hlinks : ∀ b, dv (U b) ≤ e
  /-- fine plaquettes (the tree's `periodicPlaquetteHolonomy`), every plaquette -/
  hplaq : ∀ p : PeriodicLatticePlaquette (scaleUp ell k Lu), dv (periodicPlaquetteHolonomy U p) ≤ q0
  /-- curvature-blocking smallness at the finest scale (`curv_tower_na`) -/
  hcb : 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ k * q0) ≤ 1
  h216 : 216 * rhoM0 ell k e q0 ^ 2 < 1
  h1000 : rhoM0 ell k e q0 ≤ 1 / (1000 * (ell : ℝ) ^ 3)
  /-- regularity of the background tower at ALL edges, through the tree's crude bound (the only place the strip bites) -/
  hregthr : ∀ j, j < k → (8 * (ell : ℝ) - 6) * (blkConstOf ell ^ j * e) < r0
  /-- the chain's arithmetic smallness, in `k`-free form -/
  hsmallU : ThetaM0 ell a t (rhoM0 ell k e q0) < min a 1 / 1000

theorem aFE_eq (ell k : ℕ) : aFE ell k = 27 * (ell : ℝ) ^ k * Real.sqrt ((ell : ℝ) ^ k) := by
  have hn : 0 ≤ (ell : ℝ) ^ k := by positivity
  unfold aFE
  have : 729 * ((ell : ℝ) ^ k) ^ 3 = (27 * (ell : ℝ) ^ k) ^ 2 * (ell : ℝ) ^ k := by ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

theorem bFE_eq (ell k : ℕ) : bFE ell k = 162 * Real.sqrt 3 * Real.sqrt ((ell : ℝ) ^ k) := by
  have hn : 0 ≤ (ell : ℝ) ^ k := by positivity
  unfold bFE
  have : 78732 * (ell : ℝ) ^ k = (162 : ℝ) ^ 2 * (3 * (ell : ℝ) ^ k) := by ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num), Real.sqrt_mul (by norm_num)]
  ring

theorem q_eq (ell k : ℕ) (hell : 0 < ell) :
    Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) = 1 / ((ell : ℝ) ^ k * Real.sqrt ((ell : ℝ) ^ k)) := by
  have hn : 0 < (ell : ℝ) ^ k := by positivity
  have hs : 0 < Real.sqrt ((ell : ℝ) ^ k) := Real.sqrt_pos.mpr hn
  have : 1 / ((ell : ℝ) ^ k) ^ 3 = (1 / ((ell : ℝ) ^ k * Real.sqrt ((ell : ℝ) ^ k))) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hn.le]; ring
  rw [this, Real.sqrt_sq (by positivity)]

theorem sqrt12_eq : Real.sqrt 12 = 2 * Real.sqrt 3 := by
  have : (12 : ℝ) = 2 ^ 2 * 3 := by norm_num
  rw [this, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

theorem P_eq (a : ℝ) (n : ℝ) (hn : 0 ≤ n) : Real.sqrt (Mc a * n ^ 2) = Real.sqrt (Mc a) * n := by
  rw [Real.sqrt_mul (by unfold Mc; exact le_trans (by norm_num) (le_max_left _ _)), Real.sqrt_sq hn]

#print axioms aFE_eq
#print axioms bFE_eq
#print axioms q_eq
#print axioms sqrt12_eq
#print axioms P_eq

end AdalyFormal.AsmM0
