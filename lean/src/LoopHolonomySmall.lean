import PrincipalProductAngle
import T1MainSegment
import AdalyFormal.Balaban.UbarTowerCovariance
import AdalyFormal.Balaban.TowerLawCovariant
import AdalyFormal.Balaban.QjComposite
import AdalyFormal.Balaban.AdmissibleSubspace
import AdalyFormal.Balaban.CoarseCurl
import AdalyFormal.Balaban.Bch2
import AdalyFormal.Balaban.RMapLipschitz

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# C1 loop holonomy: factor count, product angle, and an explicit (109) radius

Certified `W_x = loopVar 1 ell V c x` is the four-leg contour product of C1/C2/C3
(near tree + shifted segment + far tree + direct closure). This file:

* expands that product to an explicit list of individual `SU(2)` link factors;
* bounds the list length by a function of the C1 block side `ell` only
  (`O(ell)`, never `O(ell^3)` — `ell^3` is the C3 averaging weight);
* fills the same closed loop by an explicit list of conjugated unit plaquettes
  (`O(ell²)` rungs), matching printed CMP98 (109)'s `V0(∂p)` hypothesis;
* feeds the certified discrete product-angle lemmas to conclude
  `ν(principalSuTwoLog W_x) ≤ ρ(ε₀,ε₁,ell)` from per-bond data, and
  `ν(principalSuTwoLog W_x) ≤ ρ_□(ε₀,ell)` from plaquette data;
* records an explicit strict threshold forcing `ρ < π/2`, the small-ball
  side of `Bounds.lean` (`0 < r` / `r = 0`, not the first-cut `[π/2, π)`).
-/

noncomputable section

namespace SmallnessBridge.Assemble

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration
    PeriodicLatticePlaquette PeriodicPlaquetteDirections
    periodicPlaquetteHolonomy periodicLatticeShift)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Angle su2Angle_conj)
open AdalyFormal.Balaban.Bch2
open AdalyFormal.Balaban.RMapLipschitz
open AdalyFormal.Balaban.TowerLawCov
  (coarsePathHolonomy coarseGammaPath coarseStraightSegment coarseCoordSteps
    coarsePathEndpoint)
open AdalyFormal.Balaban.UbarTowerCov (loopVar gammaVarStrided coarseBondVar cPlusS cPlusS_eq)
open AdalyFormal.Balaban.QjComposite
  (stepBlockOf mem_stepBlockOf stepBlockOf_one
    coarsePathHolonomy_nil coarsePathHolonomy_cons
    coarsePathHolonomy_append coarsePathEndpoint_cons coarsePathEndpoint_append
    coarsePathEndpoint_coarseGammaPath)
open AdalyFormal.Balaban.AdmissibleSubspace (inBlock mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open SmallnessBridge.ProdBound
open scoped Matrix

variable {L : PeriodicLatticeExtent}

/-! ## §1 — ordered link factors of a unit-level holonomy -/

def holonomyFactors {G : Type*} [Group G] (s : ℕ)
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L) :
    List (Fin 3) → List G
  | [] => []
  | μ :: rest => V (y, μ) :: holonomyFactors s V (coarseShift y s μ) rest

@[simp] theorem holonomyFactors_nil {G : Type*} [Group G] (s : ℕ)
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L) :
    holonomyFactors s V y [] = [] := rfl

@[simp] theorem holonomyFactors_cons {G : Type*} [Group G] (s : ℕ)
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L)
    (μ : Fin 3) (rest : List (Fin 3)) :
    holonomyFactors s V y (μ :: rest) =
      V (y, μ) :: holonomyFactors s V (coarseShift y s μ) rest := rfl

theorem holonomyFactors_prod {G : Type*} [Group G] (s : ℕ)
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    (holonomyFactors s V y p).prod = coarsePathHolonomy s V y p := by
  induction p generalizing y with
  | nil =>
      rw [holonomyFactors_nil, coarsePathHolonomy_nil, List.prod_nil]
  | cons μ rest ih =>
      rw [holonomyFactors_cons, coarsePathHolonomy_cons, List.prod_cons, ih]

theorem holonomyFactors_length {G : Type*} [Group G] (s : ℕ)
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    (holonomyFactors s V y p).length = p.length := by
  induction p generalizing y with
  | nil => rfl
  | cons μ rest ih =>
      rw [holonomyFactors_cons, List.length_cons, ih, List.length_cons]

theorem mem_holonomyFactors {G : Type*} [Group G] {s : ℕ}
    {V : PeriodicLinkConfiguration G L} {y : PeriodicLatticeSite L}
    {p : List (Fin 3)} {g : G} (hg : g ∈ holonomyFactors s V y p) :
    ∃ y' : PeriodicLatticeSite L, ∃ μ : Fin 3, g = V (y', μ) := by
  induction p generalizing y with
  | nil =>
      simp [holonomyFactors_nil] at hg
  | cons μ rest ih =>
      have hcases : g = V (y, μ) ∨ g ∈ holonomyFactors s V (coarseShift y s μ) rest := by
        simpa [holonomyFactors_cons] using hg
      cases hcases with
      | inl h => exact ⟨y, μ, h⟩
      | inr h => exact ih h

/-- Inverse-oriented factors of a forward holonomy: `(g₁⋯gₙ)⁻¹ = gₙ⁻¹⋯g₁⁻¹`. -/
def invFactors {G : Type*} [Group G] (gs : List G) : List G :=
  (gs.map (fun g => g⁻¹)).reverse

theorem invFactors_prod {G : Type*} [Group G] (gs : List G) :
    (invFactors gs).prod = gs.prod⁻¹ := by
  -- `invFactors` is the map-inverse-then-reverse of `List.prod_inv_reverse`.
  simpa [invFactors] using (List.prod_inv_reverse gs).symm

theorem invFactors_length {G : Type*} [Group G] (gs : List G) :
    (invFactors gs).length = gs.length := by
  simp [invFactors]

theorem mem_invFactors {G : Type*} [Group G] {gs : List G} {g : G}
    (h : g ∈ invFactors gs) : ∃ g0 ∈ gs, g = g0⁻¹ := by
  have : g ∈ gs.map (fun x => x⁻¹) := by
    simpa [invFactors, List.mem_reverse] using h
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp this
  exact ⟨g0, hg0, rfl⟩

/-! ## §2 — the C1 four-leg factor list of `loopVar` -/

/-- Ordered factors of `loopVar s ell V c x`:
near tree, shifted segment, inverse far tree (same direction list as the near
tree, based at `cPlusS`), inverse direct closure. This is the definitional
C1/C2/C3 contour, not an L5 partner rewrite. -/
def loopFactors {G : Type*} [Group G] (s ell : ℕ)
    (V : PeriodicLinkConfiguration G L)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) : List G :=
  holonomyFactors s V c.1 (coarseGammaPath s c.1 x) ++
    holonomyFactors s V x (List.replicate ell c.2) ++
    invFactors (holonomyFactors s V (cPlusS s ell c) (coarseGammaPath s c.1 x)) ++
    invFactors (holonomyFactors s V c.1 (List.replicate ell c.2))

theorem prod_append4 {G : Type*} [Monoid G] (a b c d : List G) :
    (a ++ b ++ c ++ d).prod = a.prod * b.prod * c.prod * d.prod := by
  simp [List.prod_append, mul_assoc]

theorem loopFactors_prod {G : Type*} [Group G] (s ell : ℕ)
    (V : PeriodicLinkConfiguration G L)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    (loopFactors s ell V c x).prod = loopVar s ell V c x := by
  unfold loopFactors loopVar gammaVarStrided coarseBondVar
  rw [prod_append4, holonomyFactors_prod, holonomyFactors_prod, invFactors_prod,
    invFactors_prod, holonomyFactors_prod, holonomyFactors_prod]

/-- Exact factor count: two copies of the staircase plus two copies of the
`ell`-step segment. No `ell³` term. -/
theorem loopFactors_length {G : Type*} [Group G] (s ell : ℕ)
    (V : PeriodicLinkConfiguration G L)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    (loopFactors s ell V c x).length =
      2 * (coarseGammaPath s c.1 x).length + 2 * ell := by
  unfold loopFactors
  simp [List.length_append, holonomyFactors_length, invFactors_length,
    List.length_replicate]
  ring

theorem su2Angle_holonomyFactors_le (s : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) (delta : ℝ)
    (hV : ∀ e, su2Angle (V e) ≤ delta)
    {g : SU2} (hg : g ∈ holonomyFactors s V y p) :
    su2Angle g ≤ delta := by
  obtain ⟨y', μ, rfl⟩ := mem_holonomyFactors hg
  exact hV _

/-- Every C1 contour factor is some `V(e)` or `V(e)⁻¹`; inverses do not change
the certified angle (`su2Angle_inv`). -/
theorem su2Angle_loopFactors_le (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) (delta : ℝ)
    (hV : ∀ e, su2Angle (V e) ≤ delta)
    {g : SU2} (hg : g ∈ loopFactors s ell V c x) :
    su2Angle g ≤ delta := by
  have hmem :
      g ∈ holonomyFactors s V c.1 (coarseGammaPath s c.1 x) ∨
        g ∈ holonomyFactors s V x (List.replicate ell c.2) ∨
          g ∈ invFactors
              (holonomyFactors s V (cPlusS s ell c) (coarseGammaPath s c.1 x)) ∨
            g ∈ invFactors
                (holonomyFactors s V c.1 (List.replicate ell c.2)) := by
    simpa [loopFactors, List.mem_append, or_assoc] using hg
  rcases hmem with h | h | h | h
  · exact su2Angle_holonomyFactors_le s V _ _ delta hV h
  · exact su2Angle_holonomyFactors_le s V _ _ delta hV h
  · obtain ⟨g0, hg0, rfl⟩ := mem_invFactors h
    rw [su2Angle_inv]
    exact su2Angle_holonomyFactors_le s V _ _ delta hV hg0
  · obtain ⟨g0, hg0, rfl⟩ := mem_invFactors h
    rw [su2Angle_inv]
    exact su2Angle_holonomyFactors_le s V _ _ delta hV hg0

/-! ## §3 — staircase length on the C1 block `B(c₋)` of side `ell`

Channels, for `x ∈ stepBlockOf c.1 1 ell`:

* near tree: `(coarseGammaPath 1 c.1 x).length ≤ 3*(ell-1)`  (`O(ell)`, 3 axes);
* shifted segment: `List.replicate ell c.2`, length `= ell`;
* far tree: the same list as the near tree (definitional in `gammaVarStrided`),
  same length; L5 is not used;
* direct closure: `List.replicate ell c.2`, length `= ell`.

The C3 weight `((ell:ℝ)^3)⁻¹` counts block sites, not holonomy factors.
-/

theorem coarseGammaPath_length (s : ℕ) (y x : PeriodicLatticeSite L) :
    (coarseGammaPath s y x).length =
      coarseCoordSteps s y x 2 +
        coarseCoordSteps s (Function.update y 2 (x 2)) x 1 +
          coarseCoordSteps s
            (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0 := by
  simp [coarseGammaPath, coarseStraightSegment, List.length_append,
    List.length_replicate]
  ring

theorem coarseCoordSteps_update_ne (s : ℕ) (y x : PeriodicLatticeSite L)
    {ν κ : Fin 3} (w : Fin (L κ + 1)) (h : ν ≠ κ) :
    coarseCoordSteps s (Function.update y κ w) x ν = coarseCoordSteps s y x ν := by
  unfold coarseCoordSteps
  rw [Function.update_of_ne h]

theorem coarseCoordSteps_one_lt_of_inBlock {y x : PeriodicLatticeSite L} {ell : ℕ}
    (hx : inBlock y ell x) (μ : Fin 3) :
    coarseCoordSteps 1 y x μ < ell := by
  obtain ⟨hlo, hhi⟩ := hx μ
  unfold coarseCoordSteps
  rw [Fin.sub_val_of_le (Fin.le_def.mpr hlo), Nat.div_one]
  omega

theorem coarseGammaPath_one_length_le {y x : PeriodicLatticeSite L} {ell : ℕ}
    (hx : inBlock y ell x) :
    (coarseGammaPath 1 y x).length ≤ 3 * (ell - 1) := by
  have h2 : coarseCoordSteps 1 y x 2 < ell :=
    coarseCoordSteps_one_lt_of_inBlock hx 2
  have h1 : coarseCoordSteps 1 y x 1 < ell :=
    coarseCoordSteps_one_lt_of_inBlock hx 1
  have h0 : coarseCoordSteps 1 y x 0 < ell :=
    coarseCoordSteps_one_lt_of_inBlock hx 0
  have h1' :
      coarseCoordSteps 1 (Function.update y 2 (x 2)) x 1 =
        coarseCoordSteps 1 y x 1 :=
    coarseCoordSteps_update_ne 1 y x (x 2) (by decide : (1 : Fin 3) ≠ 2)
  have h0a :
      coarseCoordSteps 1 (Function.update y 2 (x 2)) x 0 =
        coarseCoordSteps 1 y x 0 :=
    coarseCoordSteps_update_ne 1 y x (x 2) (by decide : (0 : Fin 3) ≠ 2)
  have h0' :
      coarseCoordSteps 1
          (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0 =
        coarseCoordSteps 1 y x 0 := by
    rw [coarseCoordSteps_update_ne 1 (Function.update y 2 (x 2)) x (x 1)
      (by decide : (0 : Fin 3) ≠ 1), h0a]
  rw [coarseGammaPath_length, h1', h0']
  have h2le : coarseCoordSteps 1 y x 2 ≤ ell - 1 := Nat.le_pred_of_lt h2
  have h1le : coarseCoordSteps 1 y x 1 ≤ ell - 1 := Nat.le_pred_of_lt h1
  have h0le : coarseCoordSteps 1 y x 0 ≤ ell - 1 := Nat.le_pred_of_lt h0
  have : 3 * (ell - 1) = (ell - 1) + (ell - 1) + (ell - 1) := by ring
  rw [this]
  exact add_le_add (add_le_add h2le h1le) h0le

/-- Uniform C1 factor-count majorant. Equals `8*ell - 6` at `ell ≥ 1`; saturates
to `0` at `ell = 0`. -/
def loopFactorBound (ell : ℕ) : ℕ := 2 * ell + 6 * (ell - 1)

theorem loopFactorBound_eq_of_pos {ell : ℕ} (hell : 0 < ell) :
    loopFactorBound ell = 8 * ell - 6 := by
  unfold loopFactorBound
  have : 1 ≤ ell := hell
  omega

theorem shiftedSegment_length (ell : ℕ) (μ : Fin 3) :
    (List.replicate ell μ).length = ell :=
  List.length_replicate

theorem loopFactors_length_le_bound (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hx : x ∈ stepBlockOf c.1 1 ell) :
    (loopFactors 1 ell V c x).length ≤ loopFactorBound ell := by
  have hxB : x ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf c.1 ell := by
    rwa [← stepBlockOf_one]
  have hin : inBlock c.1 ell x := (mem_blockOf).mp hxB
  have hγ : (coarseGammaPath 1 c.1 x).length ≤ 3 * (ell - 1) :=
    coarseGammaPath_one_length_le hin
  have hlen := loopFactors_length (G := SU2) 1 ell V c x
  unfold loopFactorBound
  have h2 : 2 * (coarseGammaPath 1 c.1 x).length ≤ 2 * (3 * (ell - 1)) :=
    Nat.mul_le_mul_left _ hγ
  have : 2 * (3 * (ell - 1)) = 6 * (ell - 1) := by ring
  rw [hlen]
  omega

/-! ## §4 — product angle → principal logarithm on the C1 loop -/

/-- Exact-length form: no block membership, no `ell` majorant. Factor bounds
are non-strict; the ball `n·δ < π/2` is strict. -/
theorem nu_loopVar_le_length_mul (V : PeriodicLinkConfiguration SU2 L)
    (s ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (delta : ℝ)
    (hV : ∀ e, su2Angle (V e) ≤ delta)
    (hsmall :
      ((loopFactors s ell V c x).length : ℝ) * delta < Real.pi / 2) :
    nu ((principalSuTwoLog (loopVar s ell V c x) : SuTwo) : M2) ≤
      ((loopFactors s ell V c x).length : ℝ) * delta ∧
      ((loopFactors s ell V c x).length : ℝ) * delta < Real.pi / 2 := by
  have hprod := loopFactors_prod (G := SU2) s ell V c x
  have hfac : ∀ g ∈ loopFactors s ell V c x, su2Angle g ≤ delta :=
    fun g hg => su2Angle_loopFactors_le s ell V c x delta hV hg
  have h := principal_list_prod_small (loopFactors s ell V c x) delta hfac hsmall
  rw [hprod] at h
  exact h

/-- Uniform C1 form: `x ∈ B(c₋)`, `ρ = n(ell)·δ` with `n(ell) = loopFactorBound ell`.
Requires `0 ≤ δ` to loosen the exact length to the majorant. -/
theorem nu_loopVar_le_bound_mul (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (delta : ℝ)
    (hδ : 0 ≤ delta)
    (hV : ∀ e, su2Angle (V e) ≤ delta)
    (hx : x ∈ stepBlockOf c.1 1 ell)
    (hsmall : (loopFactorBound ell : ℝ) * delta < Real.pi / 2) :
    nu ((principalSuTwoLog (loopVar 1 ell V c x) : SuTwo) : M2) ≤
      (loopFactorBound ell : ℝ) * delta ∧
      (loopFactorBound ell : ℝ) * delta < Real.pi / 2 := by
  have hlen : ((loopFactors 1 ell V c x).length : ℝ) ≤ (loopFactorBound ell : ℝ) :=
    Nat.cast_le.mpr (loopFactors_length_le_bound V ell c x hx)
  have hlen_small :
      ((loopFactors 1 ell V c x).length : ℝ) * delta < Real.pi / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hlen hδ) hsmall
  have hpt := nu_loopVar_le_length_mul V 1 ell c x delta hV hlen_small
  have hloose :
      ((loopFactors 1 ell V c x).length : ℝ) * delta ≤
        (loopFactorBound ell : ℝ) * delta :=
    mul_le_mul_of_nonneg_right hlen hδ
  exact ⟨hpt.1.trans hloose, hsmall⟩

/-! ## §5 — printed CMP98 p.34 eq. (109)

Ground truth (independent raster read):
`compute/estimates_layer/adjudicate33/INDEPENDENT_TRANSCRIPTION_109.md`.

```
|V0(∂p)-1| < α0,   V1,b = e^{i A_b},   |A_b| < α1,   p, b ⊂ Ω'.
```

α0 bounds the V0 **plaquette holonomy** `V0(∂p)`, not a per-bond near-identity
of V0. α1 bounds the per-bond Lie-algebra coordinate of the perturbation.
Campaign alias `eps0, eps1` for the printed `α0, α1`. Distance is the certified
`frobNorm`. `V1,b = su2Exp (X b)` with `X` already anti-Hermitian (`X = iA` and
the printed `|A_b| → ν(X)` conversion remain caller obligations). `Ω'` is not a
formal object here; the hypothesis is imposed on every plaquette / bond.

Printed inequalities are **strict**. The certified product lemmas consume the
non-strict closures; `le_of_lt` is the only bridge, and the converse (rounding
`≤` up to `<`) is never used.

Per-bond near-identity of V0 is a **strictly stronger** hypothesis, recorded as
`NearIdentity109`. It is **not** printed (109) and is **not** derived from it
(that implication is a gauge-fixing / regularity residual, matching the honesty
in `deps/ESmall.lean`). The background-only theorems `nu_loopVar_V0_le_rho` /
`nu_loopVar_V0_le_rhoCap` consume the plaquette hypothesis via the Stokes filling
of §6. The perturbed-link theorems consume `NearIdentity109` and say so.
-/

/-- Printed CMP98 p.34 (109), strict, in certified units: plaquette V0, bond X. -/
def Printed109 (V0 : PeriodicLinkConfiguration SU2 L)
    (X : PeriodicLatticeEdge L → M2) (eps0 eps1 : ℝ) : Prop :=
  (∀ p : PeriodicLatticePlaquette L,
      frobNorm ((periodicPlaquetteHolonomy (G := SU2) V0 p : M2) - 1) < eps0) ∧
    (∀ e, IsSu2 (X e)) ∧
      (∀ e, nu (X e) < eps1)

/-- Non-strict **per-bond** closures consumed by `su2Angle_perturbed_link_le`.
This is strictly stronger than printed (109) on V0, and is not derived from it. -/
def NearIdentity109 (V0 : PeriodicLinkConfiguration SU2 L)
    (X : PeriodicLatticeEdge L → M2) (eps0 eps1 : ℝ) : Prop :=
  (∀ e, frobNorm ((V0 e : M2) - 1) ≤ eps0) ∧
    (∀ e, IsSu2 (X e)) ∧
      (∀ e, nu (X e) ≤ eps1)

/-- Composite configuration of C1/`configMul`: `V_b = e^{X_b} V0_b`. -/
def perturbedConfig (V0 : PeriodicLinkConfiguration SU2 L)
    (X : PeriodicLatticeEdge L → M2) : PeriodicLinkConfiguration SU2 L :=
  fun e => su2Exp (X e) * V0 e

/-- Per-link angle budget from (109)-style data. Requires `eps1 ≤ π` for
`angle_exp`, which is **not** part of printed (109). -/
theorem su2Angle_perturbedConfig_le (V0 : PeriodicLinkConfiguration SU2 L)
    (X : PeriodicLatticeEdge L → M2) (eps0 eps1 : ℝ)
    (h : NearIdentity109 V0 X eps0 eps1) (hpi : eps1 ≤ Real.pi) (e : PeriodicLatticeEdge L) :
    su2Angle (perturbedConfig V0 X e) ≤
      (Real.pi / (2 * Real.sqrt 2)) * eps0 + eps1 :=
  su2Angle_perturbed_link_le (V0 e) (X e) eps0 eps1 (h.2.1 e) (h.1 e) (h.2.2 e) hpi

/-- Explicit C1 radius. `n(ell) = 2ell + 6(ell-1)` composite factors, each of
angle `≤ (π/(2√2))ε₀ + ε₁`. -/
def loopRho (eps0 eps1 : ℝ) (ell : ℕ) : ℝ :=
  (loopFactorBound ell : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * eps0 + eps1)

def loopRhoCap (eps0 : ℝ) (ell : ℕ) : ℝ :=
  (loopFactorBound ell : ℝ) * ((Real.pi / 4) * eps0)

theorem loopRho_nonneg {eps0 eps1 : ℝ} {ell : ℕ}
    (h0 : 0 ≤ eps0) (h1 : 0 ≤ eps1) : 0 ≤ loopRho eps0 eps1 ell :=
  mul_nonneg (Nat.cast_nonneg _)
    (add_nonneg (mul_nonneg (by positivity) h0) h1)

/-- Background-only sufficient threshold: `n(ell)·ε₀ < √2` implies
`loopRho ε₀ 0 ell < π/2`. Strictness is preserved. -/
theorem loopRho_lt_half_of_n_eps0 {ell : ℕ} {eps0 : ℝ}
    (hsmall : (loopFactorBound ell : ℝ) * eps0 < Real.sqrt 2) :
    loopRho eps0 0 ell < Real.pi / 2 := by
  unfold loopRho
  have hrew :
      (loopFactorBound ell : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * eps0 + 0) =
        (Real.pi / (2 * Real.sqrt 2)) * ((loopFactorBound ell : ℝ) * eps0) := by
    ring
  rw [hrew]
  calc
    (Real.pi / (2 * Real.sqrt 2)) * ((loopFactorBound ell : ℝ) * eps0)
        < (Real.pi / (2 * Real.sqrt 2)) * Real.sqrt 2 :=
      mul_lt_mul_of_pos_left hsmall (by positivity)
    _ = Real.pi / 2 := by field_simp

/-- Explicit `ε₀ < √2 / n(ell)` form, `n(ell) > 0`. -/
theorem n_eps0_lt_sqrt2_of_div {ell : ℕ} {eps0 : ℝ}
    (hn : 0 < loopFactorBound ell)
    (he : eps0 < Real.sqrt 2 / (loopFactorBound ell : ℝ)) :
    (loopFactorBound ell : ℝ) * eps0 < Real.sqrt 2 := by
  have hpos : 0 < (loopFactorBound ell : ℝ) := Nat.cast_pos.mpr hn
  have : eps0 * (loopFactorBound ell : ℝ) < Real.sqrt 2 :=
    (lt_div_iff₀ hpos).mp he
  rwa [mul_comm]

/-- Cap-coefficient threshold: `n(ell)·ε₀ < 2` implies `loopRhoCap ε₀ ell < π/2`. -/
theorem loopRhoCap_lt_half_of_n_eps0 {ell : ℕ} {eps0 : ℝ}
    (hsmall : (loopFactorBound ell : ℝ) * eps0 < 2) :
    loopRhoCap eps0 ell < Real.pi / 2 := by
  unfold loopRhoCap
  have hm :=
    mul_lt_mul_of_pos_left hsmall (by positivity : 0 < Real.pi / 4)
  nlinarith [hm]

/-- Split sufficient condition with both `(109)` parameters, both strict. -/
theorem loopRho_lt_half_of_split {ell : ℕ} {eps0 eps1 : ℝ}
    (h0 : (loopFactorBound ell : ℝ) * eps0 < Real.sqrt 2 / 2)
    (h1 : (loopFactorBound ell : ℝ) * eps1 < Real.pi / 4) :
    loopRho eps0 eps1 ell < Real.pi / 2 := by
  unfold loopRho
  have ha :
      (loopFactorBound ell : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * eps0) <
        Real.pi / 4 := by
    have hrew :
        (loopFactorBound ell : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * eps0) =
          (Real.pi / (2 * Real.sqrt 2)) * ((loopFactorBound ell : ℝ) * eps0) := by
      ring
    rw [hrew]
    have hlt :
        (Real.pi / (2 * Real.sqrt 2)) * ((loopFactorBound ell : ℝ) * eps0) <
          (Real.pi / (2 * Real.sqrt 2)) * (Real.sqrt 2 / 2) :=
      mul_lt_mul_of_pos_left h0 (by positivity)
    have heq : (Real.pi / (2 * Real.sqrt 2)) * (Real.sqrt 2 / 2) = Real.pi / 4 := by
      field_simp
      ring
    exact hlt.trans_eq heq
  have hsum :
      (loopFactorBound ell : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * eps0 + eps1) =
        (loopFactorBound ell : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * eps0) +
          (loopFactorBound ell : ℝ) * eps1 := by
    ring
  rw [hsum]
  linarith [ha, h1]

/-! ## §6 — Stokes filling of the C1 loop by unit plaquettes

Printed (109) supplies `‖V0(∂p)-1‖_F < α0` on unit plaquettes, not a per-bond
bound on V0. The C1 loop `W_x = loopVar 1 ell V c x` is the boundary of the
tube obtained by extruding the near staircase along `c.2` for `ell` steps.
Each transverse staircase bond contributes `ell` conjugated unit plaquettes;
same-direction rungs are degenerate and dropped. The filling has length
`≤ 3 ell (ell-1)` on `x ∈ B(c₋)`.
-/

theorem periodicLatticeShift_comm_all (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    periodicLatticeShift (periodicLatticeShift y μ) ν =
      periodicLatticeShift (periodicLatticeShift y ν) μ := by
  unfold periodicLatticeShift
  by_cases h : μ = ν
  · subst h; rfl
  · rw [Function.update_of_ne (Ne.symm h), Function.update_of_ne h, Function.update_comm h]

theorem coarseShift_zero (y : PeriodicLatticeSite L) (μ : Fin 3) :
    coarseShift y 0 μ = y := rfl

theorem coarseShift_succ (y : PeriodicLatticeSite L) (n : ℕ) (μ : Fin 3) :
    coarseShift y (n + 1) μ = periodicLatticeShift (coarseShift y n μ) μ :=
  Function.iterate_succ_apply' (fun z => periodicLatticeShift z μ) n y

theorem coarseShift_one_eq (y : PeriodicLatticeSite L) (μ : Fin 3) :
    coarseShift y 1 μ = periodicLatticeShift y μ := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, coarseShift_succ, coarseShift_zero]

theorem coarseShift_add (y : PeriodicLatticeSite L) (a b : ℕ) (μ : Fin 3) :
    coarseShift (coarseShift y a μ) b μ = coarseShift y (a + b) μ := by
  unfold coarseShift
  rw [← Function.iterate_add_apply, Nat.add_comm]

theorem periodicLatticeShift_coarseShift_comm
    (y : PeriodicLatticeSite L) (a : ℕ) (μ ν : Fin 3) :
    periodicLatticeShift (coarseShift y a μ) ν =
      coarseShift (periodicLatticeShift y ν) a μ := by
  induction a with
  | zero => rw [coarseShift_zero, coarseShift_zero]
  | succ a ih =>
      rw [coarseShift_succ, periodicLatticeShift_comm_all, ih, coarseShift_succ]

theorem coarseShift_comm (y : PeriodicLatticeSite L) (a b : ℕ) (μ ν : Fin 3) :
    coarseShift (coarseShift y a μ) b ν = coarseShift (coarseShift y b ν) a μ := by
  induction b with
  | zero => rw [coarseShift_zero, coarseShift_zero]
  | succ b ih =>
      rw [coarseShift_succ, ih, coarseShift_succ, periodicLatticeShift_coarseShift_comm]

theorem coarsePathEndpoint_coarseShift (y : PeriodicLatticeSite L) (n : ℕ)
    (μ : Fin 3) (p : List (Fin 3)) :
    coarsePathEndpoint 1 (coarseShift y n μ) p =
      coarseShift (coarsePathEndpoint 1 y p) n μ := by
  induction p generalizing y with
  | nil => rfl
  | cons ν rest ih =>
      rw [coarsePathEndpoint_cons, coarsePathEndpoint_cons, coarseShift_comm]
      exact ih _

theorem coarsePathEndpoint_snoc (y : PeriodicLatticeSite L) (p : List (Fin 3))
    (ν : Fin 3) :
    coarsePathEndpoint 1 y (p ++ [ν]) =
      periodicLatticeShift (coarsePathEndpoint 1 y p) ν := by
  rw [coarsePathEndpoint_append, coarsePathEndpoint_cons, coarseShift_one_eq]
  rfl

def conjBy {G : Type*} [Group G] (g x : G) : G := g * x * g⁻¹

theorem conjBy_mul {G : Type*} [Group G] (g a b : G) :
    conjBy g a * conjBy g b = conjBy g (a * b) := by
  unfold conjBy
  simp [mul_assoc, inv_mul_cancel]

theorem list_map_conjBy_prod {G : Type*} [Group G] (g : G) (gs : List G) :
    (gs.map (conjBy g)).prod = conjBy g gs.prod := by
  induction gs with
  | nil => simp [conjBy]
  | cons x xs ih =>
      simp [List.prod_cons, ih, conjBy_mul]

theorem su2Angle_conjBy (g x : SU2) : su2Angle (conjBy g x) = su2Angle x :=
  su2Angle_conj g x

/-- Oriented unit plaquette word, defined for every ordered pair of directions
(degenerate when `μ = ν`). -/
def orientedPlaqHol {G : Type*} [Group G] (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) : G :=
  V (y, μ) * V (periodicLatticeShift y μ, ν) *
    (V (periodicLatticeShift y ν, μ))⁻¹ * (V (y, ν))⁻¹

theorem su2Angle_orientedPlaqHol_le_of_ne
    (V : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L)
    {μ ν : Fin 3} (hμν : μ ≠ ν) (delta : ℝ)
    (h : ∀ p : PeriodicLatticePlaquette L,
      su2Angle (periodicPlaquetteHolonomy V p) ≤ delta) :
    su2Angle (orientedPlaqHol V y μ ν) ≤ delta := by
  rcases lt_trichotomy μ ν with hlt | heq | hgt
  · have hp : orientedPlaqHol V y μ ν =
        periodicPlaquetteHolonomy V (y, ⟨(μ, ν), hlt⟩) := rfl
    rw [hp]
    exact h _
  · exact (hμν heq).elim
  · have hp : orientedPlaqHol V y μ ν =
        (periodicPlaquetteHolonomy V (y, ⟨(ν, μ), hgt⟩))⁻¹ := by
      simp [orientedPlaqHol, periodicPlaquetteHolonomy, mul_assoc, mul_inv, inv_inv]
    rw [hp, su2Angle_inv]
    exact h _

def segmentHol {G : Type*} [Group G] (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ : Fin 3) (ell : ℕ) : G :=
  (holonomyFactors 1 V y (List.replicate ell μ)).prod

theorem segmentHol_zero {G : Type*} [Group G] (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ : Fin 3) : segmentHol V y μ 0 = 1 := by
  simp [segmentHol, holonomyFactors_nil]

theorem segmentHol_succ {G : Type*} [Group G] (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    segmentHol V y μ (n + 1) =
      V (y, μ) * segmentHol V (periodicLatticeShift y μ) μ n := by
  unfold segmentHol
  rw [List.replicate_succ, holonomyFactors_cons, List.prod_cons, coarseShift_one_eq]

theorem segmentHol_snoc {G : Type*} [Group G] (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    segmentHol V y μ (n + 1) =
      segmentHol V y μ n * V (coarseShift y n μ, μ) := by
  induction n generalizing y with
  | zero =>
      simp [segmentHol_succ, segmentHol_zero, coarseShift_zero]
  | succ n ih =>
      rw [segmentHol_succ, ih (periodicLatticeShift y μ), ← mul_assoc, ← segmentHol_succ,
        ← coarseShift_one_eq, coarseShift_add, Nat.add_comm]

def ladderHol {G : Type*} [Group G] (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) (ell : ℕ) : G :=
  (segmentHol V y μ ell)⁻¹ * V (y, ν) *
    segmentHol V (periodicLatticeShift y ν) μ ell *
      (V (coarseShift y ell μ, ν))⁻¹

theorem ladderHol_zero {G : Type*} [Group G] (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) : ladderHol V y μ ν 0 = 1 := by
  simp [ladderHol, segmentHol_zero, coarseShift_zero]

theorem ladderHol_eq_one_of_eq {G : Type*} [Group G]
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L)
    (μ : Fin 3) (ell : ℕ) : ladderHol V y μ μ ell = 1 := by
  cases ell with
  | zero => exact ladderHol_zero V y μ μ
  | succ n =>
      have hsite : coarseShift (periodicLatticeShift y μ) n μ =
          coarseShift y (n + 1) μ := by
        rw [← coarseShift_one_eq, coarseShift_add, Nat.add_comm]
      unfold ladderHol
      rw [segmentHol_succ, segmentHol_snoc (y := periodicLatticeShift y μ), hsite]
      simp [mul_assoc, inv_mul_cancel, mul_inv_cancel]

/-- Rungs of the `μ`-extrusion of a `ν`-step; empty on the degenerate line `μ = ν`. -/
def ladderFactors (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) : ℕ → List SU2
  | 0 => []
  | n + 1 =>
      if h : μ = ν then []
      else
        let A := V (y, μ)
        let hol := orientedPlaqHol V y μ ν
        let S := segmentHol V (periodicLatticeShift y μ) μ n
        (S⁻¹ * (A⁻¹ * hol⁻¹ * A) * S) ::
          ladderFactors V (periodicLatticeShift y μ) μ ν n

theorem ladderFactors_length_le (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) (ell : ℕ) :
    (ladderFactors V y μ ν ell).length ≤ ell := by
  induction ell generalizing y with
  | zero => simp [ladderFactors]
  | succ n ih =>
      unfold ladderFactors
      split_ifs
      · simp
      · exact Nat.succ_le_succ (ih _)

theorem ladderHol_succ_eq
    (V : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L)
    {μ ν : Fin 3} (hμν : μ ≠ ν) (n : ℕ) :
    ladderHol V y μ ν (n + 1) =
      (segmentHol V (periodicLatticeShift y μ) μ n)⁻¹
        * ((V (y, μ))⁻¹ * (orientedPlaqHol V y μ ν)⁻¹ * V (y, μ))
        * segmentHol V (periodicLatticeShift y μ) μ n
        * ladderHol V (periodicLatticeShift y μ) μ ν n := by
  set A : SU2 := V (y, μ)
  set D : SU2 := V (y, ν)
  set B : SU2 := V (periodicLatticeShift y μ, ν)
  set C : SU2 := V (periodicLatticeShift y ν, μ)
  set S : SU2 := segmentHol V (periodicLatticeShift y μ) μ n
  set Sν : SU2 :=
    segmentHol V (periodicLatticeShift (periodicLatticeShift y μ) ν) μ n
  set far : SU2 := V (coarseShift y (n + 1) μ, ν)
  have hSν :
      segmentHol V (periodicLatticeShift (periodicLatticeShift y ν) μ) μ n = Sν := by
    simp only [Sν, periodicLatticeShift_comm_all]
  have hfar : V (coarseShift (periodicLatticeShift y μ) n μ, ν) = far := by
    simp only [far, coarseShift_succ, periodicLatticeShift_coarseShift_comm]
  have hinv : (orientedPlaqHol V y μ ν)⁻¹ = D * C * B⁻¹ * A⁻¹ := by
    simp [orientedPlaqHol, A, B, C, D, mul_assoc, mul_inv, inv_inv]
  have hseg : segmentHol V (periodicLatticeShift y ν) μ (n + 1) = C * Sν := by
    rw [segmentHol_succ, hSν]
  have hsmall :
      ladderHol V (periodicLatticeShift y μ) μ ν n = S⁻¹ * B * Sν * far⁻¹ := by
    simp only [ladderHol, S, B, Sν, hfar]
  conv_lhs => unfold ladderHol
  rw [segmentHol_succ, hseg]
  rw [show V (coarseShift y (n + 1) μ, ν) = far from rfl, hsmall, hinv]
  simp [mul_assoc, inv_mul_cancel, mul_inv_cancel, A, D, B, C, S, Sν, far]

theorem ladderFactors_prod (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) (ell : ℕ) :
    (ladderFactors V y μ ν ell).prod = ladderHol V y μ ν ell := by
  induction ell generalizing y with
  | zero => simp [ladderFactors, ladderHol_zero]
  | succ n ih =>
      unfold ladderFactors
      split_ifs with h
      · subst h
        simp [ladderHol_eq_one_of_eq]
      · rw [List.prod_cons, ih, ladderHol_succ_eq (hμν := h)]

theorem su2Angle_mem_ladderFactors (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) (ell : ℕ) (delta : ℝ)
    (h : ∀ p : PeriodicLatticePlaquette L,
      su2Angle (periodicPlaquetteHolonomy V p) ≤ delta)
    {g : SU2} (hg : g ∈ ladderFactors V y μ ν ell) :
    su2Angle g ≤ delta := by
  induction ell generalizing y with
  | zero =>
      simp [ladderFactors] at hg
  | succ n ih =>
      unfold ladderFactors at hg
      split_ifs at hg with hμν
      · simp at hg
      · simp only [List.mem_cons] at hg
        rcases hg with hg | hg
        · subst hg
          set A : SU2 := V (y, μ)
          set hol : SU2 := orientedPlaqHol V y μ ν
          set S : SU2 := segmentHol V (periodicLatticeShift y μ) μ n
          have h1 : su2Angle (A⁻¹ * hol⁻¹ * A) = su2Angle hol := by
            have := su2Angle_conj A⁻¹ hol⁻¹
            simpa [inv_inv, su2Angle_inv] using this
          have h2 : su2Angle (S⁻¹ * (A⁻¹ * hol⁻¹ * A) * S) = su2Angle hol := by
            have := su2Angle_conj S⁻¹ (A⁻¹ * hol⁻¹ * A)
            simpa [inv_inv, h1] using this
          simpa [A, hol, S] using h2.trans_le
            (su2Angle_orientedPlaqHol_le_of_ne V y hμν delta h)
        · exact ih (periodicLatticeShift y μ) hg

theorem holonomyFactors_append_prod {G : Type*} [Group G]
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L)
    (p q : List (Fin 3)) :
    (holonomyFactors 1 V y (p ++ q)).prod =
      (holonomyFactors 1 V y p).prod *
        (holonomyFactors 1 V (coarsePathEndpoint 1 y p) q).prod := by
  rw [holonomyFactors_prod, holonomyFactors_prod, holonomyFactors_prod,
    coarsePathHolonomy_append]

theorem holonomyFactors_snoc_prod {G : Type*} [Group G]
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) (ν : Fin 3) :
    (holonomyFactors 1 V y (p ++ [ν])).prod =
      (holonomyFactors 1 V y p).prod * V (coarsePathEndpoint 1 y p, ν) := by
  rw [holonomyFactors_append_prod, holonomyFactors_cons, holonomyFactors_nil,
    List.prod_cons, List.prod_nil, mul_one]

/-- Conjugated plaquette rungs filling the C1 tube along a remaining staircase. -/
def surfaceAlong (V : PeriodicLinkConfiguration SU2 L)
    (y0 : PeriodicLatticeSite L) (μ : Fin 3) (ell : ℕ) :
    List (Fin 3) → List (Fin 3) → List SU2
  | acc, [] => []
  | acc, ν :: rest =>
      let y := coarsePathEndpoint 1 y0 acc
      let S0 := segmentHol V y0 μ ell
      let holFar := (holonomyFactors 1 V (coarseShift y0 ell μ) acc).prod
      List.append ((ladderFactors V y μ ν ell).map (conjBy (S0 * holFar)))
        (surfaceAlong V y0 μ ell (List.append acc [ν]) rest)

theorem surfaceAlong_length_le (V : PeriodicLinkConfiguration SU2 L)
    (y0 : PeriodicLatticeSite L) (μ : Fin 3) (ell : ℕ)
    (acc rest : List (Fin 3)) :
    (surfaceAlong V y0 μ ell acc rest).length ≤ ell * rest.length := by
  induction rest generalizing acc with
  | nil => simp [surfaceAlong]
  | cons ν rest ih =>
      simp [surfaceAlong, List.length_append, List.length_map, List.length_cons]
      have h1 := ladderFactors_length_le V (coarsePathEndpoint 1 y0 acc) μ ν ell
      have h2 := ih (acc ++ [ν])
      calc
        _ ≤ ell + ell * rest.length := Nat.add_le_add h1 h2
        _ = ell * (rest.length + 1) := by ring

theorem su2Angle_mem_surfaceAlong (V : PeriodicLinkConfiguration SU2 L)
    (y0 : PeriodicLatticeSite L) (μ : Fin 3) (ell : ℕ)
    (acc rest : List (Fin 3)) (delta : ℝ)
    (h : ∀ p : PeriodicLatticePlaquette L,
      su2Angle (periodicPlaquetteHolonomy V p) ≤ delta)
    {g : SU2} (hg : g ∈ surfaceAlong V y0 μ ell acc rest) :
    su2Angle g ≤ delta := by
  induction rest generalizing acc with
  | nil =>
      simp [surfaceAlong] at hg
  | cons ν rest ih =>
      have hmem :
          g ∈ (ladderFactors V (coarsePathEndpoint 1 y0 acc) μ ν ell).map
              (conjBy (segmentHol V y0 μ ell *
                (holonomyFactors 1 V (coarseShift y0 ell μ) acc).prod)) ∨
            g ∈ surfaceAlong V y0 μ ell (acc ++ [ν]) rest := by
        simpa [surfaceAlong] using hg
      rcases hmem with hg | hg
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        rw [su2Angle_conjBy]
        exact su2Angle_mem_ladderFactors V _ μ ν ell delta h hg0
      · exact ih (acc ++ [ν]) hg

theorem surfaceAlong_prod (V : PeriodicLinkConfiguration SU2 L)
    (y0 : PeriodicLatticeSite L) (μ : Fin 3) (ell : ℕ)
    (acc rest : List (Fin 3)) :
    ((holonomyFactors 1 V y0 acc).prod
        * segmentHol V (coarsePathEndpoint 1 y0 acc) μ ell
        * (holonomyFactors 1 V (coarseShift y0 ell μ) acc).prod⁻¹
        * (segmentHol V y0 μ ell)⁻¹
        * (surfaceAlong V y0 μ ell acc rest).prod) =
      ((holonomyFactors 1 V y0 (List.append acc rest)).prod
        * segmentHol V (coarsePathEndpoint 1 y0 (List.append acc rest)) μ ell
        * (holonomyFactors 1 V (coarseShift y0 ell μ) (List.append acc rest)).prod⁻¹
        * (segmentHol V y0 μ ell)⁻¹) := by
  induction rest generalizing acc with
  | nil =>
      simp [surfaceAlong]
  | cons ν rest ih =>
      let y := coarsePathEndpoint 1 y0 acc
      let S0 := segmentHol V y0 μ ell
      let holFar := (holonomyFactors 1 V (coarseShift y0 ell μ) acc).prod
      let Q := ladderHol V y μ ν ell
      let accν := List.append acc [ν]
      have hsurf :
          surfaceAlong V y0 μ ell acc (ν :: rest) =
            List.append ((ladderFactors V y μ ν ell).map (conjBy (S0 * holFar)))
              (surfaceAlong V y0 μ ell accν rest) := by
        simp [surfaceAlong, y, S0, holFar, accν]
      have hmap :
          ((ladderFactors V y μ ν ell).map (conjBy (S0 * holFar))).prod =
            conjBy (S0 * holFar) Q := by
        rw [list_map_conjBy_prod, ladderFactors_prod]
      have hyν : coarsePathEndpoint 1 y0 accν = periodicLatticeShift y ν := by
        simpa [y, accν] using coarsePathEndpoint_snoc y0 acc ν
      have hfarν :
          (holonomyFactors 1 V (coarseShift y0 ell μ) accν).prod =
            holFar * V (coarseShift y ell μ, ν) := by
        simp only [accν]
        rw [show acc.append [ν] = acc ++ [ν] from rfl, holonomyFactors_snoc_prod,
          coarsePathEndpoint_coarseShift]
      have hpre :
          (holonomyFactors 1 V y0 accν).prod =
            (holonomyFactors 1 V y0 acc).prod * V (y, ν) := by
        simpa [accν] using holonomyFactors_snoc_prod V y0 acc ν
      have hstep :
          ((holonomyFactors 1 V y0 acc).prod * segmentHol V y μ ell * holFar⁻¹ * S0⁻¹
              * conjBy (S0 * holFar) Q) =
            ((holonomyFactors 1 V y0 accν).prod
              * segmentHol V (coarsePathEndpoint 1 y0 accν) μ ell
              * (holonomyFactors 1 V (coarseShift y0 ell μ) accν).prod⁻¹
              * S0⁻¹) := by
        unfold conjBy Q ladderHol
        rw [hyν, hfarν, hpre]
        simp [mul_assoc, inv_mul_cancel, mul_inv_cancel, y, S0, holFar]
      have hrest : List.append accν rest = List.append acc (ν :: rest) := by
        simp [accν]
      rw [hsurf, show List.append
          ((ladderFactors V y μ ν ell).map (conjBy (S0 * holFar)))
          (surfaceAlong V y0 μ ell accν rest) =
          ((ladderFactors V y μ ν ell).map (conjBy (S0 * holFar))) ++
            surfaceAlong V y0 μ ell accν rest from rfl, List.prod_append, hmap]
      have ih' := ih accν
      have hmul := congrArg (fun z : SU2 => z * (surfaceAlong V y0 μ ell accν rest).prod) hstep
      simp [mul_assoc, y, S0, holFar, accν] at hmul ih' ⊢
      rw [hmul, ih']

def loopSurfaceFactors (V : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) : List SU2 :=
  surfaceAlong V c.1 c.2 ell [] (coarseGammaPath 1 c.1 x)

/-- Uniform C1 plaquette-count majorant. Equals `3 ell (ell-1)`; saturates to `0`
at `ell ≤ 1`. -/
def loopSurfaceBound (ell : ℕ) : ℕ := 3 * ell * (ell - 1)

theorem loopSurfaceFactors_length_le (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hx : x ∈ stepBlockOf c.1 1 ell) :
    (loopSurfaceFactors V ell c x).length ≤ loopSurfaceBound ell := by
  have hxB : x ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf c.1 ell := by
    rwa [← stepBlockOf_one]
  have hin : inBlock c.1 ell x := (mem_blockOf).mp hxB
  have hγ : (coarseGammaPath 1 c.1 x).length ≤ 3 * (ell - 1) :=
    coarseGammaPath_one_length_le hin
  have hlen := surfaceAlong_length_le V c.1 c.2 ell [] (coarseGammaPath 1 c.1 x)
  unfold loopSurfaceFactors loopSurfaceBound
  have : ell * (coarseGammaPath 1 c.1 x).length ≤ ell * (3 * (ell - 1)) :=
    Nat.mul_le_mul_left _ hγ
  have hmul : ell * (3 * (ell - 1)) = 3 * ell * (ell - 1) := by ring
  omega

theorem loopSurfaceFactors_prod (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hx : x ∈ stepBlockOf c.1 1 ell) :
    (loopSurfaceFactors V ell c x).prod = loopVar 1 ell V c x := by
  have hx' := mem_stepBlockOf.mp hx
  have hend : coarsePathEndpoint 1 c.1 (coarseGammaPath 1 c.1 x) = x :=
    coarsePathEndpoint_coarseGammaPath (fun μ => ⟨(hx' μ).1, one_dvd _⟩)
  have hfar : cPlusS 1 ell c = coarseShift c.1 ell c.2 := by
    rw [cPlusS_eq, one_mul]
  have hfill := surfaceAlong_prod V c.1 c.2 ell [] (coarseGammaPath 1 c.1 x)
  unfold loopSurfaceFactors loopVar gammaVarStrided coarseBondVar
  rw [hfar]
  simp [holonomyFactors_nil, List.append, hend, segmentHol, holonomyFactors_prod,
    mul_assoc] at hfill ⊢
  have hcancel :
      coarsePathHolonomy 1 V c.1 (List.replicate ell c.2) *
          ((coarsePathHolonomy 1 V c.1 (List.replicate ell c.2))⁻¹ *
            (surfaceAlong V c.1 c.2 ell [] (coarseGammaPath 1 c.1 x)).prod) =
        (surfaceAlong V c.1 c.2 ell [] (coarseGammaPath 1 c.1 x)).prod := by
    simp [← mul_assoc, mul_inv_cancel]
  exact hcancel.symm.trans hfill

/-- Explicit C1 radius from printed (109) plaquette data. `N(ell) = 3 ell (ell-1)`
conjugated unit plaquettes, each of angle `≤ (π/(2√2)) α0`. -/
def loopRhoPlaq (eps0 : ℝ) (ell : ℕ) : ℝ :=
  (loopSurfaceBound ell : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * eps0)

def loopRhoPlaqCap (eps0 : ℝ) (ell : ℕ) : ℝ :=
  (loopSurfaceBound ell : ℝ) * ((Real.pi / 4) * eps0)

theorem loopRhoPlaq_lt_half_of_n_eps0 {ell : ℕ} {eps0 : ℝ}
    (hsmall : (loopSurfaceBound ell : ℝ) * eps0 < Real.sqrt 2) :
    loopRhoPlaq eps0 ell < Real.pi / 2 := by
  unfold loopRhoPlaq
  have hrew :
      (loopSurfaceBound ell : ℝ) * ((Real.pi / (2 * Real.sqrt 2)) * eps0) =
        (Real.pi / (2 * Real.sqrt 2)) * ((loopSurfaceBound ell : ℝ) * eps0) := by
    ring
  rw [hrew]
  calc
    (Real.pi / (2 * Real.sqrt 2)) * ((loopSurfaceBound ell : ℝ) * eps0)
        < (Real.pi / (2 * Real.sqrt 2)) * Real.sqrt 2 :=
      mul_lt_mul_of_pos_left hsmall (by positivity)
    _ = Real.pi / 2 := by field_simp

theorem loopRhoPlaqCap_lt_half_of_n_eps0 {ell : ℕ} {eps0 : ℝ}
    (hsmall : (loopSurfaceBound ell : ℝ) * eps0 < 2) :
    loopRhoPlaqCap eps0 ell < Real.pi / 2 := by
  unfold loopRhoPlaqCap
  have hm :=
    mul_lt_mul_of_pos_left hsmall (by positivity : 0 < Real.pi / 4)
  nlinarith [hm]

theorem su2Angle_plaq_le_frob (V : PeriodicLinkConfiguration SU2 L)
    (eps0 : ℝ) (h0 : 0 ≤ eps0)
    (hV : ∀ p : PeriodicLatticePlaquette L,
      frobNorm ((periodicPlaquetteHolonomy (G := SU2) V p : M2) - 1) ≤ eps0)
    (p : PeriodicLatticePlaquette L) :
    su2Angle (periodicPlaquetteHolonomy (G := SU2) V p) ≤
      (Real.pi / (2 * Real.sqrt 2)) * eps0 :=
  (su2Angle_le_frobNorm (periodicPlaquetteHolonomy (G := SU2) V p)).trans
    (mul_le_mul_of_nonneg_left (hV p) (by positivity))

theorem su2Angle_plaq_le_frob_cap (V : PeriodicLinkConfiguration SU2 L)
    (eps0 : ℝ) (heps : eps0 ≤ 2)
    (hV : ∀ p : PeriodicLatticePlaquette L,
      frobNorm ((periodicPlaquetteHolonomy (G := SU2) V p : M2) - 1) ≤ eps0)
    (p : PeriodicLatticePlaquette L) :
    su2Angle (periodicPlaquetteHolonomy (G := SU2) V p) ≤ (Real.pi / 4) * eps0 :=
  (su2Angle_le_frobNorm_cap ((hV p).trans heps)).trans
    (mul_le_mul_of_nonneg_left (hV p) (by positivity))

theorem nu_loopVar_le_surface_mul (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (delta : ℝ) (hδ : 0 ≤ delta)
    (h : ∀ p : PeriodicLatticePlaquette L,
      su2Angle (periodicPlaquetteHolonomy V p) ≤ delta)
    (hx : x ∈ stepBlockOf c.1 1 ell)
    (hsmall : (loopSurfaceBound ell : ℝ) * delta < Real.pi / 2) :
    nu ((principalSuTwoLog (loopVar 1 ell V c x) : SuTwo) : M2) ≤
        (loopSurfaceBound ell : ℝ) * delta ∧
      (loopSurfaceBound ell : ℝ) * delta < Real.pi / 2 := by
  have hprod := loopSurfaceFactors_prod V ell c x hx
  have hfac : ∀ g ∈ loopSurfaceFactors V ell c x, su2Angle g ≤ delta :=
    fun g hg => su2Angle_mem_surfaceAlong V c.1 c.2 ell [] (coarseGammaPath 1 c.1 x) delta h hg
  have hlen : ((loopSurfaceFactors V ell c x).length : ℝ) ≤ (loopSurfaceBound ell : ℝ) :=
    Nat.cast_le.mpr (loopSurfaceFactors_length_le V ell c x hx)
  have hlen_small :
      ((loopSurfaceFactors V ell c x).length : ℝ) * delta < Real.pi / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hlen hδ) hsmall
  have hpt := principal_list_prod_small (loopSurfaceFactors V ell c x) delta hfac hlen_small
  rw [hprod] at hpt
  exact ⟨hpt.1.trans (mul_le_mul_of_nonneg_right hlen hδ), hsmall⟩

/-- Perturbed-link consumer under the per-bond strengthening `NearIdentity109`
(strictly stronger than printed (109) on V0). `eps1 ≤ π` is an extra analytic
hypothesis, not printed (109). The conclusion is non-strict `ν ≤ ρ`. -/
theorem nu_loopVar_perturbed_le_rho
    (V0 : PeriodicLinkConfiguration SU2 L)
    (X : PeriodicLatticeEdge L → M2) (eps0 eps1 : ℝ)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (h : NearIdentity109 V0 X eps0 eps1) (hpi : eps1 ≤ Real.pi)
    (h0 : 0 ≤ eps0) (h1 : 0 ≤ eps1)
    (hx : x ∈ stepBlockOf c.1 1 ell)
    (hsmall : loopRho eps0 eps1 ell < Real.pi / 2) :
    nu ((principalSuTwoLog
          (loopVar 1 ell (perturbedConfig V0 X) c x) : SuTwo) : M2) ≤
        loopRho eps0 eps1 ell ∧
      loopRho eps0 eps1 ell < Real.pi / 2 := by
  set delta : ℝ := (Real.pi / (2 * Real.sqrt 2)) * eps0 + eps1
  have hδ : 0 ≤ delta :=
    add_nonneg (mul_nonneg (by positivity) h0) h1
  have hV : ∀ e, su2Angle (perturbedConfig V0 X e) ≤ delta :=
    fun e => su2Angle_perturbedConfig_le V0 X eps0 eps1 h hpi e
  exact nu_loopVar_le_bound_mul (perturbedConfig V0 X) ell c x delta hδ hV hx hsmall

/-- Per-bond background-only form. Strictly stronger V0 hypothesis than printed
(109); retained as a named lemma, not as a (109) match. -/
theorem nu_loopVar_V0_bond_le_rho
    (V0 : PeriodicLinkConfiguration SU2 L) (eps0 : ℝ)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hV : ∀ e, frobNorm ((V0 e : M2) - 1) ≤ eps0)
    (h0 : 0 ≤ eps0)
    (hx : x ∈ stepBlockOf c.1 1 ell)
    (hsmall : loopRho eps0 0 ell < Real.pi / 2) :
    nu ((principalSuTwoLog (loopVar 1 ell V0 c x) : SuTwo) : M2) ≤
        loopRho eps0 0 ell ∧
      loopRho eps0 0 ell < Real.pi / 2 := by
  set delta : ℝ := (Real.pi / (2 * Real.sqrt 2)) * eps0
  have hδ : 0 ≤ delta := mul_nonneg (by positivity) h0
  have hAng : ∀ e, su2Angle (V0 e) ≤ delta := by
    intro e
    exact (su2Angle_le_frobNorm (V0 e)).trans
      (mul_le_mul_of_nonneg_left (hV e) (by positivity))
  simpa [loopRho, delta] using
    nu_loopVar_le_bound_mul V0 ell c x delta hδ hAng hx (by simpa [loopRho, delta] using hsmall)

/-- Per-bond cap form; same honesty as `nu_loopVar_V0_bond_le_rho`. -/
theorem nu_loopVar_V0_bond_le_rhoCap
    (V0 : PeriodicLinkConfiguration SU2 L) (eps0 : ℝ)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hV : ∀ e, frobNorm ((V0 e : M2) - 1) ≤ eps0)
    (heps : eps0 ≤ 2) (h0 : 0 ≤ eps0)
    (hx : x ∈ stepBlockOf c.1 1 ell)
    (hsmall : loopRhoCap eps0 ell < Real.pi / 2) :
    nu ((principalSuTwoLog (loopVar 1 ell V0 c x) : SuTwo) : M2) ≤
        loopRhoCap eps0 ell ∧
      loopRhoCap eps0 ell < Real.pi / 2 := by
  set delta : ℝ := (Real.pi / 4) * eps0
  have hδ : 0 ≤ delta := mul_nonneg (by positivity) h0
  have hAng : ∀ e, su2Angle (V0 e) ≤ delta := by
    intro e
    exact (su2Angle_le_frobNorm_cap ((hV e).trans heps)).trans
      (mul_le_mul_of_nonneg_left (hV e) (by positivity))
  simpa [loopRhoCap, delta] using
    nu_loopVar_le_bound_mul V0 ell c x delta hδ hAng hx
      (by simpa [loopRhoCap, delta] using hsmall)

/-- Background-only form from printed (109): V0 **plaquette** smallness, global
coefficient `π/(2√2)`, radius `N(ell)·(π/(2√2)) α0` with `N = 3 ell (ell-1)`. -/
theorem nu_loopVar_V0_le_rho
    (V0 : PeriodicLinkConfiguration SU2 L) (eps0 : ℝ)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hV : ∀ p : PeriodicLatticePlaquette L,
      frobNorm ((periodicPlaquetteHolonomy (G := SU2) V0 p : M2) - 1) ≤ eps0)
    (h0 : 0 ≤ eps0)
    (hx : x ∈ stepBlockOf c.1 1 ell)
    (hsmall : loopRhoPlaq eps0 ell < Real.pi / 2) :
    nu ((principalSuTwoLog (loopVar 1 ell V0 c x) : SuTwo) : M2) ≤
        loopRhoPlaq eps0 ell ∧
      loopRhoPlaq eps0 ell < Real.pi / 2 := by
  set delta : ℝ := (Real.pi / (2 * Real.sqrt 2)) * eps0
  have hδ : 0 ≤ delta := mul_nonneg (by positivity) h0
  have hAng : ∀ p, su2Angle (periodicPlaquetteHolonomy (G := SU2) V0 p) ≤ delta :=
    fun p => su2Angle_plaq_le_frob V0 eps0 h0 hV p
  simpa [loopRhoPlaq, delta] using
    nu_loopVar_le_surface_mul V0 ell c x delta hδ hAng hx
      (by simpa [loopRhoPlaq, delta] using hsmall)

/-- Sharper printed-(109) form on `‖V0(∂p)-1‖_F ≤ 2`. -/
theorem nu_loopVar_V0_le_rhoCap
    (V0 : PeriodicLinkConfiguration SU2 L) (eps0 : ℝ)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hV : ∀ p : PeriodicLatticePlaquette L,
      frobNorm ((periodicPlaquetteHolonomy (G := SU2) V0 p : M2) - 1) ≤ eps0)
    (heps : eps0 ≤ 2) (h0 : 0 ≤ eps0)
    (hx : x ∈ stepBlockOf c.1 1 ell)
    (hsmall : loopRhoPlaqCap eps0 ell < Real.pi / 2) :
    nu ((principalSuTwoLog (loopVar 1 ell V0 c x) : SuTwo) : M2) ≤
        loopRhoPlaqCap eps0 ell ∧
      loopRhoPlaqCap eps0 ell < Real.pi / 2 := by
  set delta : ℝ := (Real.pi / 4) * eps0
  have hδ : 0 ≤ delta := mul_nonneg (by positivity) h0
  have hAng : ∀ p, su2Angle (periodicPlaquetteHolonomy (G := SU2) V0 p) ≤ delta :=
    fun p => su2Angle_plaq_le_frob_cap V0 eps0 heps hV p
  simpa [loopRhoPlaqCap, delta] using
    nu_loopVar_le_surface_mul V0 ell c x delta hδ hAng hx
      (by simpa [loopRhoPlaqCap, delta] using hsmall)

/-- Strict printed (109) wrapper for the background-only C1 bound. Uses only the
V0-plaquette conjunct; does **not** upgrade `ν ≤ ρ` to `ν < ρ`. The perturbation
coordinates `X`/`eps1` are part of printed (109) but do not enter this
background-only conclusion. -/
theorem nu_loopVar_printed109_le_rho
    (V0 : PeriodicLinkConfiguration SU2 L)
    (X : PeriodicLatticeEdge L → M2) (eps0 eps1 : ℝ)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (h : Printed109 V0 X eps0 eps1)
    (h0 : 0 ≤ eps0)
    (hx : x ∈ stepBlockOf c.1 1 ell)
    (hsmall : loopRhoPlaq eps0 ell < Real.pi / 2) :
    nu ((principalSuTwoLog (loopVar 1 ell V0 c x) : SuTwo) : M2) ≤
        loopRhoPlaq eps0 ell ∧
      loopRhoPlaq eps0 ell < Real.pi / 2 :=
  nu_loopVar_V0_le_rho V0 eps0 ell c x (fun p => le_of_lt (h.1 p)) h0 hx hsmall

#print axioms holonomyFactors_prod
#print axioms loopFactors_prod
#print axioms loopFactors_length
#print axioms loopFactors_length_le_bound
#print axioms coarseGammaPath_one_length_le
#print axioms nu_loopVar_le_length_mul
#print axioms nu_loopVar_le_bound_mul
#print axioms loopSurfaceFactors_prod
#print axioms nu_loopVar_le_surface_mul
#print axioms nu_loopVar_perturbed_le_rho
#print axioms nu_loopVar_printed109_le_rho
#print axioms nu_loopVar_V0_le_rho
#print axioms nu_loopVar_V0_le_rhoCap
#print axioms nu_loopVar_V0_bond_le_rho
#print axioms loopRho_lt_half_of_n_eps0
#print axioms loopRhoCap_lt_half_of_n_eps0
#print axioms loopRhoPlaq_lt_half_of_n_eps0
#print axioms loopRhoPlaqCap_lt_half_of_n_eps0
#print axioms loopRho_lt_half_of_split
#print axioms n_eps0_lt_sqrt2_of_div

end SmallnessBridge.Assemble
