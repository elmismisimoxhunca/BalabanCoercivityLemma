/-
M1Proof.lean — **M1: iteration of averages / composition law** (CMP98 (89)–(92)).

Tranche `m1-si1-multiscale`, M1 stage.  Owner directory: `compute/m1_si1_multiscale/m1g/`.
Spec (read-only): `compute/m1_si1_multiscale/spec/SPEC.md` + `spec/MultiscaleTarget.lean`
(compiled skeleton, namespace `AdalySI1.Multiscale`, imported here as the hash-verified
olean pair `m1g/specdep/MultiscaleTarget.{olean,lean}` — sha256 recorded in
`m1g/REPORT.md`).  Corpus: `compute/m1_si1_multiscale/corpus_extract/CMP98_90_91_110.md`.
Source draft reused from `m1/M1Proof.lean` (sha256 649d1dca…; never compiled there).

WHAT IS PROVED HERE (no `sorry`, no new axioms — audited in §5):

* **M1.1 — the stride lift.**  `modifiedAverageS s V0 ell V1 c` is CMP98 (89)/(63) with the
  general-stride primitives the spec names: `cPlusS s ell` for `cPlus ell`, `ubarSU2 s ell`
  for `ubarSU2 1 ell`, and the stride-`s` tree transport `rZeroPathS s` along
  `coarseGammaPath s` over the strided block `stepBlockOf _ s ell` for the stride-1 pair
  `(rZeroPath, GammaPath, blockOf)`.  Reduction theorem `modifiedAverageS_one_eq`:
  `modifiedAverageS 1 = modifiedAverage` LITERALLY, via the bridges
  `rZeroPathS_one_eq` (stride-1 strided fold = fine signed fold along the SAME staircase,
  using the tree's proved `StridedAveraging.coarseGammaPath_one_map`),
  `stepBlockOf_one` (proved in `QjComposite`), and `cPlusS_one` (from `cPlusS_eq`).
* **M1.2 — the iterated average.**  `iteratedAverage bg ell` is the (90)/(91) recursion
  (`iteratedAverage_zero`/`iteratedAverage_succ` are definitional laws,
  `iteratedAverage_one` is CMP98's (92) base case: one level IS (63)).  Mixed-scale
  (Tanimoto) variant `maskedIteratedAverage` with per-level bond masks, instantiated at a
  `RegionTower` by `regionBondMask`/`regionIteratedAverage` (average `c` at level `j+1`
  only when `bondSupport (ell^j) ell c ⊆ region j` — the conservative boundary convention,
  M3.3's chosen branch); `maskedIteratedAverage_eq_iteratedAverage_of_forall` records that
  the global iteration is the full-mask special case.
* **M1.3a — the iterated operator satisfies the (88) recursion.**  `iteratedAverageFrom`
  (base-stride-generalized iteration) with the COMPOSITION/SPLITTING LAW
  `iteratedAverageFrom_add`: the `(j+k)`-th order operation IS the `k`-th order operation
  at base stride `s·ell^j` with shifted backgrounds, applied to the `j`-th order output —
  CMP98 (91)'s "composition of the operation (89) for `V0 = Ū^j` and of the `j`-th order
  operation", at any split point.  `selfConsistentTower_eq_iteratedAverage` realizes
  CMP98 (91)'s self-consistent background choice `V0 = Ū^j` concretely: the prescribed-`bg`
  iteration at `bg = selfConsistentTower ell U` reproduces the self-consistent chain.
* **M1.3b — DEFERRED, NOT FAKED.**  The identification of `iteratedAverage` with an
  INDEPENDENTLY formalized CMP98 (88) `globalAverage` is impossible today: the tree has no
  (88) object (grep: no `globalAverage`; the (77)/(87) gauge transformations that define
  the `k`-th order average in (88) are not formalized — `UbarTowerCov.UbarTower` is the
  RAW background tower (43), not (88)).  The exact deferred statement is in §4 below.

Sources: CMP98 pp.31–34 (88)–(96) via the coordinator extract; the Tanimoto
successive-averaging clarification (decreasing `Ω_j`, exterior left at the finer scale).
Read discipline: the two spec files whole; everything else by grep + ≤80-line windows.
-/

import MultiscaleTarget
import AdalyFormal.Balaban.StridedAveraging
import Lean.Util.CollectAxioms

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

namespace AdalySI1.Multiscale.M1

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log)
open AdalySI1.ModifiedAverageDeriv
  (modifiedAverage endpointAvg rZeroPath rZeroPathStep configMul groupConj cPlus)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepBlockOf_one)
open AdalyFormal.Balaban.Q1Real (GammaPath)
open AdalyFormal.Balaban.StridedAveraging (coarseGammaPath_one_map)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — M1.1: the stride lift `modifiedAverageS`

`ModifiedAverageDeriv`'s objects are hardwired at stride `1` (its §7 explicitly defers
general stride and names `cPlusS` as the deferred primitive).  The lift proceeds factor by
factor: first the tree-gauge transport fold `rZeroPath` (CMP98 (58)) gets a stride-`s`
analogue `rZeroPathS` whose steps advance by `coarseShift · s μ` along the FORWARD strided
staircase `coarseGammaPath s` (the only direction pattern `endpointAvg`'s block paths use);
then the endpoint factor `endpointAvg` (CMP98 (110)/(63)) is re-pointed at
`stepBlockOf _ s ell`; finally `modifiedAverageS` reassembles (63)'s four-factor product
with `ubarSU2 s ell` (already stride-general, `BlockedBackground`) and `cPlusS s ell`. -/

/-- **Stride-`s` tree-gauge transport step** — `ModifiedAverageDeriv.rZeroPathStep` with the
fine unit step `periodicLatticeStep x (μ, true)` replaced by the strided shift
`coarseShift x s μ` (and only the forward branch kept: `coarseGammaPath s` emits forward
steps only).  The conjugation structure is (58)'s, unchanged: the running `V0`-holonomy
`st.2.1` transports each bond factor into the tree frame before it is multiplied in. -/
def rZeroPathStepS (s : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L) :
    (PeriodicLatticeSite L × SU2 × SU2) → Fin 3 → (PeriodicLatticeSite L × SU2 × SU2) :=
  fun st μ =>
    (coarseShift st.1 s μ, st.2.1 * V0 (st.1, μ),
      st.2.2 * groupConj st.2.1 (V1 (st.1, μ)))

/-- **`(R_{0,y}V₁)` at stride `s`** along a forward strided path — the stride-`s` analogue of
`ModifiedAverageDeriv.rZeroPath` (CMP98 (58)). -/
noncomputable def rZeroPathS (s : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (base : PeriodicLatticeSite L) (steps : List (Fin 3)) : SU2 :=
  (steps.foldl (rZeroPathStepS s V0 V1) (base, 1, 1)).2.2

/-- **Step-level stride-1 bridge (definitional).**  At `s = 1` one strided forward step IS
one fine forward signed step: `coarseShift x 1 μ` unfolds to
`periodicLatticeShift x μ = Function.update x μ (x μ + 1) = periodicLatticeStep x (μ, true)`,
and the `(μ, true)` branch of `rZeroPathStep` selects exactly the two factors above. -/
theorem rZeroPathStepS_one_eq (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (st : PeriodicLatticeSite L × SU2 × SU2) (μ : Fin 3) :
    rZeroPathStepS 1 V0 V1 st μ = rZeroPathStep V0 V1 st (μ, true) := rfl

/-- **Fold-level stride-1 bridge**: the stride-1 strided fold along `steps` equals the fine
signed fold along `steps.map (·, true)` — for EVERY initial transport state, which is what
the induction needs. -/
theorem foldl_rZeroPathStepS_one (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (steps : List (Fin 3)) (st : PeriodicLatticeSite L × SU2 × SU2) :
    (steps.foldl (rZeroPathStepS 1 V0 V1) st).2.2
      = ((steps.map fun μ => (μ, true)).foldl (rZeroPathStep V0 V1) st).2.2 := by
  induction steps generalizing st with
  | nil => rfl
  | cons μ rest ih =>
      rw [List.foldl_cons, List.map_cons, List.foldl_cons, rZeroPathStepS_one_eq]
      exact ih _

/-- **Path-level stride-1 bridge**: at `s = 1` the strided tree transport along
`coarseGammaPath 1 y x` IS CMP98 (58)'s `rZeroPath` along `GammaPath y x` — via the tree's
proved staircase bridge `coarseGammaPath_one_map`.  Unconditional (both contours wrap the
same way off-block). -/
theorem rZeroPathS_one_eq (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (y x : PeriodicLatticeSite L) :
    rZeroPathS 1 V0 V1 y (coarseGammaPath 1 y x) = rZeroPath V0 V1 y (GammaPath y x) := by
  unfold rZeroPathS rZeroPath
  rw [foldl_rZeroPathStepS_one, coarseGammaPath_one_map]

/-- **Endpoint tree-gauge average at stride `s`** — CMP98 (110)/(63)'s
`exp[Σ_{x∈B(y)} L⁻ᵈ log (R_{0,y}V₁)(Γ_{y,x})]` with the strided block `stepBlockOf y s ell`
and the strided transport.  Same `ell⁻³` weight as `endpointAvg` (the normalization split is
inherited unchanged). -/
noncomputable def endpointAvgS (s : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (y : PeriodicLatticeSite L) : SU2 :=
  su2Exp (∑ x ∈ stepBlockOf y s ell,
    ((ell : ℚ) ^ 3)⁻¹ • su2Log (rZeroPathS s V0 V1 y (coarseGammaPath s y x)))

/-- **Endpoint-factor stride-1 reduction**: at `s = 1`, `endpointAvgS` IS
`ModifiedAverageDeriv.endpointAvg` — `stepBlockOf_one` identifies the blocks,
`rZeroPathS_one_eq` the summands. -/
theorem endpointAvgS_one_eq (V0 V1 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (y : PeriodicLatticeSite L) :
    endpointAvgS 1 V0 V1 ell y = endpointAvg V0 V1 ell y := by
  unfold endpointAvgS endpointAvg
  rw [stepBlockOf_one]
  refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
  rw [rZeroPathS_one_eq]

/-- **Far-endpoint stride-1 bridge**: `cPlusS 1 ell c = pathSite c.1 c.2 ell`, i.e.
`ModifiedAverageDeriv.cPlus` — both sides unfold to `(periodicLatticeShift · c.2)^[ell] c.1`
(`cPlusS_eq` then `1 * ell = ell`). -/
theorem cPlusS_one (ell : ℕ) (c : PeriodicLatticeEdge L) :
    cPlusS 1 ell c = cPlus ell c := by
  have h := cPlusS_eq 1 ell c
  rw [Nat.one_mul] at h
  exact h

/-- **M1.1, the stride lift.**  CMP98 (89)/(63) at fine stride `s` with block factor `ell`:
`(R_{0,c₋}V₁)⁻¹ · (ū(V₁·V₀) c · (ū V₀ c)⁻¹) · groupConj (ū V₀ c) (R_{0,c₊}V₁)` where
`ū = ubarSU2 s ell`, the endpoint factors are `endpointAvgS s`, and the far endpoint is
`cPlusS s ell c` (`s * ell` unit steps — the deferred general-stride primitive
`ModifiedAverageDeriv` §7 names).  `V0` is the level background, `V1` the field averaged. -/
noncomputable def modifiedAverageS (s : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (V1 : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L) : SU2 :=
  (endpointAvgS s V0 V1 ell c.1)⁻¹
    * (ubarSU2 s ell (configMul V1 V0) c * (ubarSU2 s ell V0 c)⁻¹)
    * groupConj (ubarSU2 s ell V0 c) (endpointAvgS s V0 V1 ell (cPlusS s ell c))

/-- **M1.1 REDUCTION THEOREM** (spec acceptance: "`s = 1` reductions are `rfl`/bridge
lemmas"): at stride `1` the lift IS CMP98 (63), literally —
`modifiedAverageS 1 = modifiedAverage` as functions. -/
theorem modifiedAverageS_one_eq :
    modifiedAverageS (L := L) 1 = modifiedAverage (L := L) := by
  funext V0 ell V1 c
  unfold modifiedAverageS modifiedAverage
  rw [endpointAvgS_one_eq, endpointAvgS_one_eq, cPlusS_one]

/-! ## §2 — M1.2: the iterated average (CMP98 (90)/(91)) and the mixed-scale variant

(90): `Ū¹ := R(U⁰) U¹`; (91): `Ū^{j+1} := R(Ū^j)(j-th order operation)` — ONE application
of (89), at fine stride `ell^j` with block factor `ell`, background `bg j`.  The background
family is prescribed (frozen for the linearization, SPEC §2.4); at the physical point
`bg j = Ū^j` self-consistently (§3's `selfConsistentTower` realizes this).  Level `j` lives
on the stride-`ell^j` sublattice, exactly the scale bookkeeping of the spec. -/

/-- **`iteratedAverage` — the (90)/(91) recursion.**  Level `0` is the field itself; level
`j+1` is one stride-`s = ell^j` modified average of the level-`j` output against the
prescribed level background `bg j`. -/
noncomputable def iteratedAverage (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) :
    (j : ℕ) → PeriodicLinkConfiguration SU2 L → PeriodicLinkConfiguration SU2 L
  | 0, U => U
  | (j + 1), U => modifiedAverageS (ell ^ j) (bg j) ell (iteratedAverage bg ell j U)

/-- **(90)'s base**: level `0` is the identity operation. -/
theorem iteratedAverage_zero (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (U : PeriodicLinkConfiguration SU2 L) : iteratedAverage bg ell 0 U = U := rfl

/-- **(91), the recursion law**: level `j+1` IS one (89)-step at fine stride `ell^j` with
background `bg j` applied to the level-`j` output. -/
theorem iteratedAverage_succ (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) (j : ℕ)
    (U : PeriodicLinkConfiguration SU2 L) :
    iteratedAverage bg ell (j + 1) U
      = modifiedAverageS (ell ^ j) (bg j) ell (iteratedAverage bg ell j U) := rfl

/-- **CMP98 (92)'s induction base** — "for `k = 1` the equality holds by the definitions
(89), (90), and Eq. (63)": the level-1 iterate is LITERALLY one `modifiedAverage` (63),
by `pow_zero` and the M1.1 reduction `modifiedAverageS_one_eq`. -/
theorem iteratedAverage_one (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (U : PeriodicLinkConfiguration SU2 L) :
    iteratedAverage bg ell 1 U = modifiedAverage (bg 0) ell U := by
  have h := iteratedAverage_succ bg ell 0 U
  rw [show (0 + 1 : ℕ) = 1 from rfl] at h
  rw [h, iteratedAverage_zero, pow_zero, modifiedAverageS_one_eq]

/-- **Masked (mixed-scale) one-step average at stride `s`** — the stride lift of the spec's
`maskedModifiedAverage`: CMP98 (63) values on the bonds selected by `S`, the UNTOUCHED
finer field elsewhere (Tanimoto: "the rest is left in a finer scale"). -/
noncomputable def maskedModifiedAverageS (s : ℕ) (V0 : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (V1 : PeriodicLinkConfiguration SU2 L) (S : PeriodicLatticeEdge L → Prop)
    (c : PeriodicLatticeEdge L) : SU2 :=
  if S c then modifiedAverageS s V0 ell V1 c else V1 c

/-- **Masked stride-1 reduction**: at `s = 1` the masked lift IS the spec's
`maskedModifiedAverage`, pointwise.  Function-extensional equality is impossible:
`modifiedAverage`/`modifiedAverageS` take `(V0, ell, V1)` while the spec's
`maskedModifiedAverage` takes `(V0, V1, ell)`. -/
theorem maskedModifiedAverageS_one_eq
    (V0 V1 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (S : PeriodicLatticeEdge L → Prop) (c : PeriodicLatticeEdge L) :
    maskedModifiedAverageS 1 V0 ell V1 S c = maskedModifiedAverage V0 V1 ell S c := by
  unfold maskedModifiedAverageS maskedModifiedAverage
  rw [modifiedAverageS_one_eq]

/-- **The mixed-scale iterated average** (Tanimoto's successive averaging): at level `j+1`,
only the bonds selected by the level mask `M j` are averaged (one (89)-step at fine stride
`ell^j`, background `bg j`); every other bond keeps its finer-scale value. -/
noncomputable def maskedIteratedAverage (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (M : ℕ → PeriodicLatticeEdge L → Prop) :
    (j : ℕ) → PeriodicLinkConfiguration SU2 L → PeriodicLinkConfiguration SU2 L
  | 0, U => U
  | (j + 1), U =>
      maskedModifiedAverageS (ell ^ j) (bg j) ell (maskedIteratedAverage bg ell M j U) (M j)

theorem maskedIteratedAverage_zero (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (M : ℕ → PeriodicLatticeEdge L → Prop) (U : PeriodicLinkConfiguration SU2 L) :
    maskedIteratedAverage bg ell M 0 U = U := rfl

theorem maskedIteratedAverage_succ (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (M : ℕ → PeriodicLatticeEdge L → Prop) (j : ℕ) (U : PeriodicLinkConfiguration SU2 L) :
    maskedIteratedAverage bg ell M (j + 1) U
      = maskedModifiedAverageS (ell ^ j) (bg j) ell (maskedIteratedAverage bg ell M j U)
          (M j) := rfl

/-- **The global iteration is the full-mask special case** (Tanimoto: `Ω_j = whole torus`
recovers CMP98's global chain). -/
theorem maskedIteratedAverage_eq_iteratedAverage_of_forall
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (M : ℕ → PeriodicLatticeEdge L → Prop) (hM : ∀ j c, M j c)
    (j : ℕ) (U : PeriodicLinkConfiguration SU2 L) :
    maskedIteratedAverage bg ell M j U = iteratedAverage bg ell j U := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [maskedIteratedAverage_succ, iteratedAverage_succ, ih]
      funext c
      show (if M j c then modifiedAverageS (ell ^ j) (bg j) ell (iteratedAverage bg ell j U) c
              else (iteratedAverage bg ell j U) c)
          = modifiedAverageS (ell ^ j) (bg j) ell (iteratedAverage bg ell j U) c
      rw [if_pos (hM j c)]

/-- **The level-`j` bond mask of a region tower** — a level-`(j+1)` coarse bond may be
averaged only when its whole stride-`(ell^j)` support (CMP98 (89)/(92) locality
`B(c₋) ∪ B(c₊)`, the spec's `bondSupport`) lies inside `region j`.  This is M3.1's
admissibility condition used as the mask, with the conservative boundary convention
(M3.3's chosen branch: boundary-crossing bonds are NOT averaged). -/
def regionBondMask (R : RegionTower L) (ell : ℕ) (j : ℕ) (c : PeriodicLatticeEdge L) : Prop :=
  bondSupport (ell ^ j) ell c ⊆ R.region j

/-- **The mixed-scale iterated average of a region tower** — the Tanimoto large/small-field
operator: decreasing regions `Ω_j = R.region j`, exterior left at the finer scale. -/
noncomputable def regionIteratedAverage (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (R : RegionTower L) :
    (j : ℕ) → PeriodicLinkConfiguration SU2 L → PeriodicLinkConfiguration SU2 L :=
  maskedIteratedAverage bg ell (regionBondMask R ell)

/-! ## §3 — M1.3a: the iterated operator satisfies the (88) recursion

CMP98 (88) defines the `k`-th order average as a single operation and (91)/(92) identify it
with the `k`-fold composition of (63) at backgrounds `Ū^j`.  The recursion content of (88)
— provable WITHOUT the (77)/(87) gauge transformations — is: (i) the `k = 1` reduction to
(63) (`iteratedAverage_one`, §2), and (ii) the COMPOSITION/SPLITTING LAW: the `(j + k)`-th
order operation is the `k`-th order operation at base stride `s · ell^j` (with shifted
backgrounds `bg (j + ·)`) applied to the `j`-th order output.  `iteratedAverageFrom`
generalizes `iteratedAverage` with a base stride so the split is statable; the base-`1`
bridge closes the loop. -/

/-- **Base-stride-generalized iteration**: the `j`-fold composition of (89)-steps starting
at fine stride `s` (level `i` uses fine stride `s · ell^i`, block factor `ell`).  At
`s = 1` this is `iteratedAverage` (`iteratedAverage_eq_iteratedAverageFrom_one`). -/
noncomputable def iteratedAverageFrom (s : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) :
    (j : ℕ) → PeriodicLinkConfiguration SU2 L → PeriodicLinkConfiguration SU2 L
  | 0, U => U
  | (j + 1), U => modifiedAverageS (s * ell ^ j) (bg j) ell (iteratedAverageFrom s bg ell j U)

theorem iteratedAverageFrom_zero (s : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L) :
    iteratedAverageFrom s bg ell 0 U = U := rfl

theorem iteratedAverageFrom_succ (s : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (j : ℕ) (U : PeriodicLinkConfiguration SU2 L) :
    iteratedAverageFrom s bg ell (j + 1) U
      = modifiedAverageS (s * ell ^ j) (bg j) ell (iteratedAverageFrom s bg ell j U) := rfl

/-- **Base-stride-1 bridge**: the generalized iteration at `s = 1` IS `iteratedAverage`
(strides `1 · ell^j = ell^j`). -/
theorem iteratedAverage_eq_iteratedAverageFrom_one
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) (j : ℕ)
    (U : PeriodicLinkConfiguration SU2 L) :
    iteratedAverage bg ell j U = iteratedAverageFrom 1 bg ell j U := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [iteratedAverage_succ, iteratedAverageFrom_succ, ih, Nat.one_mul]

/-- **M1.3a, THE COMPOSITION/SPLITTING LAW.**  The `(j + k)`-fold iterate from stride `s`
IS the `k`-fold iterate from stride `s · ell^j` — with the backgrounds shifted to
`bg (j + ·)` — applied to the `j`-fold output.  This is CMP98 (91)'s "composition of the
operation (89) for `V0 = Ū^j` and of the `j`-th order operation", iterated: the (88)
`k`-th order operation obeys exactly this splitting, and the iterated operator satisfies it
by induction.  No gauge input; `pow_add` does the scale bookkeeping `ell^(j+k) =
ell^j · ell^k`. -/
theorem iteratedAverageFrom_add (s : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (ell j k : ℕ) (U : PeriodicLinkConfiguration SU2 L) :
    iteratedAverageFrom s bg ell (j + k) U
      = iteratedAverageFrom (s * ell ^ j) (fun l => bg (j + l)) ell k
          (iteratedAverageFrom s bg ell j U) := by
  induction k with
  | zero =>
      rw [Nat.add_zero, iteratedAverageFrom_zero]
  | succ k ih =>
      rw [show j + (k + 1) = (j + k) + 1 by omega, iteratedAverageFrom_succ, ih,
        iteratedAverageFrom_succ, pow_add, Nat.mul_assoc]

/-- **M1.3a at base stride 1**: the (90)/(91) tower satisfies the (88) recursion — the
`(j + k)`-th order average splits as the `k`-th order operation (at base stride `ell^j`,
backgrounds `bg (j + ·)`) of the `j`-th order output. -/
theorem iteratedAverage_add (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell j k : ℕ)
    (U : PeriodicLinkConfiguration SU2 L) :
    iteratedAverage bg ell (j + k) U
      = iteratedAverageFrom (ell ^ j) (fun l => bg (j + l)) ell k
          (iteratedAverage bg ell j U) := by
  rw [iteratedAverage_eq_iteratedAverageFrom_one, iteratedAverageFrom_add,
    ← iteratedAverage_eq_iteratedAverageFrom_one, Nat.one_mul]

/-- **CMP98 (91)'s self-consistent background chain.**  At the physical point the background
for the next one-step averaging IS the previous iterate: `Ū⁰ = U`,
`Ū^{j+1} = R(Ū^j)(Ū^j)` (the level-`j` output occupies BOTH the `V0` and the `V1` slot —
CMP98 (91)'s `V0 = Ū^j` applied to the `j`-th order operation's own output). -/
noncomputable def selfConsistentTower (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L) :
    ℕ → PeriodicLinkConfiguration SU2 L
  | 0 => U
  | (j + 1) => modifiedAverageS (ell ^ j) (selfConsistentTower ell U j) ell
      (selfConsistentTower ell U j)

theorem selfConsistentTower_zero (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L) :
    selfConsistentTower ell U 0 = U := rfl

theorem selfConsistentTower_succ (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L) (j : ℕ) :
    selfConsistentTower ell U (j + 1)
      = modifiedAverageS (ell ^ j) (selfConsistentTower ell U j) ell
          (selfConsistentTower ell U j) := rfl

/-- **The self-consistent chain IS the prescribed-background iteration at its own output
backgrounds** — the concrete realization of CMP98 (91)'s background prescription
`V0 = Ū^j`: `iteratedAverage bg ell k U` with `bg = selfConsistentTower ell U` reproduces
`selfConsistentTower ell U k`.  Induction on `k`; both slots rewrite by the IH. -/
theorem selfConsistentTower_eq_iteratedAverage (ell : ℕ)
    (U : PeriodicLinkConfiguration SU2 L) (k : ℕ) :
    selfConsistentTower ell U k = iteratedAverage (selfConsistentTower ell U) ell k U := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [selfConsistentTower_succ, iteratedAverage_succ, ih]

/-! ## §4 — M1.3b: DEFERRED OBLIGATION (explicit, not faked)

The fundamental equality CMP98 (92) has two halves.  M1.3a (§3) is proved: the iterated
operator satisfies the (88) recursion.  **M1.3b — the identification with an INDEPENDENTLY
formalized (88) — is deferred**, because the second operand does not exist yet:

* No `globalAverage`/`U^k` object formalizing CMP98 (88) exists anywhere in the formal
  tree (grep, 2026-09-17).  (88) defines the `k`-th order average through the gauge
  transformations (77) (the tree-gauge fixing `G_k`) and (87); those are NOT formalized.
  What exists is only the RAW background blocking tower `UbarTowerCov.UbarTower`
  (CMP98 (43)/(15), used inside `ubarSU2`) and the (77) PATH-FACTORIZATION identity
  (`BackgroundAveraging.lean`) — neither is the (88) averaged configuration.
* Per the tranche instruction, M1.3b is recorded here as an exact Lean-shaped statement to
  be discharged when the (77)/(87) gauge transformations land; it is NOT proved, and no
  placeholder/`sorryAx` stands in for it.

Deferred statement (over an independent formalization
`globalAverage : (k : ℕ) → (ell : ℕ) → PeriodicLinkConfiguration SU2 L →
PeriodicLinkConfiguration SU2 L` of CMP98 (88)):

    /-- **CMP98 (92).** The iterated one-step averages reproduce the global `k`-th order
    average, with CMP98 (91)'s self-consistent backgrounds. -/
    theorem iteratedAverage_eq_globalAverage (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L)
        (k : ℕ) :
        iteratedAverage (selfConsistentTower ell U) ell k U = globalAverage k ell U

Proof route (CMP98's own): induction on `k`; the base `k = 1` is `iteratedAverage_one` +
`modifiedAverageS_one_eq` (proved in §2/§1); the step uses gauge covariance (93) and the
`k = 2` analysis (94)–(96) — the site-level template `Qcomposite_gaugeTransform` is
already proved and is the pattern to transport.  This is flagged as the heaviest M1
dependency in the spec; nothing about M1.1/M1.2/M1.3a depends on it. -/

/-! ## §5 — Import fingerprints and axiom audit

Same discipline as the spec's own §4: pin the resolved oleans of the paid deps and of the
reused spec skeleton, and audit every proved M1 theorem's axiom set to be exactly the
standard `{propext, Classical.choice, Quot.sound}`. -/

run_cmd do
  let ownDeps := "/home/sebastian/projects/project-adaly/compute/m1_si1_multiscale/deps"
  let specDep := "/home/sebastian/projects/project-adaly/compute/m1_si1_multiscale/m1gcheck/specdep"
  for mod in [`SI1Proof, `T1MainSegment, `ModifiedAverageDeriv] do
    let path ← Lean.findOLean mod
    let expected := s!"{ownDeps}/{mod}.olean"
    unless path.toString == expected do
      Lean.logInfo m!"GUARD_NEUTRALISED M1_IMPORT_MISMATCH {mod}: resolved {path}, expected {expected}"
    Lean.logInfo m!"M1_RESOLVED {mod}: {path}"
  let mt ← Lean.findOLean `MultiscaleTarget
  unless mt.toString == s!"{specDep}/MultiscaleTarget.olean" do
    Lean.logInfo m!"GUARD_NEUTRALISED M1_IMPORT_MISMATCH MultiscaleTarget: resolved {mt}, expected {specDep}/MultiscaleTarget.olean"
  Lean.logInfo m!"M1_RESOLVED MultiscaleTarget: {mt}"
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  let thms : List Lean.Name :=
    [`AdalySI1.Multiscale.M1.rZeroPathS_one_eq,
     `AdalySI1.Multiscale.M1.endpointAvgS_one_eq,
     `AdalySI1.Multiscale.M1.cPlusS_one,
     `AdalySI1.Multiscale.M1.modifiedAverageS_one_eq,
     `AdalySI1.Multiscale.M1.iteratedAverage_one,
     `AdalySI1.Multiscale.M1.maskedModifiedAverageS_one_eq,
     `AdalySI1.Multiscale.M1.maskedIteratedAverage_eq_iteratedAverage_of_forall,
     `AdalySI1.Multiscale.M1.iteratedAverage_eq_iteratedAverageFrom_one,
     `AdalySI1.Multiscale.M1.iteratedAverageFrom_add,
     `AdalySI1.Multiscale.M1.iteratedAverage_add,
     `AdalySI1.Multiscale.M1.selfConsistentTower_eq_iteratedAverage]
  for thm in thms do
    unless (← Lean.getEnv).contains thm do
      throwError "M1 missing declaration: {thm}"
    let axioms ← Lean.collectAxioms thm
    Lean.logInfo m!"M1_AXIOMS {thm}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {thm}: {ax}"
  Lean.logInfo "M1_IMPORT_FINGERPRINTS_PASS"

#print axioms modifiedAverageS_one_eq
#print axioms iteratedAverage_one
#print axioms iteratedAverageFrom_add
#print axioms iteratedAverage_add
#print axioms selfConsistentTower_eq_iteratedAverage
#print axioms maskedIteratedAverage_eq_iteratedAverage_of_forall

end AdalySI1.Multiscale.M1
