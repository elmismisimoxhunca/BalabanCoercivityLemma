/-
MultiscaleTarget.lean — SKELETON for the multiscale/iterated-averaging SI1 lift
(spec tranche `m1-si1-multiscale`, owner directory `compute/m1_si1_multiscale/spec/`).

SCOPE.  This file is a SPEC: it (a) re-anchors the certified boxed one-step SI1 certificate
read-only, (b) fixes the genuine composite/masked DOMAIN OBJECTS the lift needs (compiled,
axiom-audited), and (c) states the milestone propositions M1/M2/M3 as clearly labeled COMMENT
skeletons.  No `sorry`, no `sorryAx`, no placeholder proofs: every target that is not proved
here is a comment, per the tranche instruction.  See `SPEC.md` for the full narrative,
formulas, and acceptance criteria.

CERTIFIED BASEPOINT (paid, read-only — never reproved here):
  `AdalySI1.Boxed.hasDerivAt_su2Log_modifiedAverage_physical_q124`
  : for arbitrary `A` (skew-Hermitian, traceless bond field), arbitrary (nonflat) background
    `V0`, block `ell`, coarse bond `c ∈ CoarseLattice L ell`, `0 < ell`, `ell ∣ L μ + 1`,
    and the principal-log guard `loopVar 1 ell V0 c x ≠ su2NegOne` on `stepBlockOf c.1 1 ell`:
      HasDerivAt (fun t => su2Log (modifiedAverage V0 ell (fun e => su2Exp ((h*t) • A e)) c))
        (Lh ell h • (q124Principal 1 ell V0 (fineDirToUnitBond A hah htr) c' : SuTwo : M2)) 0.

SOURCES.  CMP98 pp.34-35 (89)-(92) (iterated averaging, composition law), (109)-(112)
(endpoint factor (110) and its linearization), via the coordinator extract
`compute/m1_si1_multiscale/corpus_extract/CMP98_90_91_110.md`; the Tanimoto
successive-averaging clarification `compute/expert_feedback/TANIMOTO_2026-09-08.md`
(decreasing regions `Ω_j`, exterior left at finer scale).  The SITE-LEVEL composite
`AdalyFormal.Balaban.QjComposite.Qcomposite` (CMP99b (3.19) first line) with its proven
`Qcomposite_zero/succ/one` is the formal pattern M1/M2 mirror at the bond level.
-/
import SI1Proof
import T1MainSegment
import ModifiedAverageDeriv
import AdalyFormal.Balaban.QjComposite
import Lean.Util.CollectAxioms

set_option autoImplicit false

open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
attribute [local instance] Classical.propDecidable

namespace AdalySI1.Multiscale

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2NegOne)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS loopVar)
open AdalySI1Noloop.OuterLogFullDeriv (Lh)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.DeltaKR85 (q124Principal)
open AdalySI1.ModifiedAverageDeriv (modifiedAverage)

variable {L : PeriodicLatticeExtent}

/-! ## §0 — The certified one-step basepoint, re-exported read-only -/

/-- **THE PAID ONE-STEP CERTIFICATE, RE-STATED AND RE-EXPORTED.**  The proof term is exactly
`AdalySI1.Boxed.hasDerivAt_su2Log_modifiedAverage_physical_q124` — an alias, not a reproof;
the type is restated verbatim so the skeleton pins the statement the lift starts from.
Every level of the multiscale lift must reduce to this statement transported from fine scale
`1` to fine scale `ell ^ j` (M2.1 below). -/
theorem boxed_one_step_certified (L : PeriodicLatticeExtent)
    (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hcell : c.1 ∈ CoarseLattice L ell) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hnc2 : ∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell V0 c x ≠ su2NegOne)
    (h : ℝ) :
    HasDerivAt
      (fun t : ℝ => su2Log (modifiedAverage V0 ell (fun e => su2Exp ((h * t) • A e)) c))
      (Lh ell h •
        ((q124Principal 1 ell V0 (fineDirToUnitBond A hah htr)
          (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
          : SuTwo) : M2))
      0 :=
  AdalySI1.Boxed.hasDerivAt_su2Log_modifiedAverage_physical_q124
    V0 A hah htr ell c hcell hell hdvd hnc2 h

/-! ## §1 — M2 anchor: the bond-level COMPOSITE `q`

The composite one-step linearization, CMP99b (3.19) first line transported to bond fields and
to `q124Principal` factors.  `bg j` is the level-`j` background — CMP98 (91)'s `V0 = Ū^j`,
taken at the basepoint (frozen for the linearization; see SPEC.md §2.4 for the self-consistent
reading and the deferred background-slot obligation M2.d).  The `j`-th composite maps
scale-`1` bond fields to scale-`ell ^ j` bond fields; the new factor is the COARSEST one and
acts LAST, the orientation `Qcomposite_succ` forces at site level. -/

/-- **`Q'_j` at bond level**: `q124Principal (ell^(j-1)) ell (bg (j-1)) ∘ ⋯ ∘ q124Principal 1 ell (bg 0)`.
At `j = 0` the empty composite is the identity on scale-`1` bond fields.  Definitional
recursion, mirroring `AdalyFormal.Balaban.QjComposite.Qcomposite` exactly. -/
noncomputable def qCompositeBond
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) :
    (j : ℕ) → (CoarseBond L 1 → SuTwo) →ₗ[ℝ] (CoarseBond L (ell ^ j) → SuTwo)
  | 0 => LinearMap.id
  | (j + 1) => (q124Principal (ell ^ j) ell (bg j)).comp (qCompositeBond bg ell j)

/-- **`Q'_0 = id`** — the empty product of one-step linearizations. -/
theorem qCompositeBond_zero
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) :
    qCompositeBond bg ell 0 = LinearMap.id := rfl

/-- **THE COMPOSITION LAW (M2 anchor)**: the level-`j+1` composite IS the new coarsest
one-step `q124Principal` factor composed outside the level-`j` composite.  Definitional —
the same `rfl` status as `Qcomposite_succ`. -/
theorem qCompositeBond_succ
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell j : ℕ) :
    qCompositeBond bg ell (j + 1)
      = (q124Principal (ell ^ j) ell (bg j)).comp (qCompositeBond bg ell j) := rfl

/-! ## §2 — M3 anchor: region masks, supports, masked operators -/

/-- **Tanimoto's decreasing region tower.**  At step `j` only the fields in `region j` are
averaged; the complement is left at the finer scale.  `monotone` is the `Ω_{j+1} ⊆ Ω_j`
hypothesis of the large/small-field split. -/
structure RegionTower (L : PeriodicLatticeExtent) where
  region : ℕ → Finset (PeriodicLatticeSite L)
  monotone : ∀ j : ℕ, region (j + 1) ⊆ region j

/-- **Support of one masked averaging step**, CMP98 (89)/(92) locality `B(c₋) ∪ B(c₊)` at
fine stride `s` with block factor `ell`: the strided blocks based at the near endpoint `c.1`
and at the far endpoint of the OUTPUT bond (`cPlusS s ell c`, advancing `s * ell` unit
steps — the general-stride far endpoint `ModifiedAverageDeriv` §7 defers).  A level-`j+1`
coarse bond may be averaged only when its whole support lies in `region j` (M3.1). -/
def bondSupport (s ell : ℕ) (c : PeriodicLatticeEdge L) : Finset (PeriodicLatticeSite L) :=
  stepBlockOf c.1 s ell ∪ stepBlockOf (cPlusS s ell c) s ell

/-- **Zero Dirichlet extension** of a scale-`s` bond field off the mask `S`: the variation
class for the masked step (fields outside the averaged region are held fixed, i.e. their
variation vanishes).  Linear by construction. -/
noncomputable def maskExtend (s : ℕ) (S : CoarseBond L s → Prop) :
    (CoarseBond L s → SuTwo) →ₗ[ℝ] (CoarseBond L s → SuTwo) where
  toFun A c := if S c then A c else 0
  map_add' A B := by funext c; by_cases h : S c <;> simp [h, Pi.add_apply]
  map_smul' a A := by funext c; by_cases h : S c <;> simp [h, Pi.smul_apply]

/-- **The masked composite `q`**: fine Dirichlet fields (zero off `S`) pushed through the
whole tower of one-step linearizations.  This is the linear map M2/M3 must identify with the
derivative of the masked iterated average. -/
noncomputable def maskedQCompositeBond
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) (S : CoarseBond L 1 → Prop)
    (j : ℕ) : (CoarseBond L 1 → SuTwo) →ₗ[ℝ] (CoarseBond L (ell ^ j) → SuTwo) :=
  (qCompositeBond bg ell j).comp (maskExtend 1 S)

/-- **The one-step masked (mixed-scale) average at stride `1`** — the M3 nonlinear operator
whose iteration is the multiscale average: CMP98 (63) (= `modifiedAverage`) values on the
coarse base bonds selected by `S`, the UNTOUCHED fine field elsewhere ("the rest is left in
a finer scale", Tanimoto). -/
noncomputable def maskedModifiedAverage
    (V0 V1 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (S : PeriodicLatticeEdge L → Prop) (c : PeriodicLatticeEdge L) : SU2 :=
  if S c then modifiedAverage V0 ell V1 c else V1 c

/-! ## §3 — Milestone proposition skeletons (COMMENTS ONLY — no `sorry` in accepted code)

The statements below are the accepted targets in Lean-shaped comment form.  Proving them is
NOT this tranche; each is labeled with its milestone and its dependencies.  Naming: `S_j` is
`region j` of a `RegionTower`; `modifiedAverageS s V0 ell V1` is the STRIDE-`s` one-step
modified average (M1.1 delivers it); `iteratedAverage` is the (90)/(91) recursion (M1.2).

### M1 — iteration of averages / composition law

M1.1 (stride lift, DEFINITION).  `modifiedAverageS s V0 ell V1 c : SU2` := `modifiedAverage`
with `cPlus ell` replaced by `cPlusS s ell`, `ubarSU2 1 ell` by `ubarSU2 s ell`,
`rZeroPath`/`GammaPath` by the stride-`s` tree path (`coarseGammaPath s`, already in
`QjComposite`), and `endpointAvg` by its strided analogue on `stepBlockOf y s ell`.
At `s = 1` it must reduce to `modifiedAverage` LITERALLY (`stepBlockOf_one`,
`coarsePathHolonomy_one_eq_staircaseTransport` are the proven bridges).  Status: definition +
`modifiedAverageS_one_eq : modifiedAverageS 1 = modifiedAverage` (theorem).

M1.2 (iterated average, DEFINITION).  `iteratedAverage bg ell : (j : ℕ) → Config → Config`
by `iteratedAverage bg ell 0 U = U`,
`iteratedAverage bg ell (j+1) U = modifiedAverageS (ell^j) (bg j) ell (iteratedAverage bg ell j U)`,
where at the physical point `bg j = iteratedAverage bg ell j Ubase` (CMP98 (91): `V0 = Ū^j`;
self-consistent value, frozen only in the linearization — SPEC.md §2.4).

M1.3 (composition law + fundamental equality, CMP98 (92)).  THEOREM skeleton:
  `theorem iteratedAverage_eq_globalAverage … :
      iteratedAverage bg ell k U = globalAverage k ell U`
where `globalAverage` is CMP98 (88)'s k-th order average (needs the (77)/(87) gauge
transformations — the heaviest M1 dependency; if (88) is not yet formalized, M1.3 splits
into M1.3a: `iteratedAverage` satisfies the (88) recursion relation, and M1.3b: the
identification when `globalAverage` lands).  Proof route: CMP98's own induction, using the
gauge covariance (93) — the site-level analogue is the PROVEN `Qcomposite_gaugeTransform`.

### M2 — composite derivative = product of one-step linearizations

M2.1 (per-level identification, stride lift of the boxed certificate).  THEOREM skeleton:
  `theorem hasDerivAt_su2Log_modifiedAverageS_physical_q124
      (bg : ℕ → PeriodicLinkConfiguration SU2 L) (j : ℕ) …
      (A : CoarseBond L (ell^j) → SuTwo)  (c : CoarseBond L (ell^(j+1))) …
      (hnc : ∀ x ∈ stepBlockOf c.1 (ell^j) ell, loopVar (ell^j) ell (bg j) c x ≠ su2NegOne)
      (h : ℝ) :
    HasDerivAt
      (fun t : ℝ => su2Log (modifiedAverageS (ell^j) (bg j) ell
          (coarseConfigExp (ell^j) (fun b => su2Exp ((h * t) • A b))) c))
      (Lh ell h • ((q124Principal (ell^j) ell (bg j) A c : SuTwo) : M2)) 0`
i.e. the boxed theorem with `(1, ell)` replaced by `(ell^j, ell)`.  All three fitting
hypotheses and the principal-log guard transport at stride `ell^j`; arbitrary `A`, nonflat
`bg j`, identity loops, `h = 0` retained.  NO smallness hypotheses added ((109)'s `ε₀, ε₁`
belong to the estimates tranche, not the identification).

M2.2 (chain-rule assembly).  THEOREM skeleton: with `Φ_0(t) = fun e => su2Exp (t • A e)` and
`Φ_{l+1}(t) = modifiedAverageS (ell^l) (bg l) ell (Φ_l(t))` (frozen backgrounds `bg l`),
  `theorem hasDerivAt_su2Log_iteratedAverage_qCompositeBond … :
    HasDerivAt (fun t : ℝ => su2Log (Φ j t c))
      (h • ((qCompositeBond bg ell j A c : SuTwo) : M2)) 0`
proved by induction on `j` via `HasDerivAt.comp`, M2.1 at each level, and
`qCompositeBond_succ`.  The per-level `Lh` scalars are absorbed into the `q124Principal`
factors by the paid `dcomputed_eq_ell_smul_q124Principal` normalization; the induction fixes
the composite scalar bookkeeping (obligation: record the exact scalar at each step, matching
the boxed level-1 statement at `j = 1`).

M2.3 (identification with the site-level composite).  THEOREM skeleton: on the T1/main
channel, `qCompositeBond bg ell j` composed with the site restriction agrees with
`AdalyFormal.Balaban.QjComposite.Qcomposite bg ell j` — the bond-level composite q IS the
bond lift of the proven site composite (`q124Principal_T1_eq_unitToCoarseCov` at each level,
then induction).  This pins "identified with composite q" to a concrete existing object.

M2.d (DEFERRED, explicitly out of this tranche's proof scope but IN the spec).  CMP98 (91)
takes `V0 = Ū^j` self-consistently, so the background slot of `modifiedAverageS` also moves
with `t`.  The full tangent of the self-consistent map is
  `DΦ_{j+1}(0)[A] = q124Principal (ell^j) ell (bg j) (DΦ_j(0)[A])
                    + (∂_{V0} modifiedAverageS)(bg j, Ū^j(0)) [DΦ_j(0)[A]]`.
The boxed certificate covers ONLY the field slot.  The background-slot derivative
`∂_{V0}` is a NEW identification (same channel technology, not yet paid).  M2 targets the
frozen-background composite (the CMP99b (3.19)/`Qcomposite` reading, backgrounds prescribed);
M2.d records the exact extra statement needed for the self-consistent reading.  Decision
logged in SPEC.md §2.4; not silently dropped.

### M3 — mask/Dirichlet compatibility

M3.1 (mask–support compatibility).  THEOREM skeleton: if `c : CoarseBond L (ell^(j+1))` with
`bondSupport (ell^j) ell c ⊆ S_j` (region tower), then `iteratedAverage bg ell (j+1) U` at `c`
depends only on the restriction of `U` to bonds inside `S_j` (CMP98 (89)/(92) locality,
transported; site-level analogue `Qcomposite_local` is proven).

M3.2 (Dirichlet correctness).  THEOREM skeleton: for `A` with `A c = 0` off
`S : CoarseBond L 1 → Prop` (equivalently `A` in the range of `maskExtend 1 S`), the
masked iterated average of `fun e => su2Exp (t • A e)` agrees on the mask with the unmasked
one, and its derivative at `0` equals `maskedQCompositeBond bg ell S j A c` — the masked
composite derivative IS the masked composite `q`.  Exterior bonds retain the finer-scale
background values for all `t` (the exterior is `t`-independent: Dirichlet).

M3.3 (boundary convention, flagged).  Coarse bonds whose `bondSupport` crosses `∂S_j` are
NOT averaged (they remain at the finer scale) — the conservative choice.  CMP102 p.278's
replacement of missing scale-`j` bond values by averaged finer values `bar V_b` at
boundary-crossing plaquettes is recorded in the Tanimoto file as a convention to adjudicate;
it is NOT adopted here silently.  M3.3 is the coherence statement between the chosen
convention and any future adjudicated one. -/

/-! ## §4 — Import fingerprints and axiom audit (the spec's own certificate hygiene) -/

run_cmd do
  let ownDeps := "/home/sebastian/projects/project-adaly/compute/m1_si1_multiscale/deps"
  for mod in [`SI1Proof, `T1MainSegment, `ModifiedAverageDeriv] do
    let path ← Lean.findOLean mod
    let expected := s!"{ownDeps}/{mod}.olean"
    unless path.toString == expected do
      Lean.logInfo m!"GUARD_NEUTRALISED MULTISCALE_IMPORT_MISMATCH {mod}: resolved {path}, expected {expected}"
    Lean.logInfo m!"MULTISCALE_RESOLVED {mod}: {path}"
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  let cert := `AdalySI1.Boxed.hasDerivAt_su2Log_modifiedAverage_physical_q124
  unless (← Lean.getEnv).contains cert do
    throwError "Missing boxed SI1 certificate: {cert}"
  let axioms ← Lean.collectAxioms cert
  Lean.logInfo m!"MULTISCALE_CERT_AXIOMS {cert}: {axioms}"
  for ax in axioms do
    unless allowed.contains ax do
      throwError "Nonstandard axiom in boxed SI1 certificate {cert}: {ax}"
  Lean.logInfo "MULTISCALE_IMPORT_FINGERPRINTS_PASS"

#print axioms qCompositeBond
#print axioms maskedModifiedAverage
#print axioms boxed_one_step_certified

end AdalySI1.Multiscale
