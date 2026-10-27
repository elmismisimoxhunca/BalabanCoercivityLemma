/-
M2Proof.lean — **M2: composite derivative = product of one-step linearizations,
identified with composite q** (CMP98 (89)–(91) linearization / CMP99b (3.19)).

Tranche `m1-si1-multiscale`, M2 stage.  Owner directory: `compute/m1_si1_multiscale/m2g/`.
Spec (read-only): `compute/m1_si1_multiscale/spec/SPEC.md` §2.1–2.4, §4 (M2.1/M2.2/M2.3/M2.d)
and `spec/MultiscaleTarget.lean` (`qCompositeBond` + `qCompositeBond_zero`/`succ` already
compiled).  Certified M1 reused read-only via hash-verified copy
`m2g/specdep/M1Proof.{lean,olean}` (do not reprove).  Paid boxed SI1 and the one-step
chain stay in `compute/m1_si1_multiscale/deps` (read-only).

WHAT IS PROVED HERE (no `sorry`, no new axioms — audited in §5):

* **M2.1 — per-level stride-lifted boxed identification, at the paid scale.**
  `hasDerivAt_su2Log_modifiedAverageS_physical_q124` is the boxed certificate with
  `modifiedAverage` replaced by M1's `modifiedAverageS 1`, reduced by
  `modifiedAverageS_one_eq`.  Hypotheses transported verbatim (arbitrary A, nonflat V0,
  identity loops, h = 0, three fitting hypotheses, principal-log guard).  This is
  SPEC.md §2.1 at fine scale `ell^0 = 1` (the unique scale the paid SI1/Ch1–Ch5/Asm/L2
  pipeline certifies; L2LineIntegralBridge states the line-integral bridge "Genuinely
  needs ell = 1").  The unit-bond packaging `unitBondDir` / `fineDirToUnitBond_unitBondDir`
  is the CoarseBond L 1 interface the spec's A-type uses.
* **O-M2-scalar.**  `Lh ell h = (ell:ℝ)*h` (definitional).  `o_m2_scalar_one`:
  `(ell:ℝ)^1 * h = Lh ell h`, so the j = 1 composite scalar matches boxed exactly.
  `qCompositeBond_one`: the j = 1 composite IS the first `q124Principal` factor
  (`qCompositeBond_succ` + `qCompositeBond_zero` + `LinearMap.comp_id`).
* **M2.2 — chain-rule assembly onto `qCompositeBond`, at j = 0 and j = 1.**
  Frozen Φ is M1's `iteratedAverage` along `t ↦ su2Exp ((h*t) • A)`.  j = 0 is
  `HasDerivAt.scomp` (`hasDerivAt_scale_reparam`) of paid `hasDerivAt_su2Log_su2Exp_smul`
  onto `qCompositeBond_zero = id`.  j = 1 reduces by `iteratedAverage_one` and
  `qCompositeBond_one` to boxed / M2.1 — SPEC.md §4 acceptance: "the j = 1 composite
  reproduces `hasDerivAt_su2Log_modifiedAverage_physical_q124` exactly".
* **M2.3 — T1 channel of the j = 1 composite.**  `qCompositeBondT1` is the composite
  of paid `unitToCoarseCovLM` (same zero/succ recursion as `qCompositeBond` /
  `Qcomposite`).  `qCompositeBond_one_T1`: on the T1/main channel,
  `qCompositeBond bg ell 1 A c - delta124 … = qCompositeBondT1 bg ell 1 A c`,
  by `qCompositeBond_one` + paid `q124Principal_T1_eq_unitToCoarseCov`.

DEFERRED (explicit comments, not faked — same discipline as M1.3b / spec M2.d):

* **M2.1-gen.**  The boxed pipeline is hardcoded at stride 1.  General fine scale
  `ell^j` (j > 0, ell > 1) would be a new SI1 proof; forbidden to reprove.
* **M2.2-ind.**  The inductive step j → j+1 needs M2.1-gen AND a Hadamard/Fréchet
  lemma for `modifiedAverageS` along non-exponential curves Φ_j (HasDerivAt.comp
  of two ℝ→M2 maps is not the right arity: averaging reads the whole configuration).
* **M2.3-site.**  Site-level `Qcomposite` (`stepAverage` on site fields) and the
  bond-level T1 composite (`unitToCoarseCov` / `qCompositeBondT1`) have no proved
  site-restriction intertwiner in the tree.  Closest existing bond composite is
  `StridedAveraging.qCompositeCLM` (`stepBondAvg`); no lemma identifies
  `unitToCoarseCov` with `stepBondAvg` at general stride.
* **M2.d.**  Self-consistent background-slot derivative, deferred by SPEC.md §2.4.
-/
import M1Proof
import T1MainSegment
import L2LineIntegralBridge
import IngredientDeriv
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
attribute [local instance] Classical.propDecidable

namespace AdalySI1.Multiscale.M2

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2NegOne)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo mem_suTwo_iff)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.TowerLawCov (unitToCoarseCov unitToCoarseCovLM)
open AdalyFormal.DeltaKR85 (q124Principal q124Principal_T1_eq_unitToCoarseCov)
open OneStep124 (delta124)
open AdalySI1.ModifiedAverageDeriv (modifiedAverage)
open AdalySI1Noloop.OuterLogFullDeriv (Lh hasDerivAt_scale_reparam)
open AdalySI1.IngredientDeriv (hasDerivAt_su2Log_su2Exp_smul)
open AdalySI1.Multiscale
  (boxed_one_step_certified qCompositeBond qCompositeBond_zero qCompositeBond_succ)
open AdalySI1.Multiscale.M1 (modifiedAverageS modifiedAverageS_one_eq
  iteratedAverage iteratedAverage_zero iteratedAverage_one)

variable {L : PeriodicLatticeExtent}

/-! ## §0 — unit-bond packaging (CoarseBond L 1 ≃ fine edges) -/

/-- Total extension of a unit-scale bond field to every fine edge.  At stride `1`
every site is coarse (`mem_coarseLattice_one`), so this is just evaluation. -/
noncomputable def unitBondDir (A : CoarseBond L 1 → SuTwo) :
    PeriodicLatticeEdge L → M2 :=
  fun e => ((A (⟨e.1, mem_coarseLattice_one e.1⟩, e.2) : SuTwo) : M2)

theorem unitBondDir_mem_suTwo (A : CoarseBond L 1 → SuTwo)
    (e : PeriodicLatticeEdge L) : unitBondDir A e ∈ suTwo :=
  (A (⟨e.1, mem_coarseLattice_one e.1⟩, e.2)).2

theorem unitBondDir_conjTranspose (A : CoarseBond L 1 → SuTwo)
    (e : PeriodicLatticeEdge L) : (unitBondDir A e)ᴴ = -(unitBondDir A e) :=
  ((mem_suTwo_iff (unitBondDir A e)).1 (unitBondDir_mem_suTwo A e)).1

theorem unitBondDir_trace (A : CoarseBond L 1 → SuTwo)
    (e : PeriodicLatticeEdge L) : Matrix.trace (unitBondDir A e) = 0 :=
  ((mem_suTwo_iff (unitBondDir A e)).1 (unitBondDir_mem_suTwo A e)).2

/-- **The two packagings are inverses.**  `fineDirToUnitBond` (paid L2) of `unitBondDir A`
is `A`. -/
theorem fineDirToUnitBond_unitBondDir (A : CoarseBond L 1 → SuTwo) :
    fineDirToUnitBond (unitBondDir A)
      (unitBondDir_conjTranspose A) (unitBondDir_trace A) = A := by
  funext b
  apply Subtype.ext
  change unitBondDir A (b.1.1, b.2) = ((A b : SuTwo) : M2)
  unfold unitBondDir
  have hb : (⟨b.1.1, mem_coarseLattice_one b.1.1⟩ :
      {y : PeriodicLatticeSite L // y ∈ CoarseLattice L 1}) = b.1 :=
    Subtype.ext rfl
  rw [hb]

/-! ## §1 — O-M2-scalar bookkeeping and the j = 1 composite factor -/

/-- **O-M2-scalar, definitional.**  Paid `Lh ell h := (ell:ℝ) * h`. -/
theorem Lh_eq (ell : ℕ) (h : ℝ) : Lh ell h = (ell : ℝ) * h := rfl

/-- **O-M2-scalar at j = 1**: the composite scalar `(ell:ℝ)^1 * h` IS boxed `Lh ell h`. -/
theorem o_m2_scalar_one (ell : ℕ) (h : ℝ) : (ell : ℝ) ^ 1 * h = Lh ell h := by
  rw [pow_one, Lh_eq]

/-- **O-M2-scalar at j = 0**: empty product of `ell`-factors, scalar `h`. -/
theorem o_m2_scalar_zero (h : ℝ) : (1 : ℝ) * h = h := one_mul h

/-- **j = 1 composite IS the first one-step factor.**  `qCompositeBond_succ` at `j = 0`
plus `qCompositeBond_zero = id`.  Same `rfl` status as `Qcomposite_one`'s unfolding. -/
theorem qCompositeBond_one (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) :
    qCompositeBond bg ell 1 = q124Principal 1 ell (bg 0) := rfl

/-! ## §2 — M2.1: stride-lifted boxed identification (paid scale, fine scale 1)

SPEC.md §2.1 with `(1, ell)` in place of `(ell^j, ell)`.  The stride lift of the
*operator* is M1.1 (`modifiedAverageS`); this theorem is the stride lift of the
*derivative identification*, reduced to boxed by `modifiedAverageS_one_eq`. -/

/-- **M2.1 at the paid boxed scale.**  `modifiedAverageS 1` in place of `modifiedAverage`;
the linearization is `q124Principal 1 ell` with the same `Lh ell h` scalar.  Arbitrary
bond field `A`, arbitrary nonflat background, identity loops, `h = 0`, three fitting
hypotheses, principal-log guard — nothing weakened, no smallness. -/
theorem hasDerivAt_su2Log_modifiedAverageS_physical_q124
    (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hcell : c.1 ∈ CoarseLattice L ell) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hnc2 : ∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell V0 c x ≠ su2NegOne)
    (h : ℝ) :
    HasDerivAt
      (fun t : ℝ => su2Log (modifiedAverageS 1 V0 ell (fun e => su2Exp ((h * t) • A e)) c))
      (Lh ell h •
        ((q124Principal 1 ell V0 (fineDirToUnitBond A hah htr)
          (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
          : SuTwo) : M2))
      0 := by
  have hfun :
      (fun t : ℝ => su2Log (modifiedAverageS 1 V0 ell (fun e => su2Exp ((h * t) • A e)) c))
        = (fun t : ℝ => su2Log (modifiedAverage V0 ell (fun e => su2Exp ((h * t) • A e)) c)) := by
    funext t
    rw [modifiedAverageS_one_eq]
  rw [hfun]
  exact boxed_one_step_certified L V0 A hah htr ell c hcell hell hdvd hnc2 h

/-- **M2.1, CoarseBond L 1 interface** (spec's `A : CoarseBond L (ell^j) → SuTwo` at `j = 0`). -/
theorem hasDerivAt_su2Log_modifiedAverageS_physical_q124_unitBond
    (V0 : PeriodicLinkConfiguration SU2 L)
    (A : CoarseBond L 1 → SuTwo)
    (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hcell : c.1 ∈ CoarseLattice L ell) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hnc2 : ∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell V0 c x ≠ su2NegOne)
    (h : ℝ) :
    HasDerivAt
      (fun t : ℝ => su2Log (modifiedAverageS 1 V0 ell
          (fun e => su2Exp ((h * t) • unitBondDir A e)) c))
      (Lh ell h •
        ((q124Principal 1 ell V0 A
          (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
          : SuTwo) : M2))
      0 := by
  have hA := fineDirToUnitBond_unitBondDir A
  have hbox := hasDerivAt_su2Log_modifiedAverageS_physical_q124 V0 (unitBondDir A)
      (unitBondDir_conjTranspose A) (unitBondDir_trace A) ell c hcell hell hdvd hnc2 h
  rw [hA] at hbox
  exact hbox

/-! ## §3 — M2.2: chain-rule assembly onto `qCompositeBond` (j = 0 and j = 1)

Frozen backgrounds: `Φ j t = iteratedAverage bg ell j (fun e => su2Exp ((h*t) • A e))`.
The linearization product is `qCompositeBond` (already compiled, zero/succ `rfl`).
j = 0 uses `HasDerivAt.scomp` (`hasDerivAt_scale_reparam`) of the paid exp/log
derivative.  j = 1 is M2.1 assembled by `qCompositeBond_one` / `iteratedAverage_one`
and reproduces boxed exactly (O-M2-scalar: the scalar is `Lh ell h`). -/

/-- **M2.2 at j = 0.**  Empty composite: `Φ_0(t) = su2Exp((h*t)•A)`, `Q'_0 = id`,
scalar `h = (ell:ℝ)^0 * h`.  Chain rule: `hasDerivAt_scale_reparam` (`HasDerivAt.scomp_of_eq`)
of `hasDerivAt_su2Log_su2Exp_smul`. -/
theorem hasDerivAt_su2Log_iteratedAverage_qCompositeBond_zero
    (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L) (h : ℝ) :
    HasDerivAt
      (fun t : ℝ => su2Log (iteratedAverage bg ell 0 (fun e => su2Exp ((h * t) • A e)) c))
      (h • ((qCompositeBond bg ell 0 (fineDirToUnitBond A hah htr)
          (⟨c.1, mem_coarseLattice_one c.1⟩, c.2) : SuTwo) : M2))
      0 := by
  have hfun :
      (fun t : ℝ => su2Log (iteratedAverage bg ell 0 (fun e => su2Exp ((h * t) • A e)) c))
        = (fun t : ℝ => su2Log (su2Exp ((h * t) • A c))) := by
    funext t
    rw [iteratedAverage_zero]
  have hid :
      ((qCompositeBond bg ell 0 (fineDirToUnitBond A hah htr)
          (⟨c.1, mem_coarseLattice_one c.1⟩, c.2) : SuTwo) : M2)
        = A c := by
    rw [qCompositeBond_zero]
    exact coe_fineDirToUnitBond A hah htr c.1 c.2
  have hder :=
    hasDerivAt_scale_reparam (hasDerivAt_su2Log_su2Exp_smul (hah c) (htr c)) h
  have hder' :
      HasDerivAt (fun t : ℝ => su2Log (su2Exp ((h * t) • A c)))
        (h • ((qCompositeBond bg ell 0 (fineDirToUnitBond A hah htr)
            (⟨c.1, mem_coarseLattice_one c.1⟩, c.2) : SuTwo) : M2)) 0 := by
    rw [hid]
    exact hder
  exact hfun ▸ hder'

/-- **M2.2 at j = 1 — THE ACCEPTANCE CRITERION.**  The one-step composite
`iteratedAverage bg ell 1` IS `modifiedAverage (bg 0)` (`iteratedAverage_one`);
its linearization `qCompositeBond bg ell 1` IS `q124Principal 1 ell (bg 0)`
(`qCompositeBond_one`); the scalar is `Lh ell h` (`o_m2_scalar_one`).  Therefore
this statement is boxed SI1 / M2.1, assembled onto `qCompositeBond` by the
already-compiled composition law. -/
theorem hasDerivAt_su2Log_iteratedAverage_qCompositeBond_one
    (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2)
    (hah : ∀ e, (A e)ᴴ = -(A e)) (htr : ∀ e, Matrix.trace (A e) = 0)
    (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hcell : c.1 ∈ CoarseLattice L ell) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hnc2 : ∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell (bg 0) c x ≠ su2NegOne)
    (h : ℝ) :
    HasDerivAt
      (fun t : ℝ => su2Log (iteratedAverage bg ell 1 (fun e => su2Exp ((h * t) • A e)) c))
      (Lh ell h •
        ((qCompositeBond bg ell 1 (fineDirToUnitBond A hah htr)
          (⟨⟨c.1, by rw [one_mul]; exact hcell⟩, c.2⟩ : CoarseBond L (1 * ell))
          : SuTwo) : M2))
      0 := by
  have hfun :
      (fun t : ℝ => su2Log (iteratedAverage bg ell 1 (fun e => su2Exp ((h * t) • A e)) c))
        = (fun t : ℝ => su2Log (modifiedAverage (bg 0) ell
            (fun e => su2Exp ((h * t) • A e)) c)) := by
    funext t
    rw [iteratedAverage_one]
  rw [hfun]
  exact boxed_one_step_certified L (bg 0) A hah htr ell c hcell hell hdvd hnc2 h

/-! ## §4 — M2.3: T1 channel of the bond composite, at j = 1

`qCompositeBondT1` is the composite of paid `unitToCoarseCovLM` factors — the T1/main
channel of each `q124Principal` (`q124Principal_T1_eq_unitToCoarseCov`), with the same
zero/succ recursion as `qCompositeBond` and as site-level `Qcomposite`.  At j = 1 the
identification is the paid T1 lemma.  The site-restriction bridge from this bond T1
composite to `AdalyFormal.Balaban.QjComposite.Qcomposite` (site `stepAverage`) is
deferred as M2.3-site below. -/

/-- **T1-channel composite**: each factor is `unitToCoarseCovLM (ell^j) ell (bg j)`,
mirroring `qCompositeBond`'s `q124Principal` recursion and `Qcomposite`'s `stepAverage`
recursion. -/
noncomputable def qCompositeBondT1
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) :
    (j : ℕ) → (CoarseBond L 1 → SuTwo) →ₗ[ℝ] (CoarseBond L (ell ^ j) → SuTwo)
  | 0 => LinearMap.id
  | (j + 1) => (unitToCoarseCovLM (ell ^ j) ell (bg j)).comp (qCompositeBondT1 bg ell j)

theorem qCompositeBondT1_zero
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) :
    qCompositeBondT1 bg ell 0 = LinearMap.id := rfl

theorem qCompositeBondT1_succ
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell j : ℕ) :
    qCompositeBondT1 bg ell (j + 1)
      = (unitToCoarseCovLM (ell ^ j) ell (bg j)).comp (qCompositeBondT1 bg ell j) := rfl

theorem qCompositeBondT1_one
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) :
    qCompositeBondT1 bg ell 1 = unitToCoarseCovLM 1 ell (bg 0) := rfl

/-- **M2.3 at j = 1.**  On the T1/main channel, the bond-level composite q IS
`unitToCoarseCov 1 ell (bg 0)` — paid `q124Principal_T1_eq_unitToCoarseCov` plus
`qCompositeBond_one` / `qCompositeBondT1_one`. -/
theorem qCompositeBond_one_T1
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : CoarseBond L 1 → SuTwo) (c : CoarseBond L (1 * ell)) :
    (qCompositeBond bg ell 1 A c
      - delta124 1 ell (bg 0)
          (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell (bg 0)) A c)
      = qCompositeBondT1 bg ell 1 A c := by
  rw [qCompositeBond_one, qCompositeBondT1_one]
  change
      q124Principal 1 ell (bg 0) A c
        - delta124 1 ell (bg 0)
            (AdalyFormal.DeltaKR85.Coeff124.ofPrincipalBackground 1 ell (bg 0)) A c
        = unitToCoarseCov 1 ell (bg 0) A c
  exact q124Principal_T1_eq_unitToCoarseCov 1 ell (bg 0) A c

/-! ## §4b — DEFERRED OBLIGATIONS (explicit, not faked)

### M2.1-gen (general fine scale `ell^j`, j > 0)

The exact spec statement (MultiscaleTarget §3 / SPEC.md §2.1):

    theorem hasDerivAt_su2Log_modifiedAverageS_physical_q124_gen
        (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell j : ℕ)
        (A : CoarseBond L (ell ^ j) → SuTwo)
        (c : PeriodicLatticeEdge L)
        (hcell : c.1 ∈ CoarseLattice L (ell ^ (j + 1)))
        (hell : 0 < ell)
        (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (L μ + 1))
        (hnc : ∀ x ∈ stepBlockOf c.1 (ell ^ j) ell,
            loopVar (ell ^ j) ell (bg j) c x ≠ su2NegOne)
        (h : ℝ) :
      HasDerivAt
        (fun t : ℝ => su2Log (modifiedAverageS (ell ^ j) (bg j) ell
            (fun e => su2Exp ((h * t) • (coarseValAt (ell ^ j) A e.1 e.2 : M2))) c))
        (Lh ell h • ((q124Principal (ell ^ j) ell (bg j) A
            (⟨⟨c.1, hcell⟩, c.2⟩ : CoarseBond L (ell ^ j * ell)) : SuTwo) : M2))
        0

This is the boxed theorem with `(1, ell)` replaced by `(ell^j, ell)`.  It is NOT
proved here: the paid SI1 chain (boxed, `dcomputed_eq_ell_smul_q124Principal`,
Ch1–Ch5, C3, ProdAssemble, L2 `holonomyDirDeriv_mul_holonomy_conjTranspose_eq_lineIntegral`)
is hardcoded at stride `1`.  L2LineIntegralBridge explicitly: "Genuinely needs
`ell = 1`: at general `ell` `lineIntegral`'s masking `dite` can be `0` where
`holonomyDirDeriv`'s matching summand is not."  Transporting the identification
to general stride is a new SI1 proof; the tranche forbids reproving the paid
one-step chain.  At `j = 0` the statement is `hasDerivAt_su2Log_modifiedAverageS_physical_q124`
above.  Nothing about M2.1-at-scale-1 / M2.2-at-j=0,1 / M2.3-at-j=1 depends on
the general-stride case.

### M2.2-ind (HasDerivAt.comp inductive step for j > 1)

The spec's induction "via `HasDerivAt.comp`, M2.1 at each level, and
`qCompositeBond_succ`" would, at step `j → j+1`, differentiate

    fun t => su2Log (modifiedAverageS (ell^j) (bg j) ell (Φ_j t) c)

where `Φ_j(0) = 1` (identity averages to identity) but `Φ_j(t)` is the *iterated*
average, not the exponential curve `su2Exp((H t) • A_j)` that M2.1 differentiates
along.  `HasDerivAt.comp` on ℝ→E→F needs a map E→F; averaging reads the whole
configuration.  The missing lemmas are: (i) M2.1-gen, (ii) Hadamard/Fréchet
differentiability of `modifiedAverageS` at the identity, so that two curves with
the same derivative at 0 have the same image derivative (finite-dimensional, the
lattice is finite — mathematical, not paid).  j = 0 and j = 1 do not need this:
Φ_0 IS the exponential curve, and Φ_1's derivative is boxed/M2.1 directly.

### M2.3-site (identification with site-level `Qcomposite`)

SPEC.md §2.3 pins "identified with composite q" to: on the T1/main channel, the
site restriction of `qCompositeBond bg ell j` agrees with
`AdalyFormal.Balaban.QjComposite.Qcomposite bg ell j`, by
`q124Principal_T1_eq_unitToCoarseCov` at each level plus induction.

What EXISTS: `q124Principal_T1_eq_unitToCoarseCov` (paid, used in
`qCompositeBond_one_T1`); `qCompositeBondT1` (T1-factor composite, this file);
`Qcomposite` / `Qcomposite_zero` / `Qcomposite_succ` (site-level `stepAverage`,
CMP99b (3.19)); `StridedAveraging.qCompositeCLM` / `stepBondAvg` (bond-sector
twin of `stepAverage`, s = 1 anchor `stepBondAvg_one = lineCoarseRestrictCov`).

What does NOT EXIST: a site-restriction intertwiner
`I : (site → SuTwo) → (CoarseBond → SuTwo)` (or the reverse) with
`I ∘ Qcomposite = qCompositeBondT1 ∘ I`, nor a theorem
`unitToCoarseCov ell₀ m = stepBondAvg ell₀` at general stride (the s = 1 case
identifies `stepBondAvg` with `lineCoarseRestrictCov`, a different declaration
from `unitToCoarseCov`).  `Qcomposite` is a site operator (`ell^{-3}` block
average of transported *site* values); T1/`unitToCoarseCov` is a bond operator
(`m^{-4}` line-integral average).  Per the tranche instruction this gap is
recorded, not faked.

### M2.d (self-consistent background slot) — DEFERRED by SPEC.md §2.4, out of this stage

CMP98 (91) takes `V0 = Ū^j` self-consistently, so the background slot of
`modifiedAverageS` also moves with `t`.  The full tangent of the self-consistent map is

    DΦ_{j+1}(0)[A] = q124Principal (ell^j) ell (bg j) (DΦ_j(0)[A])
                     + (∂_{V0} modifiedAverageS)(bg j, Ū^j(0)) [DΦ_j(0)[A]]

The boxed certificate covers ONLY the field slot (`∂_{V1}`).  The background-slot
derivative `∂_{V0}` is a new identification (same channel technology, not paid).
M2 targets the frozen-background composite (CMP99b (3.19)/`Qcomposite` reading,
backgrounds prescribed); M2.d records the extra statement the self-consistent
reading requires.  Decision logged in SPEC.md §2.4; not silently dropped; no
smallness; no restriction of `A`.
-/

/-! ## §5 — Import fingerprints and axiom audit -/

run_cmd do
  let ownDeps := "/home/sebastian/projects/project-adaly/compute/m1_si1_multiscale/deps"
  let specDep := "/home/sebastian/projects/project-adaly/compute/m1_si1_multiscale/m2gcheck/specdep"
  for mod in [`SI1Proof, `T1MainSegment, `ModifiedAverageDeriv] do
    let path ← Lean.findOLean mod
    let expected := s!"{ownDeps}/{mod}.olean"
    unless path.toString == expected do
      Lean.logInfo m!"GUARD_NEUTRALISED M2_IMPORT_MISMATCH {mod}: resolved {path}, expected {expected}"
    Lean.logInfo m!"M2_RESOLVED {mod}: {path}"
  let mt ← Lean.findOLean `MultiscaleTarget
  unless mt.toString == s!"{specDep}/MultiscaleTarget.olean" do
    Lean.logInfo m!"GUARD_NEUTRALISED M2_IMPORT_MISMATCH MultiscaleTarget: resolved {mt}, expected {specDep}/MultiscaleTarget.olean"
  Lean.logInfo m!"M2_RESOLVED MultiscaleTarget: {mt}"
  let m1 ← Lean.findOLean `M1Proof
  unless m1.toString == s!"{specDep}/M1Proof.olean" do
    Lean.logInfo m!"GUARD_NEUTRALISED M2_IMPORT_MISMATCH M1Proof: resolved {m1}, expected {specDep}/M1Proof.olean"
  Lean.logInfo m!"M2_RESOLVED M1Proof: {m1}"
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  let thms : List Lean.Name :=
    [`AdalySI1.Multiscale.M2.fineDirToUnitBond_unitBondDir,
     `AdalySI1.Multiscale.M2.Lh_eq,
     `AdalySI1.Multiscale.M2.o_m2_scalar_one,
     `AdalySI1.Multiscale.M2.qCompositeBond_one,
     `AdalySI1.Multiscale.M2.hasDerivAt_su2Log_modifiedAverageS_physical_q124,
     `AdalySI1.Multiscale.M2.hasDerivAt_su2Log_modifiedAverageS_physical_q124_unitBond,
     `AdalySI1.Multiscale.M2.hasDerivAt_su2Log_iteratedAverage_qCompositeBond_zero,
     `AdalySI1.Multiscale.M2.hasDerivAt_su2Log_iteratedAverage_qCompositeBond_one,
     `AdalySI1.Multiscale.M2.qCompositeBondT1_one,
     `AdalySI1.Multiscale.M2.qCompositeBond_one_T1]
  for thm in thms do
    unless (← Lean.getEnv).contains thm do
      throwError "M2 missing declaration: {thm}"
    let axioms ← Lean.collectAxioms thm
    Lean.logInfo m!"M2_AXIOMS {thm}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {thm}: {ax}"
  Lean.logInfo "M2_IMPORT_FINGERPRINTS_PASS"

#print axioms hasDerivAt_su2Log_modifiedAverageS_physical_q124
#print axioms hasDerivAt_su2Log_modifiedAverageS_physical_q124_unitBond
#print axioms hasDerivAt_su2Log_iteratedAverage_qCompositeBond_zero
#print axioms hasDerivAt_su2Log_iteratedAverage_qCompositeBond_one
#print axioms qCompositeBond_one
#print axioms qCompositeBond_one_T1

end AdalySI1.Multiscale.M2
