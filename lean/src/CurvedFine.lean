/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import FineDrift
import TerminalBinder
import DatumWitness
import AdalyFormal.Balaban.RegularUQChain

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.style.longLine false
set_option maxRecDepth 8000

/-!
# `CurvedFine` — A CURVED BACKGROUND ON THE FINE TORUS, AND THE DATUM AT IT

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.

`FineDrift.fine_binder_forced_at_flat_fine_background` proves that at the tree's ONLY assembled
datum the fine-side smallness hypothesis is ALGEBRAICALLY FORCED: `DatumWitness.starDatum` is
`feedDatumGen starScale (trivialU fineL) …`, its fine background is FLAT, and the priced quantity
`‖H₁‖ · rawErrorCoeff ℓ (U_fine^{γ*})` is exactly `0` there.  An assertion that holds for every
budget whatsoever is not verification (S82).

This file builds the missing object: a genuinely curved configuration ON `fineL` (side `8`), the
per-cube data at it, and the datum assembled on it — with the priced quantity STRICTLY POSITIVE,
so the fine hypothesis is doing work rather than being satisfied by a zero.

## WHAT IS POLYMORPHIC AND WHAT WAS HARD-CODED

`CurvedContent.spikeU` is a single-link spike hard-coded to `witnessL` (`fun _ => 3`, side `4`) at
the bond `(witnessY, 0)`.  Every fact the tree proves about it depends only on WHICH bond is
excited, never on the torus — §1 therefore restates the construction with the bond as a parameter
and proves `spikeAt (witnessY, 0) = spikeU` definitionally (`spikeAt_eq_spikeU`, `rfl`), so nothing
below is a parallel construction that merely resembles the tree's.
-/

namespace AdalyFormal.CurvedFine

open Matrix AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.VariationalProjectorH1 (solutionOperator)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 witnessMElem)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL witnessY)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg
  frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AlphaAnalyticity (SU2 GaugeFn)
open AdalyFormal.Balaban.ConstantA (BaseConstant)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (IsSourceOperator cdcFormTrue bondQext)
open AdalyFormal.Balaban.SourceWiredJ (JsuTwo)
open AdalyFormal.Balaban.SourceWired (LinkDev)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.ConstructCDC (TildeFn)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem)
open AdalyFormal.Balaban.DriftPerCube (frobNorm_constGauge)
open AdalyFormal.Balaban.SuTwoLogExp (torus)
open AdalyFormal.Balaban.AbelianBlockingRate (torus_inv frobNorm_torus_sub_one
  sqrt_four_one_sub_cos)
open AdalyFormal.HrawCarriers (ScaleQuotient composedQ)
open AdalyFormal.MechEdges.G16 (rawErrorCoeff rawErrorCoeff_nonneg rawSigmaZero
  rawSigmaZero_pos)
open AdalyFormal.TerminalBinder (feedDatumGen)
open AdalyFormal.CovariantDatum (gluedGauge)
open AdalyFormal.DatumWitness (fineL starScale)
open AdalyFormal.FineDrift (PerCubeClass MismatchBound fineRadius)

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℂ

variable {L L' : PeriodicLatticeExtent}

/-! ## §1 — THE SINGLE-LINK SPIKE WITH THE TORUS AND THE BOND AS PARAMETERS -/

/-- **THE SPIKE, AT AN ARBITRARY BOND OF AN ARBITRARY TORUS.**  `g` on `e₀`, the identity
everywhere else. -/
noncomputable def spikeAt (e₀ : Bond L) (g : SU2) : PeriodicLinkConfiguration SU2 L :=
  fun e => if e = e₀ then g else 1

/-- **THE TREE'S OWN CURVED WITNESS IS A MEMBER OF THIS FAMILY**, definitionally. -/
theorem spikeAt_eq_spikeU (g : SU2) :
    spikeAt (witnessY, (0 : Fin 3)) g = AdalyFormal.Balaban.CurvedContent.spikeU g := rfl

theorem spikeAt_self (e₀ : Bond L) (g : SU2) : spikeAt e₀ g e₀ = g := by
  unfold spikeAt; rw [if_pos rfl]

theorem spikeAt_of_ne {e₀ e : Bond L} (g : SU2) (h : e ≠ e₀) : spikeAt e₀ g e = 1 := by
  unfold spikeAt; rw [if_neg h]

/-- The flat configuration is the `g = 1` member: the family interpolates between the tree's flat
background and a curved one inside a single definition. -/
theorem spikeAt_one (e₀ : Bond L) : spikeAt e₀ (1 : SU2) = trivialU L := by
  funext e; unfold spikeAt; split_ifs <;> rfl

theorem frobNorm_one_sub_one :
    AdalyFormal.Balaban.RMapLipschitz.frobNorm (((1 : SU2) : M₂) - 1) = 0 := by
  rw [show ((1 : SU2) : M₂) = 1 from rfl, sub_self]
  exact AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero

/-- **`α₁` OF A SPIKE IS THE EXCITED ELEMENT'S OWN DEVIATION**, on any torus and at any bond: the
sup over bonds is attained at `e₀`, every other bond contributing `0`. -/
theorem frobSupBond_spikeAt (e₀ : Bond L) (g : SU2) :
    frobSupBond (spikeAt e₀ g)
      = AdalyFormal.Balaban.RMapLipschitz.frobNorm ((g : M₂) - 1) := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ (fun b _ => ?_)
    by_cases hb : b = e₀
    · subst hb; rw [spikeAt_self]
    · rw [spikeAt_of_ne g hb, frobNorm_one_sub_one]
      exact AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _
  · have h := frobNorm_le_frobSupBond (spikeAt e₀ g) e₀
    rwa [spikeAt_self] at h

/-- `α₁(spike) = √(4(1−cos t))` at `g = torus t`. -/
theorem frobSupBond_spikeAt_torus (e₀ : Bond L) (t : ℝ) :
    frobSupBond (spikeAt e₀ (torus t)) = Real.sqrt (4 * (1 - Real.cos t)) := by
  rw [frobSupBond_spikeAt, frobNorm_torus_sub_one]

/-- **THE COVARIANCE-SIDE BOUND, ON ANY TORUS**: `α₁ ≤ √2·t`. -/
theorem frobSupBond_spikeAt_torus_le (e₀ : Bond L) {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ Real.pi) :
    frobSupBond (spikeAt e₀ (torus t)) ≤ Real.sqrt 2 * t := by
  rw [frobSupBond_spikeAt_torus, sqrt_four_one_sub_cos]
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h8]
  have hkey := AdalyFormal.Balaban.CurvedContent.two_abs_sin_half_le ht htpi
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [hkey, h2]

/-- `‖torus t − 1‖_F > 0` on `0 < t < π` — the one positivity every non-forcedness row below
rests on. -/
theorem frobNorm_torus_sub_one_pos {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    0 < AdalyFormal.Balaban.RMapLipschitz.frobNorm ((torus t : M₂) - 1) := by
  have hsin : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  rw [frobNorm_torus_sub_one, sqrt_four_one_sub_cos, abs_of_pos hsin]
  have h8 : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  positivity

/-- **`torus t ≠ 1` on `0 < t < π`** — the group-level fact behind curvature. -/
theorem torus_ne_one {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) : (torus t : SU2) ≠ 1 := by
  intro hc
  have h := frobNorm_torus_sub_one_pos ht htpi
  rw [show ((torus t : SU2) : M₂) = ((1 : SU2) : M₂) from congrArg _ hc] at h
  rw [frobNorm_one_sub_one] at h
  exact lt_irrefl _ h

/-- `α₁(spike) > 0` on `0 < t < π`, on any torus. -/
theorem frobSupBond_spikeAt_torus_pos (e₀ : Bond L) {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    0 < frobSupBond (spikeAt e₀ (torus t)) := by
  rw [frobSupBond_spikeAt]
  exact frobNorm_torus_sub_one_pos ht htpi

/-! ## §2 — CURVATURE ON AN ARBITRARY TORUS: THE PLAQUETTE HOLONOMY OF A SPIKE -/

/-- **A ONE-STEP SHIFT MOVES THE SITE**, whenever the torus has at least two sites in that
direction.  A general lattice fact; the tree had it only as `decide` at `witnessL`. -/
theorem shift_ne_self (x : PeriodicLatticeSite L) (ν : Fin 3) (hL : 0 < L ν) :
    periodicLatticeShift x ν ≠ x := by
  intro hc
  have h : (Function.update x ν (x ν + 1)) ν = x ν := congrFun hc ν
  rw [Function.update_self] at h
  have hv : (((x ν) + 1 : Fin (L ν + 1)) : ℕ) = ((x ν : Fin (L ν + 1)) : ℕ) := congrArg Fin.val h
  rw [Fin.val_add_one] at hv
  split_ifs at hv with hlast
  · have hx : ((x ν : Fin (L ν + 1)) : ℕ) = L ν := by rw [hlast]; rfl
    omega
  · omega

/-- **THE PLAQUETTE HOLONOMY OF A SPIKE IS THE EXCITED ELEMENT ITSELF**, at the plaquette based at
the excited bond's own site in the plane containing its direction.

The four-link word (`ClayStatement.periodicPlaquetteHolonomy`) is
`U(x,μ)·U(x+μ̂,ν)·U(x+ν̂,μ)⁻¹·U(x,ν)⁻¹`.  Three of the four links are off the excited bond: two
because `ν ≠ μ` (which `PeriodicPlaquetteDirections` supplies as `μ < ν`), and one because
`x + ν̂ ≠ x`.  That last is the ONLY geometric input, and §2's `shift_ne_self` supplies it. -/
theorem holonomy_spikeAt (x : PeriodicLatticeSite L) (d : PeriodicPlaquetteDirections)
    (g : SU2) (hshift : periodicLatticeShift x d.1.2 ≠ x) :
    holonomyElem (spikeAt (x, d.1.1) g) (x, d) = g := by
  have hne : d.1.1 ≠ d.1.2 := ne_of_lt d.2
  have h1 : spikeAt (x, d.1.1) g (x, d.1.1) = g := spikeAt_self _ _
  have h2 : spikeAt (x, d.1.1) g (periodicLatticeShift x d.1.1, d.1.2) = 1 :=
    spikeAt_of_ne g (by
      intro hc
      exact hne (congrArg Prod.snd hc).symm)
  have h3 : spikeAt (x, d.1.1) g (periodicLatticeShift x d.1.2, d.1.1) = 1 :=
    spikeAt_of_ne g (by
      intro hc
      exact hshift (congrArg Prod.fst hc))
  have h4 : spikeAt (x, d.1.1) g (x, d.1.2) = 1 :=
    spikeAt_of_ne g (by
      intro hc
      exact hne (congrArg Prod.snd hc).symm)
  show spikeAt (x, d.1.1) g (x, d.1.1) * spikeAt (x, d.1.1) g (periodicLatticeShift x d.1.1, d.1.2)
      * (spikeAt (x, d.1.1) g (periodicLatticeShift x d.1.2, d.1.1))⁻¹
      * (spikeAt (x, d.1.1) g (x, d.1.2))⁻¹ = g
  rw [h1, h2, h3, h4, inv_one, mul_one, mul_one, mul_one]

/-- **THE SPIKE IS CURVED ON ANY TORUS WITH AT LEAST TWO SITES IN THE SECOND PLAQUETTE
DIRECTION**: nonzero plaquette holonomy AND `0 < α₁`. -/
theorem spikeAt_is_curved (x : PeriodicLatticeSite L) (d : PeriodicPlaquetteDirections)
    (hL : 0 < L d.1.2) {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    holonomyElem (spikeAt (x, d.1.1) (torus t)) (x, d) ≠ 1
      ∧ 0 < frobSupBond (spikeAt (x, d.1.1) (torus t)) := by
  refine ⟨?_, frobSupBond_spikeAt_torus_pos _ ht htpi⟩
  rw [holonomy_spikeAt x d (torus t) (shift_ne_self x d.1.2 hL)]
  exact torus_ne_one ht htpi

/-- **THE SOURCE-SIDE CLASS ON ANY TORUS**: `LinkDev t` at the `torus t` spike.  The proof is
`CurvedContent.linkDev_spike_torus`'s, with the bond and the torus as parameters. -/
theorem linkDev_spikeAt_torus (e₀ : Bond L) {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ Real.pi) :
    LinkDev t (spikeAt e₀ (torus t)) := by
  intro b
  by_cases hb : b = e₀
  · subst hb
    rw [spikeAt_self]
    have hentry : ((torus t : SU2) : M₂) - 1
        = AdalyFormal.Balaban.SuTwoLogExp.dg (Complex.exp ((t : ℂ) * Complex.I) - 1)
            (Complex.exp (-((t : ℂ) * Complex.I)) - 1) := by
      rw [AdalyFormal.Balaban.CurvedContent.coe_torus_dg,
        ← AdalyFormal.Balaban.SuTwoLogExp.dg_one, AdalyFormal.Balaban.SuTwoLogExp.dg_sub]
    rw [hentry]
    refine AdalyFormal.Balaban.CurvedContent.EB_dg ht ?_ ?_
    · rw [AdalyFormal.Balaban.CurvedContent.norm_cexp_sub_one]
      exact AdalyFormal.Balaban.CurvedContent.two_abs_sin_half_le ht htpi
    · rw [show Complex.exp (-((t : ℂ) * Complex.I))
          = Complex.exp (((-t : ℝ) : ℂ) * Complex.I) by push_cast; ring_nf]
      rw [AdalyFormal.Balaban.CurvedContent.norm_cexp_sub_one (-t),
        show (-t) / 2 = -(t / 2) by ring, Real.sin_neg, abs_neg]
      exact AdalyFormal.Balaban.CurvedContent.two_abs_sin_half_le ht htpi
  · rw [spikeAt_of_ne _ hb, show (((1 : SU2) : M₂) - 1) = 0 by
      rw [show ((1 : SU2) : M₂) = 1 from rfl, sub_self]]
    intro i j
    simpa using ht

/-! ## §3 — `U*_fine`: THE CURVED BACKGROUND ON THE `8³` FINE TORUS

`DatumWitness.fineL = fun _ => 7`, side `8`, sitting over `witnessL = fun _ => 3`, side `4`, via
`starScale : ScaleQuotient fineL 2 witnessL`.  The excited bond is at the origin in direction `0`;
the cover of §4 is a slab in direction `2`, so BOTH endpoints of the excited bond lie in the SAME
cube and the spike's own deviation survives the gauge (§4c). -/

/-- The origin of the fine torus. -/
def fineOrigin : PeriodicLatticeSite fineL := fun _ => 0

/-- The excited bond: the origin, direction `0`. -/
def fineBond : Bond fineL := (fineOrigin, (0 : Fin 3))

/-- The `(0,1)` plaquette direction pair. -/
def dir01 : PeriodicPlaquetteDirections := ⟨(0, 1), by decide⟩

/-- The plaquette carrying the curvature: based at the origin, in the `(0,1)` plane. -/
def finePlaquette : PeriodicLatticePlaquette fineL := (fineOrigin, dir01)

/-- **`U*_fine`, THE CURVED BACKGROUND ON THE FINE TORUS.** -/
noncomputable def UfineStar (t : ℝ) : PeriodicLinkConfiguration SU2 fineL :=
  spikeAt fineBond (torus t)

/-- **THE FINE BACKGROUND IS CURVED ON THE FINE TORUS'S OWN PLAQUETTES.**  The holonomy is taken
at `finePlaquette : PeriodicLatticePlaquette fineL` — a plaquette of the `8³` lattice, not of the
`4³` coarse one, and not inherited through any blocking map. -/
theorem UfineStar_is_curved {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    holonomyElem (UfineStar t) finePlaquette ≠ 1 ∧ 0 < frobSupBond (UfineStar t) :=
  spikeAt_is_curved fineOrigin dir01 (by decide) ht htpi

/-- **AND IT IS NOT THE FLAT BACKGROUND**, which is what `starDatum` is built on. -/
theorem UfineStar_ne_trivialU {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    UfineStar t ≠ trivialU fineL := by
  intro hc
  have h := (UfineStar_is_curved ht htpi).2
  rw [hc] at h
  have hz : frobSupBond (trivialU fineL) = 0 := by
    rw [show trivialU fineL = spikeAt fineBond (1 : SU2) from (spikeAt_one fineBond).symm,
      frobSupBond_spikeAt]
    exact frobNorm_one_sub_one
  rw [hz] at h
  exact lt_irrefl _ h

theorem frobSupBond_UfineStar_le {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ Real.pi) :
    frobSupBond (UfineStar t) ≤ Real.sqrt 2 * t :=
  frobSupBond_spikeAt_torus_le fineBond ht htpi

theorem frobSupBond_UfineStar_pos {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    0 < frobSupBond (UfineStar t) :=
  frobSupBond_spikeAt_torus_pos fineBond ht htpi

theorem linkDev_UfineStar {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ Real.pi) :
    LinkDev t (UfineStar t) :=
  linkDev_spikeAt_torus fineBond ht htpi

/-! ## §4 — THE PER-CUBE FINE CLASS AT `U*_fine`, AND WHY IT IS NOT FORCED -/

/-- **A GLUED GAUGE ACTS AS A CONJUGATION ON ANY BOND WHOSE TWO ENDPOINTS CARRY THE SAME GROUP
ELEMENT.**  The general bond-local form of `DriftPerCube.frobNorm_constGauge` (which needs the
gauge constant on the WHOLE torus); it is what lets an interior bond's deviation be read off the
ungauged configuration while other bonds still pay a mismatch.  Reusable. -/
theorem frobNorm_glued_eq_of_const_on_bond {ι : Type*} (assign : PeriodicLatticeSite L → ι)
    (γ : ι → GaugeFn L) (U : PeriodicLinkConfiguration SU2 L) (b : Bond L) (c : SU2)
    (h1 : γ (assign b.1) b.1 = c)
    (h2 : γ (assign (periodicLatticeShift b.1 b.2)) (periodicLatticeShift b.1 b.2) = c) :
    AdalyFormal.Balaban.RMapLipschitz.frobNorm
        (((periodicGaugeTransform (gluedGauge assign γ) U) b : M₂) - 1)
      = AdalyFormal.Balaban.RMapLipschitz.frobNorm ((U b : M₂) - 1) := by
  have hb : (periodicGaugeTransform (gluedGauge assign γ) U) b
      = (periodicGaugeTransform (fun _ => c) U) b := by
    show gluedGauge assign γ b.1 * U b * (gluedGauge assign γ (periodicLatticeShift b.1 b.2))⁻¹
      = c * U b * c⁻¹
    rw [show gluedGauge assign γ b.1 = c from h1,
      show gluedGauge assign γ (periodicLatticeShift b.1 b.2) = c from h2]
  rw [hb, frobNorm_constGauge]

/-- **THE PER-CUBE CLASS AT CONSTANT-PER-CUBE GAUGES, ON ANY TORUS**, at radius `α₁(U)`: a constant
gauge is a conjugation and moves no deviation.  `FineDrift`'s version is `witnessL`-only; this one
is polymorphic in the torus and in the cube index type. -/
theorem perCubeClass_of_constGauges {ι : Type*} (assign : PeriodicLatticeSite L → ι)
    (c : ι → SU2) (U : PeriodicLinkConfiguration SU2 L) :
    PerCubeClass assign (fun i => (fun _ => c i)) U (frobSupBond U) := by
  intro b
  show AdalyFormal.Balaban.RMapLipschitz.frobNorm
    (((periodicGaugeTransform (fun _ => c (assign b.1)) U) b : M₂) - 1) ≤ frobSupBond U
  rw [frobNorm_constGauge]
  exact frobNorm_le_frobSupBond U b

/-- The two-cube cover of the FINE torus: the `x₂ = 0` layer and its complement.  Direction `2` is
chosen so that the excited bond (direction `0`) has BOTH endpoints inside one cube — see §4c. -/
def fSlab (x : PeriodicLatticeSite fineL) : Bool := decide ((x 2 : ℕ) = 0)

/-- Per-cube gauges on the fine torus: constant on each cube, DIFFERENT between them. -/
noncomputable def fGauge (s : ℝ) (i : Bool) : GaugeFn fineL :=
  fun _ => if i then torus s else 1

theorem frobNorm_torus_sub_one_le {s : ℝ} (hs : 0 ≤ s) (hspi : s ≤ Real.pi) :
    AdalyFormal.Balaban.RMapLipschitz.frobNorm ((torus s : M₂) - 1) ≤ Real.sqrt 2 * s := by
  rw [frobNorm_torus_sub_one, sqrt_four_one_sub_cos]
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h8]
  have hkey := AdalyFormal.Balaban.CurvedContent.two_abs_sin_half_le hs hspi
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [hkey, h2]

theorem frobNorm_torus_neg_sub_one_le {s : ℝ} (hs : 0 ≤ s) (hspi : s ≤ Real.pi) :
    AdalyFormal.Balaban.RMapLipschitz.frobNorm ((torus (-s) : M₂) - 1) ≤ Real.sqrt 2 * s := by
  have hcos : Real.cos (-s) = Real.cos s := Real.cos_neg s
  rw [frobNorm_torus_sub_one, hcos, ← frobNorm_torus_sub_one]
  exact frobNorm_torus_sub_one_le hs hspi

/-- **§4a — THE MISMATCH OF THE FINE TWO-CUBE FAMILY IS `≤ √2·s`.** -/
theorem fGauge_mismatch {s : ℝ} (hs : 0 ≤ s) (hspi : s ≤ Real.pi) :
    MismatchBound fSlab (fGauge s) (Real.sqrt 2 * s) := by
  intro b
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 * s := by positivity
  show AdalyFormal.Balaban.RMapLipschitz.frobNorm ((((if fSlab b.1 then torus s else 1)
      * (if fSlab (periodicLatticeShift b.1 b.2) then torus s else 1)⁻¹ : SU2) : M₂) - 1)
    ≤ Real.sqrt 2 * s
  by_cases h1 : fSlab b.1 <;> by_cases h2 : fSlab (periodicLatticeShift b.1 b.2)
  · rw [if_pos h1, if_pos h2, mul_inv_cancel]
    exact le_of_eq_of_le frobNorm_one_sub_one hnn
  · rw [if_pos h1, if_neg h2, inv_one, mul_one]
    exact frobNorm_torus_sub_one_le hs hspi
  · rw [if_neg h1, if_pos h2, one_mul, torus_inv]
    exact frobNorm_torus_neg_sub_one_le hs hspi
  · rw [if_neg h1, if_neg h2, inv_one, mul_one]
    exact le_of_eq_of_le frobNorm_one_sub_one hnn

/-- **§4b — THE TWO FINE PER-CUBE GAUGES GENUINELY DIFFER**, on `0 < s ≤ π`, so the family is not a
global gauge in disguise and `FineDrift.perCube_iff_global_of_boundaryMatch`'s collapse does not
cover it. -/
theorem fGauge_ne {s : ℝ} (hs : 0 < s) (hspi : s ≤ Real.pi) : fGauge s true ≠ fGauge s false := by
  intro hc
  have hval : (torus s : SU2) = 1 := by
    have h0 := congrFun hc fineOrigin
    simpa [fGauge] using h0
  exact torus_ne_one hs (lt_of_le_of_ne hspi (by
    intro hpi
    have : Real.cos s = -1 := by rw [hpi]; exact Real.cos_pi
    have hz : AdalyFormal.Balaban.RMapLipschitz.frobNorm ((torus s : M₂) - 1) = 0 := by
      rw [show ((torus s : SU2) : M₂) = ((1 : SU2) : M₂) from congrArg _ hval]
      exact frobNorm_one_sub_one
    rw [frobNorm_torus_sub_one, this] at hz
    have : Real.sqrt (4 * (1 - (-1 : ℝ))) = 0 := hz
    norm_num at this)) hval

/-- **§4c — THE EXCITED BOND IS INTERIOR TO ONE CUBE.**  Both endpoints of `fineBond` have
`x₂ = 0`, so the slab cover assigns them the SAME cube; the cover is in direction `2` and the bond
in direction `0`. -/
theorem fSlab_fineBond_interior :
    fSlab (periodicLatticeShift fineBond.1 fineBond.2) = fSlab fineBond.1 := by
  decide

/-- The excited bond's base site lies in the `x₂ = 0` cube. -/
theorem fSlab_fineBond_base : fSlab fineBond.1 = true := by decide

/-- **§4d — THE GAUGED FINE BACKGROUND STILL CARRIES THE SPIKE.**  At the excited bond the glued
gauge acts as a conjugation, so the deviation there is EXACTLY the ungauged one. -/
theorem frobNorm_gauged_UfineStar_at_bond (s t : ℝ) :
    AdalyFormal.Balaban.RMapLipschitz.frobNorm
        (((periodicGaugeTransform (gluedGauge fSlab (fGauge s)) (UfineStar t)) fineBond : M₂) - 1)
      = AdalyFormal.Balaban.RMapLipschitz.frobNorm ((torus t : M₂) - 1) := by
  rw [frobNorm_glued_eq_of_const_on_bond fSlab (fGauge s) (UfineStar t) fineBond (torus s)
    (by rw [fSlab_fineBond_base]; rfl)
    (by rw [fSlab_fineBond_interior, fSlab_fineBond_base]; rfl), UfineStar, spikeAt_self]

/-- **§4e — THE PRICED FINE QUANTITY IS STRICTLY POSITIVE AT `U*_fine`.**

This is the exact negation of `FineDrift.fine_binder_forced_at_flat_fine_background`'s mechanism:
there the priced quantity is `= 0` for every coefficient, so the hypothesis is algebraically forced
(S82); here it is `> 0`, so the hypothesis constrains the background. -/
theorem fine_price_pos_at_UfineStar {ell : ℕ} (hell : 0 < ell) {K : ℝ} (hK : 0 < K)
    (s : ℝ) {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    0 < K * rawErrorCoeff ell
      (periodicGaugeTransform (gluedGauge fSlab (fGauge s)) (UfineStar t)) := by
  have hbond : 0 < AdalyFormal.Balaban.RMapLipschitz.frobNorm
      (((periodicGaugeTransform (gluedGauge fSlab (fGauge s)) (UfineStar t)) fineBond : M₂) - 1) := by
    rw [frobNorm_gauged_UfineStar_at_bond]
    exact frobNorm_torus_sub_one_pos ht htpi
  have hsup : 0 < frobSupBond
      (periodicGaugeTransform (gluedGauge fSlab (fGauge s)) (UfineStar t)) :=
    lt_of_lt_of_le hbond (frobNorm_le_frobSupBond _ fineBond)
  have hre : rawErrorCoeff ell (periodicGaugeTransform (gluedGauge fSlab (fGauge s)) (UfineStar t))
      = (36 * Real.sqrt 2 / Real.sqrt (ell : ℝ))
        * frobSupBond (periodicGaugeTransform (gluedGauge fSlab (fGauge s)) (UfineStar t)) := rfl
  rw [hre]
  have hl : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hsq : (0 : ℝ) < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr hl
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hcoef : (0 : ℝ) < 36 * Real.sqrt 2 / Real.sqrt (ell : ℝ) :=
    div_pos (by linarith) hsq
  exact mul_pos hK (mul_pos hcoef hsup)

/-- **§4f — AND THE PER-CUBE RADIUS AT `U*_fine` IS POSITIVE, NOT ZERO.**  `FineDrift`'s forced
instance sits at radius `0` and mismatch `0`; this family sits at radius `α₁(U*_fine) > 0` and
mismatch `√2·s`, with the two per-cube gauges genuinely different (§4b). -/
theorem fine_perCube_radius_pos_at_UfineStar (s : ℝ) {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    PerCubeClass fSlab (fGauge s) (UfineStar t) (frobSupBond (UfineStar t))
      ∧ 0 < frobSupBond (UfineStar t) := by
  refine ⟨?_, frobSupBond_UfineStar_pos ht htpi⟩
  exact perCubeClass_of_constGauges fSlab (fun i => if i then torus s else 1) (UfineStar t)

/-- **§4g — THE FINE BINDER HOLDS AT `U*_fine` INSIDE `FineDrift`'s EXACT BUDGET.** -/
theorem fine_binder_at_UfineStar {ell ell₀ : ℕ} (hell : 0 < ell) (hell₀ : 0 < ell₀)
    (K : ℝ) (hK : 0 < K) {t s : ℝ} (ht : 0 ≤ t) (htpi : t ≤ Real.pi)
    (hs : 0 ≤ s) (hspi : s ≤ Real.pi)
    (hbudget : Real.sqrt 2 * t + Real.sqrt 2 * s ≤ fineRadius ell ell₀ K) :
    K * rawErrorCoeff ell
        (periodicGaugeTransform (gluedGauge fSlab (fGauge s)) (UfineStar t))
      ≤ 1 / (4708 * (ell₀ : ℝ) ^ 3) := by
  refine AdalyFormal.FineDrift.hsmallFineGauged_of_perCube hell hell₀ K hK fSlab (fGauge s) _
    (frobSupBond (UfineStar t)) (Real.sqrt 2 * s)
    (perCubeClass_of_constGauges fSlab (fun i => if i then torus s else 1) (UfineStar t))
    (fGauge_mismatch hs hspi) ?_
  have hr := frobSupBond_UfineStar_le ht htpi
  linarith

/-- **§4h — THE WINDOW IS NONEMPTY IN CLOSED FORM, AT STRICTLY POSITIVE `t`.**  Witness:
`t = s = min 1 (fineRadius/4)`.  Both are `> 0`, so §4g is never invoked at the forced point. -/
theorem fine_window_nonempty_curved {ell ell₀ : ℕ} (hell : 0 < ell) (hell₀ : 0 < ell₀)
    {K : ℝ} (hK : 0 < K) :
    ∃ t s : ℝ, 0 < t ∧ t < Real.pi ∧ 0 < s ∧ s ≤ Real.pi
      ∧ Real.sqrt 2 * t + Real.sqrt 2 * s ≤ fineRadius ell ell₀ K := by
  have hR : 0 < fineRadius ell ell₀ K := AdalyFormal.FineDrift.fineRadius_pos hell hell₀ hK
  set c : ℝ := min 1 (fineRadius ell ell₀ K / 4) with hcdef
  have hc0 : 0 < c := lt_min one_pos (by linarith)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcR : c ≤ fineRadius ell ell₀ K / 4 := min_le_right _ _
  have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  refine ⟨c, c, hc0, lt_of_le_of_lt hc1 hpi, hc0, le_of_lt (lt_of_le_of_lt hc1 hpi), ?_⟩
  nlinarith [hs2, hc0, hcR, Real.sqrt_nonneg 2]


/-! ## §5 — THE DATUM ASSEMBLED ON `U*_fine`

`DatumWitness.starDatum bc heps = feedDatumGen starScale (trivialU fineL) heps _`
(`starDatum_eq_feedDatumGen`, CITED, `rfl`).  §5 assembles the SAME constructor on the curved fine
background of §3 and re-proves, at that background, each datum-level fact the terminal chain
consumes.  Nothing is inherited by "it was true at the flat one": every row below names the
configuration it is proved at. -/

/-- **THE CURVED-FINE DATUM.**  Same constructor, curved fine background. -/
noncomputable def curvedFineDatum (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) (t : ℝ) :
    AdalyFormal.Balaban.VariationalProjectorH1.BalabanCovarianceData
      (BondFnL2 fineL) (BondFnL2 witnessL) :=
  feedDatumGen starScale (UfineStar t) heps (le_of_lt bc.a_pos)

/-- **THE `Q` SLOT IS THE COMPOSED BLOCK AVERAGE AT THE CURVED FINE BACKGROUND**, `rfl`.  Compare
`DatumWitness.starDatum_Q`, whose right-hand side is `composedQ starScale (trivialU fineL)`: the
constraint operator itself moves with the fine background (`qCLM U ell` carries `U`), so no
`Q`-level fact may be inherited from the flat datum without re-proof. -/
theorem curvedFineDatum_Q (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) (t : ℝ) :
    (curvedFineDatum bc heps t).Q = composedQ starScale (UfineStar t) := rfl

/-- **§5a — `Q` IS STILL NOT INJECTIVE AT THE CURVED FINE BACKGROUND.**  Re-proved AT `U*_fine`
(`feedDatumGen_Q_not_injective` is general in the fine background and is applied here at `ell = 2`),
not transported from `starDatum`. -/
theorem curvedFineDatum_Q_not_injective (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) (t : ℝ) :
    ¬ Function.Injective (curvedFineDatum bc heps t).Q :=
  AdalyFormal.TerminalBinder.feedDatumGen_Q_not_injective starScale (le_refl 2) (UfineStar t)
    heps (le_of_lt bc.a_pos)

/-- **§5b — `ker Q ≠ ⊥` AT THE CURVED FINE BACKGROUND**, exhibited as a nonzero vector. -/
theorem curvedFineDatum_kernel_nonzero (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) (t : ℝ) :
    ∃ k : BondFnL2 fineL, k ≠ 0 ∧ (curvedFineDatum bc heps t).Q k = 0 :=
  AdalyFormal.TerminalBinder.exists_kernel_vector _ (curvedFineDatum_Q_not_injective bc heps t)

/-- **§5c — THE `ε`-COERCIVITY AT THE CURVED FINE BACKGROUND, WITH THE MODULUS PRICED.**
`‖A‖² ≤ (1/ε)·⟨A, G₁⁻¹A⟩`.  The modulus is `1/ε` — the SAME number as at the flat fine background,
and in particular it does not degrade with the curvature parameter `t`: `t` does not occur on the
right-hand side. -/
theorem curvedFineDatum_coercive (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) (t : ℝ)
    (A : BondFnL2 fineL) :
    ‖A‖ ^ 2 ≤ (1 / eps) * (inner ℝ A ((curvedFineDatum bc heps t).Ginv A) : ℝ) :=
  AdalyFormal.TerminalBinder.feedGinvGen_coercive starScale (UfineStar t) heps
    (le_of_lt bc.a_pos) A

/-- **§5d — THE MODULUS IS THE SAME AT EVERY CURVATURE PARAMETER, INCLUDING `t = 0`.**  Stated as
one theorem over two arbitrary parameters so that "the modulus does not change" is a kernel fact
rather than a reading of §5c's statement. -/
theorem curvedFineDatum_modulus_curvature_free (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (t t' : ℝ) (A : BondFnL2 fineL) :
    ‖A‖ ^ 2 ≤ (1 / eps) * (inner ℝ A ((curvedFineDatum bc heps t).Ginv A) : ℝ)
      ∧ ‖A‖ ^ 2 ≤ (1 / eps) * (inner ℝ A ((curvedFineDatum bc heps t').Ginv A) : ℝ) :=
  ⟨curvedFineDatum_coercive bc heps t A, curvedFineDatum_coercive bc heps t' A⟩

/-- **§5e — WHAT THE `ε` SUMMAND IS ACTUALLY CARRYING.**  The quadratic form splits as

    ⟨A, G₁⁻¹A⟩  =  ‖∂_{U*_fine}A‖²  +  ε‖A‖²  +  a‖QA‖² ,

and ON THE KERNEL OF `Q` — which §5b proves is not `{0}` at the curved fine background — the THIRD
summand is exactly `0`.  So the `a·Q*Q` term contributes nothing to definiteness on a nonzero
subspace, and the coercivity modulus of §5c is carried by `ε` there together with whatever the
covariant coboundary supplies.  This is the non-vacuity check the regulator has to pass: it is
stated at a vector that exists, and it is an EQUALITY, not a bound. -/
theorem curvedFineDatum_form_on_kernel (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) (t : ℝ)
    {k : BondFnL2 fineL} (hk : (curvedFineDatum bc heps t).Q k = 0) :
    (inner ℝ k ((curvedFineDatum bc heps t).Ginv k) : ℝ)
      = ‖curlCovariantCLM_L2 (UfineStar t) k‖ ^ 2 + eps * ‖k‖ ^ 2 := by
  have hQ : composedQ starScale (UfineStar t) k = 0 := hk
  show (inner ℝ k ((feedDatumGen starScale (UfineStar t) heps (le_of_lt bc.a_pos)).Ginv k) : ℝ) = _
  rw [AdalyFormal.TerminalBinder.feedDatumGen_Ginv starScale (UfineStar t) heps
    (le_of_lt bc.a_pos), AdalyFormal.TerminalBinder.inner_feedGinvGen, hQ, norm_zero]
  ring

/-- **§5f — EQUIVARIANCE AT THE CURVED FINE BACKGROUND, FIELD BY FIELD.**  The two slots that
depend on the fine background are `Ginv` and `Q` (§5's `curvedFineDatum_Q`); both intertwine, `Q`
with the INDUCED coarse gauge.  Instantiated at `U*_fine` from `CovDatum`'s general rows. -/
theorem curvedFineDatum_equivariance (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) (t : ℝ)
    (γ : GaugeFn fineL) (A : BondFnL2 fineL) (B : BondFnL2 witnessL) :
    (feedDatumGen starScale (periodicGaugeTransform γ (UfineStar t)) heps
        (le_of_lt bc.a_pos)).Ginv (AdalyFormal.CovariantDatum.gaugeL2 γ A)
        = AdalyFormal.CovariantDatum.gaugeL2 γ ((curvedFineDatum bc heps t).Ginv A)
      ∧ (feedDatumGen starScale (periodicGaugeTransform γ (UfineStar t)) heps
          (le_of_lt bc.a_pos)).Q (AdalyFormal.CovariantDatum.gaugeL2 γ A)
        = AdalyFormal.CovariantDatum.gaugeL2 (AdalyFormal.CovariantDatum.coarseGauge starScale γ)
            ((curvedFineDatum bc heps t).Q A)
      ∧ solutionOperator (feedDatumGen starScale (periodicGaugeTransform γ (UfineStar t)) heps
          (le_of_lt bc.a_pos))
          (AdalyFormal.CovariantDatum.gaugeL2 (AdalyFormal.CovariantDatum.coarseGauge starScale γ) B)
        = AdalyFormal.CovariantDatum.gaugeL2 γ (solutionOperator (curvedFineDatum bc heps t) B)
      ∧ ‖solutionOperator (feedDatumGen starScale (periodicGaugeTransform γ (UfineStar t)) heps
          (le_of_lt bc.a_pos))‖ = ‖solutionOperator (curvedFineDatum bc heps t)‖ :=
  ⟨AdalyFormal.CovariantDatum.feedDatumGen_Ginv_gauge starScale γ (UfineStar t) heps
      (le_of_lt bc.a_pos) A,
   AdalyFormal.CovariantDatum.feedDatumGen_Q_gauge starScale γ (UfineStar t) heps
      (le_of_lt bc.a_pos) A,
   AdalyFormal.CovariantDatum.feedDatumGen_solutionOperator_gauge starScale γ (UfineStar t) heps
      (le_of_lt bc.a_pos) B,
   AdalyFormal.CovariantDatum.norm_solutionOperator_feedDatumGen_gauge starScale γ (UfineStar t)
      heps (le_of_lt bc.a_pos)⟩

/-- **§5g — AND THE CURVATURE IS NOT GAUGEABLE AWAY.**  Under EVERY gauge the fine background stays
curved at the SAME fine plaquette (`NonFlatBackground.holonomyElem_periodicGaugeTransform_eq_one_iff`,
REUSED).  Without this, §5f could be read as "the equivariance holds, but the object it is applied
to might be flat in some frame". -/
theorem UfineStar_curved_in_every_gauge (γ : GaugeFn fineL) {t : ℝ} (ht : 0 < t)
    (htpi : t < Real.pi) :
    holonomyElem (periodicGaugeTransform γ (UfineStar t)) finePlaquette ≠ 1 := by
  intro hc
  exact (UfineStar_is_curved ht htpi).1
    ((AdalyFormal.Balaban.NonFlatBackground.holonomyElem_periodicGaugeTransform_eq_one_iff
      (L := fineL) γ (UfineStar t) finePlaquette).mp hc)

/-! ## §6 — THE END-TO-END INSTANCE: BOTH SCALES CURVED, AT ONE CONFIGURATION PAIR

`DatumWitness.terminal_posDef_at_star_datum` is the tree's end-to-end row: curved COARSE background,
FLAT fine background, at `starDatum`.  §6 is the same row with the fine background curved too —
`U*_fine` of §3 on the `8³` torus and `CurvedContent.spikeU (torus t_c)` on the `4³` one.  The
consumer is `TerminalBinder.terminal_at_composed_carriers_generalFine`, whose fine background is
arbitrary and whose price for that is exactly one extra smallness line. -/

/-- The coefficient of `t_c²` in the source threshold AT THE CURVED-FINE DATUM.  Same factors as
`DatumWitness.starC`, with `‖H₁‖` and `‖Q*‖` taken at `curvedFineDatum` rather than at `starDatum`
— they are different data and the numbers are not asserted equal. -/
noncomputable def curvedC (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) (t : ℝ) : ℝ :=
  (1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2
      * ‖solutionOperator (curvedFineDatum bc heps t)‖
      * (‖(curvedFineDatum bc heps t).Qstar‖
          * Real.sqrt (2 * (Fintype.card (Bond witnessL)))))
    * AdalyFormal.Balaban.CurvedContent.spikeK

theorem curvedC_nonneg (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) (t : ℝ) :
    0 ≤ curvedC bc heps t := by
  unfold curvedC
  have h1 : (0 : ℝ) ≤ AdalyFormal.Balaban.CurvedContent.spikeK :=
    le_of_lt AdalyFormal.Balaban.CurvedContent.spikeK_pos
  positivity

/-- **§6a — THE FINE SMALLNESS LINE, DISCHARGED FROM A BOUND ON `‖H₁‖` AND A BUDGET ON `t`.** -/
theorem hsmallFine_at_UfineStar (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) {t : ℝ}
    (ht : 0 ≤ t) (htpi : t ≤ Real.pi) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ‖solutionOperator (curvedFineDatum bc heps t)‖ ≤ K)
    (hfine : Real.sqrt 2 * t
      ≤ Real.sqrt ((2 : ℕ) : ℝ) / (2356 * (36 * Real.sqrt 2) * (K + 1) * ((2 : ℕ) : ℝ) ^ 3)) :
    ‖solutionOperator (curvedFineDatum bc heps t)‖ * rawErrorCoeff 2 (UfineStar t)
      ≤ 1 / (2356 * ((2 : ℕ) : ℝ) ^ 3) := by
  have hα : frobSupBond (UfineStar t)
      ≤ Real.sqrt ((2 : ℕ) : ℝ) / (2356 * (36 * Real.sqrt 2) * (K + 1) * ((2 : ℕ) : ℝ) ^ 3) :=
    le_trans (frobSupBond_UfineStar_le ht htpi) hfine
  have hbig := AdalyFormal.TerminalBinder.hsmallFine_of_alphaFine_small
    (ell := 2) (ell₀ := 2) (by norm_num) (by norm_num) (UfineStar t) K hK0 hα
  have hraw : (0 : ℝ) ≤ rawErrorCoeff 2 (UfineStar t) := rawErrorCoeff_nonneg 2 (UfineStar t)
  have hstep : ‖solutionOperator (curvedFineDatum bc heps t)‖ * rawErrorCoeff 2 (UfineStar t)
      ≤ K * rawErrorCoeff 2 (UfineStar t) := mul_le_mul_of_nonneg_right hK hraw
  linarith

/-- **§6b — THE COARSE SMALLNESS LINE AT THE COARSE SPIKE**, at the factor-`2` TIGHTER class the
general-fine chain demands (`1/(13336·ℓ₀³)`, not `1/(6668·ℓ₀³)`). -/
theorem hsmallU_at_coarse_spike {tc : ℝ} (htc : 0 ≤ tc) (htcpi : tc ≤ Real.pi)
    (hcov : Real.sqrt 2 * tc ≤ 1 / 106688) :
    frobSupBond (AdalyFormal.Balaban.CurvedContent.spikeU (torus tc))
      ≤ 1 / (13336 * ((2 : ℕ) : ℝ) ^ 3) := by
  have h1 := AdalyFormal.Balaban.CurvedContent.frobSupBond_spike_le htc htcpi
  have h2 : (1 : ℝ) / (13336 * ((2 : ℕ) : ℝ) ^ 3) = 1 / 106688 := by norm_num
  rw [h2]; linarith

/-- **§6c — THE END-TO-END INSTANCE, BOTH SCALES CURVED.**

At `ℓ = 2` over `ℓ₀ = 2`, at the datum `feedDatumGen starScale (U*_fine) heps _` whose

* FINE background `U*_fine` is curved on the `8³` torus's OWN plaquette (`UfineStar_is_curved`,
  and in every gauge, `UfineStar_curved_in_every_gauge`), with the priced fine quantity STRICTLY
  POSITIVE at the per-cube gauge family of §4 (`fine_price_pos_at_UfineStar`) — so the fine
  hypothesis is NOT algebraically forced, which is what it is at `starDatum`;
* COARSE background `spikeU (torus t_c)` is the tree's own curved source-bearing witness;
* `Q` is not injective (`§5a`), `ker Q ≠ ⊥` (`§5b`), and the `ε`-coercivity holds with the same
  modulus `1/ε` as at the flat fine background (`§5c`, `§5d`);

the printed `C*Δ_k(U)C` is positive definite on `ℓ²(Λ̃)`.

**Every binder of `terminal_at_composed_carriers_generalFine` is discharged here except** the ones
listed in this theorem's own signature: the datum parameters `bc`, `eps`; the two curvature
parameters `t`, `t_c`; the bound `K` on `‖H₁‖` with its budget; and the test vector `w ≠ 0`.
In particular `Qext`, `T`, `S`, `hS`, `c₂`, `hc₂`, `hD2`, `δ`, `hδ0`, `hU`, `hH1`, `hT`, `hcard`,
`hδ`, `hstrict`, `hdvd0`, `hell2`, `hsmallU` and `hsmallFine` are all supplied. -/
theorem terminal_posDef_at_curved_fine_datum (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    {t tc : ℝ} (ht : 0 < t) (htpi : t < Real.pi)
    (htc : 0 < tc) (htc1 : tc ≤ 1)
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ‖solutionOperator (curvedFineDatum bc heps t)‖ ≤ K)
    (hfine : Real.sqrt 2 * t
      ≤ Real.sqrt ((2 : ℕ) : ℝ) / (2356 * (36 * Real.sqrt 2) * (K + 1) * ((2 : ℕ) : ℝ) ^ 3))
    (hcov : Real.sqrt 2 * tc ≤ 1 / 106688)
    (hsrc : curvedC bc heps t * tc ^ 2 < 1)
    (w : TildeFn witnessL 2) (hw : w ≠ 0) :
    0 < cdcFormTrue (curvedFineDatum bc heps t) bc
        (bondQext (JsuTwo (AdalyFormal.Balaban.CurvedContent.spikeU (torus tc))))
        ((curvedFineDatum bc heps t).Qstar
          (JsuTwo (AdalyFormal.Balaban.CurvedContent.spikeU (torus tc))))
        (AdalyFormal.Balaban.CurvedContent.spikeU (torus tc)) 2
        (dinvC (AdalyFormal.Balaban.CurvedContent.spikeU (torus tc)) 2) w := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have htcpi : tc < Real.pi := by linarith
  have htcpi' : tc ≤ Real.pi := le_of_lt htcpi
  have htc0 : (0 : ℝ) ≤ tc := le_of_lt htc
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  have htpi' : t ≤ Real.pi := le_of_lt htpi
  set D := curvedFineDatum bc heps t with hD
  set v : BondFnL2 witnessL := JsuTwo (AdalyFormal.Balaban.CurvedContent.spikeU (torus tc)) with hv
  have hvne : v ≠ 0 := AdalyFormal.Balaban.CurvedContent.JsuTwo_spike_ne_zero htc htcpi
  have hc₂ : 0 < ‖v‖ := AdalyFormal.Balaban.CurvedContent.norm_JsuTwo_spike_pos htc htcpi
  have hH1 : 0 < ‖solutionOperator D‖ :=
    AdalyFormal.DatumWitness.norm_solutionOperator_pos D v hvne
  have hT : 0 < ‖D.Qstar‖ := AdalyFormal.DatumWitness.norm_Qstar_pos D v hvne
  have hcard : 0 < Fintype.card (Bond witnessL) := Fintype.card_pos
  have hcardR : (0 : ℝ) < (Fintype.card (Bond witnessL) : ℝ) := by exact_mod_cast hcard
  have hN : (0 : ℝ) < Real.sqrt (2 * (Fintype.card (Bond witnessL))) :=
    Real.sqrt_pos.mpr (by linarith)
  have hσ : (0 : ℝ) < rawSigmaZero 2 ^ 2 := by
    have := rawSigmaZero_pos (by norm_num : 0 < 2)
    positivity
  have hsmallU := hsmallU_at_coarse_spike htc0 htcpi' hcov
  have hsmallFine := hsmallFine_at_UfineStar bc heps ht0 htpi' K hK0 hK hfine
  have hJle : ‖v‖ ≤ AdalyFormal.Balaban.CurvedContent.spikeK * tc :=
    AdalyFormal.Balaban.CurvedContent.norm_JsuTwo_spike_le htc0 htcpi'
  have hden : (0 : ℝ) < 1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2
      * ‖solutionOperator D‖ * ‖v‖
      * (‖D.Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL)))) := by positivity
  have hblock : (0 : ℝ) ≤ 1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2
      * ‖solutionOperator D‖
      * (‖D.Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL)))) := by positivity
  have hδ : tc < 1 / (1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2
      * ‖solutionOperator D‖ * ‖v‖
      * (‖D.Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL))))) := by
    rw [lt_div_iff₀ hden]
    have hkey : ‖v‖ * tc ≤ (AdalyFormal.Balaban.CurvedContent.spikeK * tc) * tc :=
      mul_le_mul_of_nonneg_right hJle htc0
    have hexp : tc * (1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2
        * ‖solutionOperator D‖ * ‖v‖
        * (‖D.Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL)))))
        = (1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2 * ‖solutionOperator D‖
            * (‖D.Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL)))))
          * (‖v‖ * tc) := by ring
    have hstar : curvedC bc heps t * tc ^ 2
        = (1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2 * ‖solutionOperator D‖
            * (‖D.Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL)))))
          * ((AdalyFormal.Balaban.CurvedContent.spikeK * tc) * tc) := by
      unfold curvedC; rw [← hD]; ring
    rw [hexp]
    calc (1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2 * ‖solutionOperator D‖
            * (‖D.Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL))))) * (‖v‖ * tc)
        ≤ (1370001600 * ((2 : ℕ) : ℝ) ^ 6 * rawSigmaZero 2 ^ 2 * ‖solutionOperator D‖
            * (‖D.Qstar‖ * Real.sqrt (2 * (Fintype.card (Bond witnessL)))))
          * ((AdalyFormal.Balaban.CurvedContent.spikeK * tc) * tc) :=
          mul_le_mul_of_nonneg_left hkey hblock
      _ = curvedC bc heps t * tc ^ 2 := hstar.symm
      _ < 1 := hsrc
  exact AdalyFormal.TerminalBinder.terminal_at_composed_carriers_generalFine starScale
    (UfineStar t) (le_refl 2) AdalyFormal.Balaban.CurvedContent.witnessL_strict
    AdalyFormal.Balaban.CurvedContent.witnessL_dvd
    (AdalyFormal.Balaban.CurvedContent.spikeU (torus tc)) hsmallU bc heps hsmallFine
    (bondQext v) D.Qstar _ (AdalyFormal.DatumWitness.isSourceOperator_Qstar D v)
    ‖v‖ hc₂ (AdalyFormal.Balaban.TerminalAssembly.assemblyDatum_hD2 v)
    tc htc0 (AdalyFormal.Balaban.CurvedContent.linkDev_spike_torus htc0 htcpi')
    hH1 hT hcard hδ w hw

/-! ## §7 — CLOSING THE `‖H₁‖` BINDER: A LIFT WHOSE NORM DOES NOT MOVE WITH THE CURVATURE

§6c leaves one hypothesis that is not a free parameter: `hK : ‖H₁‖ ≤ K` together with a budget on
`t` that shrinks as `K` grows.  The tree's only route to such a `K` is
`TerminalBinder.norm_H1_le_of_rightInverse_bound`, which needs a right inverse of
`composedQ starScale (U*_fine)` — an object that MOVES with `t`, so a `K` obtained that way is
`t`-dependent and the budget could in principle be unsatisfiable.

§7 removes that possibility.  `RegularUQChain.coarseDriftEnergy_le` (REUSED) prices the whole
`Q`-drift at the operator level, `‖Q(1) − Q(U)‖ ≤ (8/√ℓ)·α₁(U)`; a Neumann step then turns ONE
right inverse of the FLAT `Q` into a right inverse of the CURVED `Q` with norm at most twice as
large, uniformly in `t` on the whole window.  `K` is then a fixed real, and §7f is an unconditional
existence statement with no hypothesis about `‖H₁‖` at all. -/

/-- **§7a — THE `Q`-DRIFT AT THE OPERATOR LEVEL.**  `‖Q(1)A − Q(U)A‖ ≤ (8/√ℓ)·α₁(U)·‖A‖`, the
`L²`-aggregated `[QCHAIN-SENS]` bound (`RegularUQChain.coarseDriftEnergy_le`, `C_Q = 8/√ℓ`) carried
across the two isometric identifications that `composedQ` is built from. -/
theorem norm_composedQ_sub_flat_le {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration SU2 L) (A : BondFnL2 L) :
    ‖composedQ h (trivialU L) A - composedQ h Ufine A‖
      ≤ (8 / Real.sqrt (ell : ℝ)) * frobSupBond Ufine * ‖A‖ := by
  have hell : 0 < ell := AdalyFormal.HrawCarriers.ell_pos_of_scale h
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hsq : (0 : ℝ) < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr hellR
  have hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1) := AdalyFormal.HrawCarriers.dvd_of_scale h
  have hα0 : (0 : ℝ) ≤ frobSupBond Ufine := frobSupBond_nonneg Ufine
  -- the two carriers are identified isometrically, so the difference may be measured upstairs
  have hiso : ‖composedQ h (trivialU L) A - composedQ h Ufine A‖
      = ‖(AdalyFormal.Balaban.BridgeInverse.qCLM (trivialU L) ell A
          - AdalyFormal.Balaban.BridgeInverse.qCLM Ufine ell A)‖ := by
    rw [show composedQ h (trivialU L) A - composedQ h Ufine A
        = AdalyFormal.HrawCarriers.coarseFnL2Equiv h
            (AdalyFormal.Balaban.BridgeInverse.qCLM (trivialU L) ell A
              - AdalyFormal.Balaban.BridgeInverse.qCLM Ufine ell A) by
      rw [map_sub]; rfl]
    exact AdalyFormal.HrawCarriers.norm_coarseFnL2Equiv h _
  -- the bond energy of `A` IS `‖A‖²`
  have hbe : AdalyFormal.Balaban.RegularUPerturbation.bondEnergy (WithLp.ofLp A) = ‖A‖ ^ 2 := by
    have h1 : ‖(WithLp.toLp 2 (WithLp.ofLp A) : BondFnL2 L)‖
        = Real.sqrt (AdalyFormal.Balaban.RegularUPerturbation.bondEnergy (WithLp.ofLp A)) :=
      AdalyFormal.MechEdges.G16.norm_bondFnL2 (WithLp.ofLp A)
    have h2 : (WithLp.toLp 2 (WithLp.ofLp A) : BondFnL2 L) = A := rfl
    rw [h2] at h1
    have h3 : (0 : ℝ) ≤ AdalyFormal.Balaban.RegularUPerturbation.bondEnergy (WithLp.ofLp A) :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    rw [h1, Real.sq_sqrt h3]
  -- the aggregated drift bound, in the sqrt form
  have hsum : ∑ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L ell,
      ‖WithLp.ofLp (AdalyFormal.Balaban.BridgeInverse.qCLM (trivialU L) ell A
          - AdalyFormal.Balaban.BridgeInverse.qCLM Ufine ell A) b‖ ^ 2
      ≤ (64 / (ell : ℝ)) * frobSupBond Ufine ^ 2 * ‖A‖ ^ 2 := by
    have hb := AdalyFormal.Balaban.RegularUQChain.coarseDriftEnergy_le Ufine hell hdvd
      (WithLp.ofLp A)
    rw [hbe] at hb
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun b _ => ?_))) hb
    rfl
  rw [hiso, AdalyFormal.MechEdges.G16.pilp_norm_eq_sqrt_sum]
  have hrhs : (8 / Real.sqrt (ell : ℝ)) * frobSupBond Ufine * ‖A‖
      = Real.sqrt ((64 / (ell : ℝ)) * frobSupBond Ufine ^ 2 * ‖A‖ ^ 2) := by
    rw [show (64 / (ell : ℝ)) * frobSupBond Ufine ^ 2 * ‖A‖ ^ 2
        = ((8 / Real.sqrt (ell : ℝ)) * frobSupBond Ufine * ‖A‖) ^ 2 by
      field_simp
      rw [Real.sq_sqrt (le_of_lt hellR)]
      ring]
    exact (Real.sqrt_sq (by positivity)).symm
  rw [hrhs]
  exact Real.sqrt_le_sqrt hsum

/-- **§7b — A NEUMANN STEP: ONE FLAT LIFT GIVES A CURVED LIFT OF AT MOST TWICE THE NORM.**
If `R₀` is a right inverse of the FLAT `Q` and the drift `(8/√ℓ)·α₁(U_fine)·‖R₀‖ ≤ 1/2`, then
`Q(U_fine)` has a right inverse of norm `≤ 2‖R₀‖`.  The bound does not mention `U_fine` except
through `α₁`, so it is uniform on the whole smallness window. -/
theorem exists_rightInverse_norm_le {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration SU2 L)
    (R₀ : BondFnL2 L' →L[ℝ] BondFnL2 L)
    (hR₀ : ∀ B : BondFnL2 L', composedQ h (trivialU L) (R₀ B) = B)
    (hsmall : (8 / Real.sqrt (ell : ℝ)) * frobSupBond Ufine * ‖R₀‖ ≤ 1 / 2) :
    ∃ Rq : BondFnL2 L' →L[ℝ] BondFnL2 L,
      (∀ B : BondFnL2 L', composedQ h Ufine (Rq B) = B) ∧ ‖Rq‖ ≤ 2 * ‖R₀‖ := by
  classical
  set M : BondFnL2 L' →L[ℝ] BondFnL2 L' := (composedQ h Ufine).comp R₀ with hM
  have hkey : ∀ B : BondFnL2 L', ‖B‖ ≤ 2 * ‖M B‖ := by
    intro B
    have h1 : ‖B - M B‖ ≤ (8 / Real.sqrt (ell : ℝ)) * frobSupBond Ufine * ‖R₀ B‖ := by
      have := norm_composedQ_sub_flat_le h Ufine (R₀ B)
      rwa [hR₀ B] at this
    have h2 : ‖R₀ B‖ ≤ ‖R₀‖ * ‖B‖ := R₀.le_opNorm B
    have hc0 : (0 : ℝ) ≤ (8 / Real.sqrt (ell : ℝ)) * frobSupBond Ufine := by
      have : (0 : ℝ) ≤ frobSupBond Ufine := frobSupBond_nonneg Ufine
      positivity
    have h3 : ‖B - M B‖ ≤ ((8 / Real.sqrt (ell : ℝ)) * frobSupBond Ufine * ‖R₀‖) * ‖B‖ := by
      calc ‖B - M B‖ ≤ (8 / Real.sqrt (ell : ℝ)) * frobSupBond Ufine * ‖R₀ B‖ := h1
        _ ≤ (8 / Real.sqrt (ell : ℝ)) * frobSupBond Ufine * (‖R₀‖ * ‖B‖) :=
            mul_le_mul_of_nonneg_left h2 hc0
        _ = ((8 / Real.sqrt (ell : ℝ)) * frobSupBond Ufine * ‖R₀‖) * ‖B‖ := by ring
    have h4 : ‖B - M B‖ ≤ (1 / 2) * ‖B‖ :=
      le_trans h3 (mul_le_mul_of_nonneg_right hsmall (norm_nonneg B))
    have h5 : ‖B‖ ≤ ‖M B‖ + ‖B - M B‖ := by
      have := norm_add_le (M B) (B - M B)
      simpa using this
    linarith
  have hinj : Function.Injective M := by
    intro x y hxy
    have h0 : M (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have := hkey (x - y)
    rw [h0, norm_zero, mul_zero] at this
    have hz : x - y = 0 := norm_le_zero_iff.mp this
    exact sub_eq_zero.mp hz
  have hsurj : Function.Surjective M := by
    have := (LinearMap.injective_iff_surjective
      (K := ℝ) (V := BondFnL2 L') (f := (M : BondFnL2 L' →ₗ[ℝ] BondFnL2 L'))).mp hinj
    exact this
  set e : BondFnL2 L' ≃ₗ[ℝ] BondFnL2 L' :=
    LinearEquiv.ofBijective (M : BondFnL2 L' →ₗ[ℝ] BondFnL2 L') ⟨hinj, hsurj⟩ with he
  refine ⟨R₀.comp (LinearMap.toContinuousLinearMap (e.symm : BondFnL2 L' →ₗ[ℝ] BondFnL2 L')), ?_, ?_⟩
  · intro B
    show composedQ h Ufine (R₀ (e.symm B)) = B
    have : M (e.symm B) = B := by
      show (e : BondFnL2 L' →ₗ[ℝ] BondFnL2 L') (e.symm B) = B
      simp
    exact this
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun B => ?_)
    show ‖R₀ (e.symm B)‖ ≤ 2 * ‖R₀‖ * ‖B‖
    have hMe : M (e.symm B) = B := by
      show (e : BondFnL2 L' →ₗ[ℝ] BondFnL2 L') (e.symm B) = B
      simp
    have h1 : ‖e.symm B‖ ≤ 2 * ‖B‖ := by
      have := hkey (e.symm B); rwa [hMe] at this
    calc ‖R₀ (e.symm B)‖ ≤ ‖R₀‖ * ‖e.symm B‖ := R₀.le_opNorm _
      _ ≤ ‖R₀‖ * (2 * ‖B‖) :=
          mul_le_mul_of_nonneg_left h1 (ContinuousLinearMap.opNorm_nonneg R₀)
      _ = 2 * ‖R₀‖ * ‖B‖ := by ring

/-- **§7c — A FLAT LIFT EXISTS** (`TerminalBinder.exists_continuous_rightInverse` at the flat fine
background).  Its norm is a fixed real number, and every constant below is expressed in it. -/
theorem exists_flat_rightInverse {ell : ℕ} (h : ScaleQuotient L ell L') :
    ∃ R₀ : BondFnL2 L' →L[ℝ] BondFnL2 L,
      ∀ B : BondFnL2 L', composedQ h (trivialU L) (R₀ B) = B :=
  AdalyFormal.TerminalBinder.exists_continuous_rightInverse h (trivialU L)

/-- **§7d — `‖H₁‖ ≤ √(4‖R₀‖² + 1)` AT THE CURVED FINE BACKGROUND**, with `R₀` the FLAT lift: the
bound is uniform over the whole curvature window and does not mention `t`.  This is the row that
turns §6c's `hK` from a hypothesis into a theorem. -/
theorem norm_H1_le_uniform (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps) {t : ℝ}
    (R₀ : BondFnL2 witnessL →L[ℝ] BondFnL2 fineL)
    (Rq : BondFnL2 witnessL →L[ℝ] BondFnL2 fineL)
    (hRq : ∀ B : BondFnL2 witnessL, composedQ starScale (UfineStar t) (Rq B) = B)
    (hnorm : ‖Rq‖ ≤ 2 * ‖R₀‖)
    (hbig : ‖(curlCovariantCLM_L2 (UfineStar t)).comp Rq‖ ^ 2 + bc.a ≤ eps) :
    ‖solutionOperator (curvedFineDatum bc heps t)‖ ≤ Real.sqrt (4 * ‖R₀‖ ^ 2 + 1) := by
  have h1 := AdalyFormal.TerminalBinder.norm_H1_le_of_rightInverse_bound starScale (UfineStar t)
    heps (le_of_lt bc.a_pos) Rq hRq hbig
  refine le_trans h1 (Real.sqrt_le_sqrt ?_)
  have h2 : (0 : ℝ) ≤ ‖Rq‖ := ContinuousLinearMap.opNorm_nonneg Rq
  have h3 : (0 : ℝ) ≤ ‖R₀‖ := ContinuousLinearMap.opNorm_nonneg R₀
  nlinarith [hnorm, h2, h3]

/-- **§7e — THE COARSE WINDOW AT THE TIGHTENED CLASS**, in closed form: for every `C ≥ 0` there is a
`t_c ∈ (0,1]` with `√2·t_c ≤ 1/106688` (the factor-`2` tighter coarse class the general-fine chain
demands) and `C·t_c² < 1`.  Witness `t_c = min 1 (min (1/160032) (1/(1+C)))`;
`3/(2·160032) = 1/106688` is the whole of the first estimate, with `√2 ≤ 3/2`. -/
theorem coarse_window_tight (C : ℝ) (hC : 0 ≤ C) :
    ∃ tc : ℝ, 0 < tc ∧ tc ≤ 1 ∧ Real.sqrt 2 * tc ≤ 1 / 106688 ∧ C * tc ^ 2 < 1 := by
  have hCpos : (0 : ℝ) < 1 + C := by linarith
  refine ⟨min 1 (min (1 / 160032) (1 / (1 + C))), ?_, min_le_left _ _, ?_, ?_⟩
  · exact lt_min one_pos (lt_min (by norm_num) (by positivity))
  · have h1 : min 1 (min (1 / 160032) (1 / (1 + C))) ≤ 1 / 160032 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have h0 : 0 < min 1 (min (1 / 160032) (1 / (1 + C))) :=
      lt_min one_pos (lt_min (by norm_num) (by positivity))
    nlinarith [h1, h2, h0, Real.sqrt_nonneg 2]
  · set tc := min 1 (min (1 / 160032) (1 / (1 + C))) with hdef
    have h0 : 0 < tc := lt_min one_pos (lt_min (by norm_num) (by positivity))
    have hle1 : tc ≤ 1 := min_le_left _ _
    have hleC : tc ≤ 1 / (1 + C) := le_trans (min_le_right _ _) (min_le_right _ _)
    have hmul : tc * (1 + C) ≤ 1 := by rw [← le_div_iff₀ hCpos]; exact hleC
    nlinarith [h0, hle1, hmul, hC]

/-! ## §8 — THE UNCONDITIONAL INSTANCE: BOTH SCALES CURVED, NO SURVIVING ANALYTIC BINDER

Everything §6c left as a hypothesis is now produced: `t` and `t_c` from the two windows, `eps` from
the datum's own free regulator, and `K` from §7d — which is a fixed real, built from the norm of ONE
right inverse of the FLAT `Q` and therefore not moving with the curvature.  The only remaining
binders are `bc : BaseConstant` (the printed constant `a`, a parameter of the statement being
proved, not an analytic smallness) and the test vector. -/

/-- **THE END-TO-END CURVED-BOTH-SCALES INSTANCE, WITH NO SMALLNESS HYPOTHESIS LEFT TO SUPPLY.**

For every `BaseConstant` there are `t`, `eps`, `t_c` such that, at the datum
`feedDatumGen starScale (U*_fine t) heps _` on the `8³ → 4³` pair:

1. the FINE background is curved on the fine torus's own plaquette, and `α₁(U*_fine) > 0`;
2. the priced fine quantity at the per-cube gauge family of §4 is STRICTLY POSITIVE for every
   `s` — the fine hypothesis is NOT algebraically forced, which is exactly what it is at
   `DatumWitness.starDatum` (`FineDrift.fine_binder_forced_at_flat_fine_background`);
3. the COARSE background is the tree's curved source-bearing spike, also with holonomy `≠ 1`;
4. `Q` is not injective at the datum — the constraint fibres are not points;
5. `⟨B̃, C*Δ_k(U)C B̃⟩ > 0` for every `B̃ ≠ 0`.

Clause 5's proof discharges every binder of
`TerminalBinder.terminal_at_composed_carriers_generalFine`. -/
theorem exists_curved_both_scales_instance (bc : BaseConstant) :
    ∃ (t eps tc : ℝ) (heps : 0 < eps),
      0 < t ∧ t < Real.pi ∧ 0 < tc ∧ tc ≤ 1
      ∧ holonomyElem (UfineStar t) finePlaquette ≠ 1
      ∧ 0 < frobSupBond (UfineStar t)
      ∧ (∀ s : ℝ, 0 < rawErrorCoeff 2
          (periodicGaugeTransform (gluedGauge fSlab (fGauge s)) (UfineStar t)))
      ∧ holonomyElem (AdalyFormal.Balaban.CurvedContent.spikeU (torus tc))
          AdalyFormal.Balaban.CovariantOperators.witnessPlaquette ≠ 1
      ∧ ¬ Function.Injective (curvedFineDatum bc heps t).Q
      ∧ (∀ w : TildeFn witnessL 2, w ≠ 0 →
          0 < cdcFormTrue (curvedFineDatum bc heps t) bc
              (bondQext (JsuTwo (AdalyFormal.Balaban.CurvedContent.spikeU (torus tc))))
              ((curvedFineDatum bc heps t).Qstar
                (JsuTwo (AdalyFormal.Balaban.CurvedContent.spikeU (torus tc))))
              (AdalyFormal.Balaban.CurvedContent.spikeU (torus tc)) 2
              (dinvC (AdalyFormal.Balaban.CurvedContent.spikeU (torus tc)) 2) w) := by
  classical
  obtain ⟨R₀, hR₀⟩ := exists_flat_rightInverse (L := fineL) (L' := witnessL) starScale
  set r : ℝ := ‖R₀‖ with hr
  have hr0 : (0 : ℝ) ≤ r := ContinuousLinearMap.opNorm_nonneg R₀
  set K : ℝ := Real.sqrt (4 * r ^ 2 + 1) with hKdef
  have hK0 : (0 : ℝ) ≤ K := Real.sqrt_nonneg _
  set D : ℝ := 2356 * (36 * Real.sqrt 2) * (K + 1) * ((2 : ℕ) : ℝ) ^ 3 with hD
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hDpos : (0 : ℝ) < D := by rw [hD]; positivity
  set t : ℝ := min 1 (min (1 / (2 * (8 * r + 1))) (1 / D)) with ht
  have h8r : (0 : ℝ) < 2 * (8 * r + 1) := by linarith
  have ht0 : 0 < t := lt_min one_pos (lt_min (by positivity) (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htD : t ≤ 1 / D := le_trans (min_le_right _ _) (min_le_right _ _)
  have htr : t ≤ 1 / (2 * (8 * r + 1)) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have htpi : t < Real.pi := by linarith
  have htpi' : t ≤ Real.pi := le_of_lt htpi
  have ht0' : (0 : ℝ) ≤ t := le_of_lt ht0
  -- the drift condition of §7b, at ell = 2
  have hdrift : (8 / Real.sqrt ((2 : ℕ) : ℝ)) * frobSupBond (UfineStar t) * r ≤ 1 / 2 := by
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    have hfb : frobSupBond (UfineStar t) ≤ Real.sqrt 2 * t :=
      frobSupBond_UfineStar_le ht0' htpi'
    have hstep : (8 / Real.sqrt ((2 : ℕ) : ℝ)) * frobSupBond (UfineStar t) * r
        ≤ (8 / Real.sqrt 2) * (Real.sqrt 2 * t) * r := by
      rw [hcast]
      have hc : (0 : ℝ) ≤ 8 / Real.sqrt 2 := by positivity
      have h1 : frobSupBond (UfineStar t) * r ≤ (Real.sqrt 2 * t) * r :=
        mul_le_mul_of_nonneg_right hfb hr0
      calc (8 / Real.sqrt 2) * frobSupBond (UfineStar t) * r
          = (8 / Real.sqrt 2) * (frobSupBond (UfineStar t) * r) := by ring
        _ ≤ (8 / Real.sqrt 2) * ((Real.sqrt 2 * t) * r) := mul_le_mul_of_nonneg_left h1 hc
        _ = (8 / Real.sqrt 2) * (Real.sqrt 2 * t) * r := by ring
    have heq : (8 / Real.sqrt 2) * (Real.sqrt 2 * t) * r = 8 * t * r := by
      field_simp
    rw [heq] at hstep
    have hfin : 8 * t * r ≤ 1 / 2 := by
      have h1 : t * (2 * (8 * r + 1)) ≤ 1 := by rw [← le_div_iff₀ h8r]; exact htr
      nlinarith [h1, hr0, ht0']
    linarith
  obtain ⟨Rq, hRq, hRqn⟩ :=
    exists_rightInverse_norm_le starScale (UfineStar t) R₀ hR₀ hdrift
  -- the regulator, chosen large enough for §7d's collapse
  set eps : ℝ := ‖(curlCovariantCLM_L2 (UfineStar t)).comp Rq‖ ^ 2 + bc.a with heq
  have heps : 0 < eps := by
    have := bc.a_pos
    have h2 : (0 : ℝ) ≤ ‖(curlCovariantCLM_L2 (UfineStar t)).comp Rq‖ ^ 2 := sq_nonneg _
    rw [heq]; linarith
  have hbig : ‖(curlCovariantCLM_L2 (UfineStar t)).comp Rq‖ ^ 2 + bc.a ≤ eps := le_of_eq heq.symm
  have hK : ‖solutionOperator (curvedFineDatum bc heps t)‖ ≤ K :=
    norm_H1_le_uniform bc heps R₀ Rq hRq hRqn hbig
  -- the fine budget
  have hfine2 : Real.sqrt 2 * t
      ≤ Real.sqrt ((2 : ℕ) : ℝ) / (2356 * (36 * Real.sqrt 2) * (K + 1) * ((2 : ℕ) : ℝ) ^ 3) := by
    have hcast : Real.sqrt ((2 : ℕ) : ℝ) = Real.sqrt 2 := by norm_num
    rw [hcast, ← hD, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left htD (le_of_lt hs2)
  -- the coarse window
  obtain ⟨tc, htc0, htc1, hcov, hsrc⟩ := coarse_window_tight (curvedC bc heps t)
    (curvedC_nonneg bc heps t)
  have htcpi : tc < Real.pi := by linarith
  refine ⟨t, eps, tc, heps, ht0, htpi, htc0, htc1, (UfineStar_is_curved ht0 htpi).1,
    (UfineStar_is_curved ht0 htpi).2, ?_,
    (AdalyFormal.Balaban.CurvedContent.spike_is_curved htc0 htcpi).1,
    curvedFineDatum_Q_not_injective bc heps t, ?_⟩
  · intro s
    have := fine_price_pos_at_UfineStar (ell := 2) (by norm_num) (K := 1) one_pos s ht0 htpi
    rwa [one_mul] at this
  · intro w hw
    exact terminal_posDef_at_curved_fine_datum bc heps ht0 htpi htc0 htc1 K hK0 hK hfine2
      hcov hsrc w hw

end AdalyFormal.CurvedFine
