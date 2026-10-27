/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import HrawRNonVacuity

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.longLine false

/-!
# `HrawRCentreClass.lean` — THE ADDED HYPOTHESIS, MADE INTRINSIC

Lane `compute/hrawr_discharge/`.  Write scope: that directory only.  Never `lake build`.

`HrawRDischarge` §6 states the recomposed terminal theorem at a background PRESENTED as
`centralFlipConfig ε V` with `α₁(V)` small.  A presentation is not a class: a reader cannot check
"is my `U` of that form?" without being handed `ε` and `V`.

§10 removes the presentation.  Central flips are an INVOLUTIVE action
(`flipSign b * flipSign b = 1`, because `negI² = 1`), so

    { centralFlipConfig ε V : α₁(V) ≤ r }  =  { U : ∃ ε, α₁(centralFlipConfig ε U) ≤ r }

and the right-hand side is a property of `U` alone.  §10c states the terminal theorem with that
hypothesis and `U` itself in the conclusion.

**What the class IS, in words.**  `CentreNear r U` says every link of `U` is within `r` (in
Frobenius norm) of the CENTRE `{±1}` of `SU(2)` — the sign being chosen independently at each bond.
It contains the ordinary smallness class (`ε = fun _ => false`) and strictly contains it
(`centerU ∈ CentreNear 0` while `α₁(centerU) = 2√2`).

**Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.**
-/

namespace AdalyFormal.HrawRDischarge

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.AlphaAnalyticity (centerU negOneElem frobSupBond_centerU)
open AdalyFormal.Balaban.VariationalProjectorH1 (solutionOperator)
open AdalyFormal.Balaban.ConstantA (BaseConstant)
open AdalyFormal.Balaban.ConstructCDC (TildeFn)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)
open AdalyFormal.Balaban.DeltaKWiring (IsSourceOperator cdcFormTrue)
open AdalyFormal.Balaban.TerminalAssembly (sharpFloorConst)
open AdalyFormal.Balaban.DeltaAlpha0 (PrintedCubeClassI)
open AdalyFormal.Balaban.RecomposeSum (gammaSum CubesRefine)
open AdalyFormal.MechEdges.G16 (rawSigmaZero)
open AdalyFormal.DatumWitness (fineL starDatum)
open AdalyFormal.HoleHunt.CenterBlindness (negI flipSign centralFlipConfig)

/-! ## §10 — CENTRAL FLIPS ARE AN INVOLUTION -/

/-- `negI * negI = 1` in `SU(2)`: `(−I)(−I) = I`. -/
theorem negI_mul_self : negI * negI = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  apply Subtype.ext
  show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * (-1) = 1
  simp

/-- `flipSign b * flipSign b = 1` for both values of `b`. -/
theorem flipSign_mul_self (b : Bool) :
    flipSign b * flipSign b = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  unfold flipSign
  cases b with
  | false => simp
  | true => simpa using negI_mul_self

/-- **THE ACTION IS INVOLUTIVE**, bond by bond, at every configuration. -/
theorem centralFlipConfig_involutive {L : PeriodicLatticeExtent} (ε : Bond L → Bool)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    centralFlipConfig ε (centralFlipConfig ε U) = U := by
  funext b
  show flipSign (ε b) * (flipSign (ε b) * U b) = U b
  rw [← mul_assoc, flipSign_mul_self, one_mul]

/-- The unflipped configuration is itself. -/
theorem centralFlipConfig_false {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    centralFlipConfig (fun _ => false) U = U := by
  funext b
  show flipSign false * U b = U b
  unfold flipSign
  simp

/-! ## §10a — THE CLASS -/

/-- **`CentreNear r U`** — every link of `U` is within `r` of the centre `{±1}`, the sign chosen
independently at each bond.  Equivalently: some central flip of `U` lies in the ordinary smallness
class of radius `r`. -/
def CentreNear {L : PeriodicLatticeExtent} (r : ℝ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) : Prop :=
  ∃ ε : Bond L → Bool, frobSupBond (centralFlipConfig ε U) ≤ r

/-- **THE ORDINARY SMALLNESS CLASS IS CONTAINED IN IT** — take the empty flip. -/
theorem centreNear_of_frobSupBond {L : PeriodicLatticeExtent} (r : ℝ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (h : frobSupBond U ≤ r) : CentreNear r U :=
  ⟨fun _ => false, by rw [centralFlipConfig_false]; exact h⟩

/-- **AND THE CONTAINMENT IS STRICT, WITNESSED BY `U ≡ −1`.**  `centerU ∈ CentreNear 0` — its
all-links flip is the flat configuration, whose `α₁` is `0` — while `α₁(centerU) = 2√2`, the
LARGEST value the quantity takes on `SU(2)`.  So the class §10c uses is not the smallness class
under another name. -/
theorem centreNear_strict {L : PeriodicLatticeExtent} :
    CentreNear 0 (centerU L) ∧ frobSupBond (centerU L) = 2 * Real.sqrt 2 := by
  refine ⟨⟨fun _ => true, ?_⟩, frobSupBond_centerU⟩
  have hflat : centralFlipConfig (fun _ => true) (centerU L) = trivialU L := by
    funext b
    show flipSign true * negOneElem = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    show negI * negOneElem = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    have hne : (negOneElem : Matrix.specialUnitaryGroup (Fin 2) ℂ) = negI := Subtype.ext rfl
    rw [hne]
    exact negI_mul_self
  rw [hflat, AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU L]

/-! ## §10b — `hrawR` UNDER THE INTRINSIC CLASS -/

/-- **`hrawR` AT `D*` FOR EVERY `U` IN THE CLASS**, with the drift priced by the FLIPPED
representative — a number bounded by `r`, not by `α₁(U)`. -/
theorem starDatum_hrawR_centreNear (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (ε : Bond witnessL → Bool) :
    AdalyFormal.TerminalBinder.OnMinimizerRange (starDatum bc heps)
      (AdalyFormal.TerminalBinder.HrawAt (starDatum bc heps) U
        (AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2 (trivialU fineL))
        (rawSigmaZero 2)
        (4 * Real.sqrt 2 * frobSupBond (centralFlipConfig ε U))) := by
  have h := starDatum_hrawR_centerBlind bc heps ε (centralFlipConfig ε U)
  rwa [centralFlipConfig_involutive ε U] at h

/-! ## §10c — THE RECOMPOSED TERMINAL THEOREM WITH AN INTRINSIC HYPOTHESIS

Identical to `HrawRDischarge.terminal_sum_at_star_datum` except that the background is `U` itself,
the added hypothesis is `CentreNear (1/(13336·ℓ³)) U` — a property of `U` alone — and the floor
constant is priced by the flipped representative's `α₁`, which the hypothesis bounds. -/
theorem terminal_sum_at_star_datum_centreNear
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (ε : Bond witnessL → Bool)
    (hcn : frobSupBond (centralFlipConfig ε U) ≤ 1 / (13336 * (((2 : ℕ)) : ℝ) ^ 3))
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hα0 : 0 ≤ α₀) (hthr : c * M * α₀ < 1 / (1120 * (((2 : ℕ)) : ℝ) ^ 3))
    (𝒞src : Set (Set (Bond witnessL)))
    (hprinted : PrintedCubeClassI c M α₀ η Lj U 𝒞src)
    (hgeom : CubesRefine AdalyFormal.Balaban.CurvedContent.witnessL_dvd
      (Finset.univ : Finset (AdalyFormal.Balaban.LocalizedEstimates.CSite witnessL 2))
      (fun z => ({z} : Finset (AdalyFormal.Balaban.LocalizedEstimates.CSite witnessL 2))) 𝒞src)
    (Qext : BondFnL2 witnessL → BondFnL2 witnessL) (J : BondFnL2 fineL)
    (S : BondFnL2 witnessL →L[ℝ] BondFnL2 witnessL)
    (hS : IsSourceOperator (starDatum bc heps) Qext J S) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hD2 : ∀ B : BondFnL2 witnessL, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (R : ℝ) (hJbound : ‖J‖ ≤ R)
    (hRthr : 2 * ‖solutionOperator (starDatum bc heps)‖ * c₂ * R
      < sharpFloorConst (gammaSum 2) (4 * Real.sqrt 2 * frobSupBond (centralFlipConfig ε U))
          (rawSigmaZero 2))
    (w : TildeFn witnessL 2) (hw : w ≠ 0) :
    0 < cdcFormTrue (starDatum bc heps) bc Qext J U 2 (dinvC U 2) w := by
  have hinv : centralFlipConfig ε (centralFlipConfig ε U) = U := centralFlipConfig_involutive ε U
  have hmain := terminal_sum_at_star_datum bc heps ε (centralFlipConfig ε U) hcn c M α₀ η Lj
    hη hηne hLj hc hM hα0 hthr 𝒞src (by rw [hinv]; exact hprinted) hgeom Qext J S hS c₂ hc₂ hD2
    R hJbound hRthr w hw
  rwa [hinv] at hmain

/-- **AND THE INTRINSIC FORM**, with the flip existentially quantified exactly as `CentreNear`
states it.  The `ε` is extracted, not supplied by the caller. -/
theorem terminal_sum_at_star_datum_of_centreNear
    (bc : BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (hcn : CentreNear (1 / (13336 * (((2 : ℕ)) : ℝ) ^ 3)) U)
    (c M α₀ η Lj : ℝ) (hη : 0 ≤ η) (hηne : η ≠ 0) (hLj : 1 ≤ Lj) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hα0 : 0 ≤ α₀) (hthr : c * M * α₀ < 1 / (1120 * (((2 : ℕ)) : ℝ) ^ 3))
    (𝒞src : Set (Set (Bond witnessL)))
    (hprinted : PrintedCubeClassI c M α₀ η Lj U 𝒞src)
    (hgeom : CubesRefine AdalyFormal.Balaban.CurvedContent.witnessL_dvd
      (Finset.univ : Finset (AdalyFormal.Balaban.LocalizedEstimates.CSite witnessL 2))
      (fun z => ({z} : Finset (AdalyFormal.Balaban.LocalizedEstimates.CSite witnessL 2))) 𝒞src)
    (Qext : BondFnL2 witnessL → BondFnL2 witnessL) (J : BondFnL2 fineL)
    (S : BondFnL2 witnessL →L[ℝ] BondFnL2 witnessL)
    (hS : IsSourceOperator (starDatum bc heps) Qext J S) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hD2 : ∀ B : BondFnL2 witnessL, ‖Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (R : ℝ) (hJbound : ‖J‖ ≤ R)
    (hRthr : ∀ ε : Bond witnessL → Bool,
      2 * ‖solutionOperator (starDatum bc heps)‖ * c₂ * R
        < sharpFloorConst (gammaSum 2) (4 * Real.sqrt 2 * frobSupBond (centralFlipConfig ε U))
            (rawSigmaZero 2))
    (w : TildeFn witnessL 2) (hw : w ≠ 0) :
    0 < cdcFormTrue (starDatum bc heps) bc Qext J U 2 (dinvC U 2) w := by
  obtain ⟨ε, hε⟩ := hcn
  exact terminal_sum_at_star_datum_centreNear bc heps U ε hε c M α₀ η Lj hη hηne hLj hc hM hα0
    hthr 𝒞src hprinted hgeom Qext J S hS c₂ hc₂ hD2 R hJbound (hRthr ε) w hw

#print axioms negI_mul_self
#print axioms flipSign_mul_self
#print axioms centralFlipConfig_involutive
#print axioms centralFlipConfig_false
#print axioms CentreNear
#print axioms centreNear_of_frobSupBond
#print axioms centreNear_strict
#print axioms starDatum_hrawR_centreNear
#print axioms terminal_sum_at_star_datum_centreNear
#print axioms terminal_sum_at_star_datum_of_centreNear

end AdalyFormal.HrawRDischarge
