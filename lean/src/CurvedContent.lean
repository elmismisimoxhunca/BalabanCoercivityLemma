/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.SourceJ
import AdalyFormal.Balaban.AbelianBlockingRate
import SourceWiredJ
import SourceWiredComposed
import TerminalAssembly

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.style.longLine false

/-!
# `CurvedContent.lean` — THE CONTENT QUESTION: a curved, SOURCE-BEARING witness in BOTH smallness classes

Lane `compute/curved_witness/content/`.  Write scope: that directory only.  Never `lake build`.

## THE GAP THIS ANSWERS, QUOTED

`compute/terminal_assembly/stage/TerminalAssembly.lean` §11, verbatim:

> the SOURCE threshold `δ < 1/(1370001600·ℓ⁶·σ₀²·‖H₁‖·c₂·N)` is smaller than the COVARIANCE class
> `α₁ ≤ 1/(186·ℓ³)` by more than nine orders of magnitude at `ℓ = 3`, and the tree's curved witness
> `CovLemma24Witness.witU witT` was built to the SECOND of those, not the first.  **No configuration
> in the tree is proved to satisfy the first with a curvature that is nonzero.**

and `end_to_end_flat`'s own disclosure:

> `δ = 0` at `U = 1`, so `‖J(U)‖ ≤ 0` and **the source term contributes nothing**.

## WHAT WAS ALREADY IN PRINT (build discipline #2 — do not build what is in print)

Retrieval before construction, all already kernel-checked in `formal/`:

| already compiled | what it gives |
|---|---|
| `SourceJ.Jsource_witnessU_ne_zero` | `J ≠ 0` at `witnessU` — a SINGLE-LINK excitation on the `4³` torus |
| `DeltaPrime` §7 | the four exceptional plaquettes of that excitation, and their holonomies |
| `SuTwoLogExp` | `torus t = diag(e^{it},e^{-it})`, the `dg` toolkit, `cexp_sub` |
| `AbelianBlockingRate` | `frobNorm (torus φ − 1) = √(4(1−cos φ))`, `= √8·|sin(φ/2)|` |
| `TerminalAssembly` | `terminal_posDef_of_source_bound`, and the `assemblyDatum` witness family |

**So the tree already had `J ≠ 0` — but only at `witnessMElem`, whose `imHolonomy` is `!![0,−i;i,0]`:
a π-rotation, of ORDER ONE.**  The tree therefore held `J ≠ 0` at deviation `O(1)` and `J = 0` at
deviation `0`, and **nothing in between**.  That is exactly the gap: not "is there a curved
configuration", nor "is there a configuration with an active source", but *is there one that is
simultaneously curved, source-bearing, and SMALL ENOUGH FOR BOTH THRESHOLDS AT ONCE*.

## WHAT IS NEW HERE

§1–§2 generalise the tree's single-link scaffolding from the fixed element `witnessMElem` to an
ARBITRARY `g ∈ SU(2)` (`spikeU g`), so that the excitation can be taken small.  `spikeU
witnessMElem = witnessU` definitionally, so the tree's own witness is the `g = witnessMElem` member
and nothing is re-derived by a different route than the source.

§3–§5 evaluate the source at `g = torus t`:

    J(spikeU (torus t))(witnessY, 0)  =  4 · diag(sin t, −sin t),

an EQUALITY, hence `≠ 0` for every `0 < t < π`.  §6 evaluates both smallness classes at the SAME
`t`: `LinkDev t` and `frobSupBond = √(4(1−cos t)) ≤ √2·t`.  **Both classes are controlled by the one
parameter and both are LINEAR in it, while the curvature is `sin t` — also linear.**  Nothing scales
the wrong way; that is the whole content of the answer, and §7 makes it a theorem.

§8 composes: at `ℓ = 2` on the `4³` torus, with `v := J(U*)` so that the source operator is
`‖J‖²·I ≠ 0`, the terminal positivity holds AT a background that is curved and whose source term is
active.  §9 is the falsifiability battery.

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.
-/

namespace AdalyFormal.Balaban.CurvedContent

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL witnessY)
open AdalyFormal.Balaban.DeltaPrime (imHolonomy holonomyElem holonomyElemInv trivialU
  p3 p4 p3Site p4Site shift_p3Site_eq shift_p4Site_eq)
open AdalyFormal.Balaban.CovariantOperators (witnessU witnessMElem witnessPlaquette
  conjByAmbient conjByAmbient_apply SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHj (myWitnessPlaquette2)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack
  periodicLatticeShiftBack_shift)
open AdalyFormal.Balaban.SourceJ (piProj piProj_eq_self_of_trace_zero FnuMu DstarDir Jfield Jsource
  conjByAmbient_one_apply)
open AdalyFormal.Balaban.SuTwoLogExp (dg dg_sub dg_smul dg_trace dg_00 dg_01 dg_10 dg_11 dg_one
  dg_congr torus torus_zero coe_torus cexp_sub cexp_pos_form cexp_neg_form)
open AdalyFormal.Balaban.AbelianBlockingRate (torus_inv frobNorm_torus_sub_one
  sqrt_four_one_sub_cos)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.SourceWiredJ (EB JsuTwo norm_JsuTwo_le)
open AdalyFormal.Balaban.SourceWired (LinkDev)

/-- Local abbreviation for the ambient `2×2` complex matrices. -/
local notation "M₂" => Matrix (Fin 2) (Fin 2) ℂ

/-- Local abbreviation for `SU(2)`. -/
local notation "SU₂" => Matrix.specialUnitaryGroup (Fin 2) ℂ

/-! ## §1 — THE SINGLE-LINK SPIKE, AT AN ARBITRARY GROUP ELEMENT

`CovariantOperators.witnessU` is `fun e => if e = (witnessY,0) then witnessMElem else 1`, with the
excited element HARD-CODED.  `spikeU` is the same configuration with the element as a parameter.
Everything the tree proves about `witnessU`'s plaquette combinatorics depends only on the LATTICE
position of the excited bond, never on which element sits there — so all of it generalises, and
§2 carries it over verbatim. -/

/-- **THE SPIKE CONFIGURATION.**  `g` on the single bond `(witnessY, 0)` of the `4³` torus, the
identity on all `191` others. -/
noncomputable def spikeU (g : SU₂) : PeriodicLinkConfiguration SU₂ witnessL :=
  fun e => if e = (witnessY, (0 : Fin 3)) then g else 1

/-- **THE TREE'S OWN WITNESS IS THE `g = witnessMElem` MEMBER**, definitionally.  Stated so that
nothing below can be read as a parallel construction that merely resembles the tree's. -/
theorem spikeU_witnessMElem : spikeU witnessMElem = witnessU := rfl

/-- **THE FLAT CONFIGURATION IS THE `g = 1` MEMBER.**  The family therefore interpolates, inside a
single definition, between the two backgrounds the tree already has. -/
theorem spikeU_one : spikeU 1 = trivialU (L := witnessL) := by
  funext e
  unfold spikeU
  split_ifs <;> rfl

theorem spikeU_at_x_mu (g : SU₂) : spikeU g (witnessY, (0 : Fin 3)) = g := by
  unfold spikeU; rw [if_pos rfl]

theorem spikeU_at_y_nu (g : SU₂) :
    spikeU g (periodicLatticeShift witnessY 0, (1 : Fin 3)) = 1 := by
  unfold spikeU; rw [if_neg (by decide)]

theorem spikeU_at_x_nu (g : SU₂) : spikeU g (witnessY, (1 : Fin 3)) = 1 := by
  unfold spikeU; rw [if_neg (by decide)]

theorem spikeU_at_w_mu (g : SU₂) :
    spikeU g (periodicLatticeShift witnessY 1, (0 : Fin 3)) = 1 := by
  unfold spikeU; rw [if_neg (by decide)]

theorem spikeU_at_y_nu2 (g : SU₂) :
    spikeU g (periodicLatticeShift witnessY 0, (2 : Fin 3)) = 1 := by
  unfold spikeU; rw [if_neg (by decide)]

theorem spikeU_at_w_mu2 (g : SU₂) :
    spikeU g (periodicLatticeShift witnessY 2, (0 : Fin 3)) = 1 := by
  unfold spikeU; rw [if_neg (by decide)]

theorem spikeU_at_x_nu2 (g : SU₂) : spikeU g (witnessY, (2 : Fin 3)) = 1 := by
  unfold spikeU; rw [if_neg (by decide)]

theorem spikeU_at_p3Site_mu (g : SU₂) : spikeU g (p3Site, (0 : Fin 3)) = 1 := by
  unfold spikeU; rw [if_neg (by decide)]

theorem spikeU_at_p3Site_shift0_nu (g : SU₂) :
    spikeU g (periodicLatticeShift p3Site 0, (1 : Fin 3)) = 1 := by
  unfold spikeU; rw [if_neg (by decide)]

theorem spikeU_at_p3Site_nu (g : SU₂) : spikeU g (p3Site, (1 : Fin 3)) = 1 := by
  unfold spikeU; rw [if_neg (by decide)]

theorem spikeU_at_p4Site_mu (g : SU₂) : spikeU g (p4Site, (0 : Fin 3)) = 1 := by
  unfold spikeU; rw [if_neg (by decide)]

theorem spikeU_at_p4Site_shift0_nu (g : SU₂) :
    spikeU g (periodicLatticeShift p4Site 0, (2 : Fin 3)) = 1 := by
  unfold spikeU; rw [if_neg (by decide)]

theorem spikeU_at_p4Site_nu (g : SU₂) : spikeU g (p4Site, (2 : Fin 3)) = 1 := by
  unfold spikeU; rw [if_neg (by decide)]

/-! ## §2 — THE FOUR EXCEPTIONAL PLAQUETTES, AT AN ARBITRARY `g`

`DeltaPrime` §7 proves the holonomy of `witnessU` at each of the four plaquettes that read the
excited bond: `witnessMElem` at `witnessPlaquette`/`myWitnessPlaquette2` (the bond in "T1" slot),
`witnessMElem⁻¹` at `p3`/`p4` (the bond in the inverted "T3" slot).  The same four computations at
an arbitrary `g`. -/

theorem holonomy_spikeU_witnessPlaquette (g : SU₂) :
    holonomyElem (spikeU g) witnessPlaquette = g := by
  show spikeU g (witnessY, (0 : Fin 3)) *
      spikeU g (periodicLatticeShift witnessY 0, (1 : Fin 3)) *
      (spikeU g (periodicLatticeShift witnessY 1, (0 : Fin 3)))⁻¹ *
      (spikeU g (witnessY, (1 : Fin 3)))⁻¹ = g
  rw [spikeU_at_x_mu, spikeU_at_y_nu, spikeU_at_w_mu, spikeU_at_x_nu]
  simp

theorem holonomy_spikeU_myWitnessPlaquette2 (g : SU₂) :
    holonomyElem (spikeU g) myWitnessPlaquette2 = g := by
  show spikeU g (witnessY, (0 : Fin 3)) *
      spikeU g (periodicLatticeShift witnessY 0, (2 : Fin 3)) *
      (spikeU g (periodicLatticeShift witnessY 2, (0 : Fin 3)))⁻¹ *
      (spikeU g (witnessY, (2 : Fin 3)))⁻¹ = g
  rw [spikeU_at_x_mu, spikeU_at_y_nu2, spikeU_at_w_mu2, spikeU_at_x_nu2]
  simp

theorem holonomy_spikeU_p3 (g : SU₂) : holonomyElem (spikeU g) p3 = g⁻¹ := by
  show spikeU g (p3Site, (0 : Fin 3)) *
      spikeU g (periodicLatticeShift p3Site 0, (1 : Fin 3)) *
      (spikeU g (periodicLatticeShift p3Site 1, (0 : Fin 3)))⁻¹ *
      (spikeU g (p3Site, (1 : Fin 3)))⁻¹ = g⁻¹
  rw [spikeU_at_p3Site_mu, spikeU_at_p3Site_shift0_nu, shift_p3Site_eq, spikeU_at_x_mu,
    spikeU_at_p3Site_nu]
  simp

theorem holonomy_spikeU_p4 (g : SU₂) : holonomyElem (spikeU g) p4 = g⁻¹ := by
  show spikeU g (p4Site, (0 : Fin 3)) *
      spikeU g (periodicLatticeShift p4Site 0, (2 : Fin 3)) *
      (spikeU g (periodicLatticeShift p4Site 2, (0 : Fin 3)))⁻¹ *
      (spikeU g (p4Site, (2 : Fin 3)))⁻¹ = g⁻¹
  rw [spikeU_at_p4Site_mu, spikeU_at_p4Site_shift0_nu, shift_p4Site_eq, spikeU_at_x_mu,
    spikeU_at_p4Site_nu]
  simp

theorem holonomyElemInv_spikeU_witnessPlaquette (g : SU₂) :
    holonomyElemInv (spikeU g) witnessPlaquette = g⁻¹ := by
  unfold holonomyElemInv; rw [holonomy_spikeU_witnessPlaquette]

theorem holonomyElemInv_spikeU_myWitnessPlaquette2 (g : SU₂) :
    holonomyElemInv (spikeU g) myWitnessPlaquette2 = g⁻¹ := by
  unfold holonomyElemInv; rw [holonomy_spikeU_myWitnessPlaquette2]

theorem holonomyElemInv_spikeU_p3 (g : SU₂) : holonomyElemInv (spikeU g) p3 = g := by
  unfold holonomyElemInv; rw [holonomy_spikeU_p3, inv_inv]

theorem holonomyElemInv_spikeU_p4 (g : SU₂) : holonomyElemInv (spikeU g) p4 = g := by
  unfold holonomyElemInv; rw [holonomy_spikeU_p4, inv_inv]

/-! ## §3 — `Im ∂U` AT THE TORUS ELEMENT

`torus t = diag(e^{it}, e^{-it})`, so `(torus t)⁻¹ = torus (−t)` (`torus_inv`) and

    Im ∂U = (1/2i)·(torus t − torus (−t)) = diag(sin t, −sin t),

using `cexp_sub : e^{it} − e^{−it} = (2 sin t)·i`.  The value is real-diagonal and traceless, so
the projection `π` of (1.8) is a no-op on it — which is what lets §4 run. -/

/-- `dg` is additive — the one piece of the `dg` toolkit `SuTwoLogExp` does not carry (it has
`dg_sub`, `dg_mul`, `dg_smul`, but no `dg_add`).  Proved once here and reused. -/
theorem dg_add (a b c d : ℂ) : dg a b + dg c d = dg (a + c) (b + d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.diagonal]

/-- Cancelling the `i` in `(1/2i)·(x·i)`.  No `i² = −1` is needed: both sides clear to `x·i·2 =
x·(2i)`. -/
theorem inv_two_I_mul (x : ℂ) : (1 / (2 * Complex.I) : ℂ) * (x * Complex.I) = x / 2 := by
  field_simp

theorem coe_torus_dg (s : ℝ) : ((torus s : SU₂) : M₂)
    = dg (Complex.exp ((s : ℂ) * Complex.I)) (Complex.exp (-((s : ℂ) * Complex.I))) := rfl

theorem coe_torus_neg_dg (t : ℝ) : ((torus (-t) : SU₂) : M₂)
    = dg (Complex.exp (-((t : ℂ) * Complex.I))) (Complex.exp ((t : ℂ) * Complex.I)) := by
  rw [coe_torus_dg]
  refine dg_congr ?_ ?_ <;> congr 1 <;> push_cast <;> ring

/-- **THE CLOSED FORM OF `Im ∂U` AT A TORUS HOLONOMY.**  `(1/2i)(torus t − torus(−t)) =
diag(sin t, −sin t)`. -/
theorem imOfTorus (t : ℝ) :
    (1 / (2 * Complex.I) : ℂ) • (((torus t : SU₂) : M₂) - ((torus (-t) : SU₂) : M₂))
      = dg ((Real.sin t : ℝ) : ℂ) (-((Real.sin t : ℝ) : ℂ)) := by
  have h1 : Complex.exp ((t : ℂ) * Complex.I) - Complex.exp (-((t : ℂ) * Complex.I))
      = ((2 * Real.sin t : ℝ) : ℂ) * Complex.I := cexp_sub t
  have h2 : Complex.exp (-((t : ℂ) * Complex.I)) - Complex.exp ((t : ℂ) * Complex.I)
      = -(((2 * Real.sin t : ℝ) : ℂ) * Complex.I) := by rw [← h1]; ring
  rw [coe_torus_dg, coe_torus_neg_dg, dg_sub, h1, h2, dg_smul]
  refine dg_congr ?_ ?_
  · rw [inv_two_I_mul]; push_cast; ring
  · rw [show -(((2 * Real.sin t : ℝ) : ℂ) * Complex.I)
        = (-((2 * Real.sin t : ℝ) : ℂ)) * Complex.I by ring, inv_two_I_mul]
    push_cast; ring

/-- **`Im ∂U` AT THE SPIKE'S "T1" PLAQUETTES.** -/
theorem imHolonomy_spike_torus_wp (t : ℝ) :
    imHolonomy (spikeU (torus t)) witnessPlaquette
      = dg ((Real.sin t : ℝ) : ℂ) (-((Real.sin t : ℝ) : ℂ)) := by
  unfold imHolonomy
  rw [holonomy_spikeU_witnessPlaquette, holonomyElemInv_spikeU_witnessPlaquette, torus_inv]
  exact imOfTorus t

theorem imHolonomy_spike_torus_wp2 (t : ℝ) :
    imHolonomy (spikeU (torus t)) myWitnessPlaquette2
      = dg ((Real.sin t : ℝ) : ℂ) (-((Real.sin t : ℝ) : ℂ)) := by
  unfold imHolonomy
  rw [holonomy_spikeU_myWitnessPlaquette2, holonomyElemInv_spikeU_myWitnessPlaquette2, torus_inv]
  exact imOfTorus t

/-- **`Im ∂U` AT THE SPIKE'S "T3" PLAQUETTES** — the excited bond enters inverted, so the value is
the NEGATIVE of the T1 value.  That relative sign is what makes the lattice divergence `D*F`
nonzero in §4 rather than cancelling. -/
theorem imHolonomy_spike_torus_p3 (t : ℝ) :
    imHolonomy (spikeU (torus t)) p3
      = -dg ((Real.sin t : ℝ) : ℂ) (-((Real.sin t : ℝ) : ℂ)) := by
  unfold imHolonomy
  rw [holonomy_spikeU_p3, holonomyElemInv_spikeU_p3, torus_inv]
  rw [← neg_sub (((torus t : SU₂) : M₂)) (((torus (-t) : SU₂) : M₂)), smul_neg, imOfTorus]

theorem imHolonomy_spike_torus_p4 (t : ℝ) :
    imHolonomy (spikeU (torus t)) p4
      = -dg ((Real.sin t : ℝ) : ℂ) (-((Real.sin t : ℝ) : ℂ)) := by
  unfold imHolonomy
  rw [holonomy_spikeU_p4, holonomyElemInv_spikeU_p4, torus_inv]
  rw [← neg_sub (((torus t : SU₂) : M₂)) (((torus (-t) : SU₂) : M₂)), smul_neg, imOfTorus]

/-- The four values are traceless, so `π` fixes them. -/
theorem trace_dgSin (t : ℝ) :
    Matrix.trace (dg ((Real.sin t : ℝ) : ℂ) (-((Real.sin t : ℝ) : ℂ))) = 0 := by
  rw [dg_trace]; ring

theorem piProj_imHolonomy_wp (t : ℝ) :
    piProj (imHolonomy (spikeU (torus t)) witnessPlaquette)
      = imHolonomy (spikeU (torus t)) witnessPlaquette :=
  piProj_eq_self_of_trace_zero (by rw [imHolonomy_spike_torus_wp]; exact trace_dgSin t)

theorem piProj_imHolonomy_wp2 (t : ℝ) :
    piProj (imHolonomy (spikeU (torus t)) myWitnessPlaquette2)
      = imHolonomy (spikeU (torus t)) myWitnessPlaquette2 :=
  piProj_eq_self_of_trace_zero (by rw [imHolonomy_spike_torus_wp2]; exact trace_dgSin t)

theorem piProj_imHolonomy_p3 (t : ℝ) :
    piProj (imHolonomy (spikeU (torus t)) p3) = imHolonomy (spikeU (torus t)) p3 := by
  refine piProj_eq_self_of_trace_zero ?_
  rw [imHolonomy_spike_torus_p3, Matrix.trace_neg, trace_dgSin]
  ring

theorem piProj_imHolonomy_p4 (t : ℝ) :
    piProj (imHolonomy (spikeU (torus t)) p4) = imHolonomy (spikeU (torus t)) p4 := by
  refine piProj_eq_self_of_trace_zero ?_
  rw [imHolonomy_spike_torus_p4, Matrix.trace_neg, trace_dgSin]
  ring

/-! ## §4 — `F`, `D*`, AND `J`

`FnuMu U ν μ y` is `π Im ∂U` at the `(ν,μ)`-plaquette based at `y`, antisymmetrised; for `ν > μ = 0`
the `μ < ν` branch fires with a MINUS sign.  `DstarDir` transports by `U(x−e_ν, ν)⁻¹` — and every
link of the spike in directions `1`, `2` is the identity, so the transport is trivial and `D*` is
the plain lattice backward difference.  That is why the computation closes in one line per `ν`. -/

theorem FnuMu_spike_1_0_witnessY (t : ℝ) :
    FnuMu (spikeU (torus t)) 1 0 witnessY = -imHolonomy (spikeU (torus t)) witnessPlaquette := by
  unfold FnuMu
  rw [dif_neg (by decide), dif_pos (show (0 : Fin 3) < 1 by decide)]
  show -piProj (imHolonomy (spikeU (torus t)) (witnessY, ⟨(0, 1), _⟩)) = _
  rw [show (witnessY, (⟨(0, 1), by decide⟩ : PeriodicPlaquetteDirections)) = witnessPlaquette
      from rfl, piProj_imHolonomy_wp]

theorem FnuMu_spike_1_0_p3Site (t : ℝ) :
    FnuMu (spikeU (torus t)) 1 0 p3Site = -imHolonomy (spikeU (torus t)) p3 := by
  unfold FnuMu
  rw [dif_neg (by decide), dif_pos (show (0 : Fin 3) < 1 by decide)]
  show -piProj (imHolonomy (spikeU (torus t)) (p3Site, ⟨(0, 1), _⟩)) = _
  rw [show (p3Site, (⟨(0, 1), by decide⟩ : PeriodicPlaquetteDirections)) = p3 from rfl,
    piProj_imHolonomy_p3]

theorem FnuMu_spike_2_0_witnessY (t : ℝ) :
    FnuMu (spikeU (torus t)) 2 0 witnessY
      = -imHolonomy (spikeU (torus t)) myWitnessPlaquette2 := by
  unfold FnuMu
  rw [dif_neg (by decide), dif_pos (show (0 : Fin 3) < 2 by decide)]
  show -piProj (imHolonomy (spikeU (torus t)) (witnessY, ⟨(0, 2), _⟩)) = _
  rw [show (witnessY, (⟨(0, 2), by decide⟩ : PeriodicPlaquetteDirections)) = myWitnessPlaquette2
      from rfl, piProj_imHolonomy_wp2]

theorem FnuMu_spike_2_0_p4Site (t : ℝ) :
    FnuMu (spikeU (torus t)) 2 0 p4Site = -imHolonomy (spikeU (torus t)) p4 := by
  unfold FnuMu
  rw [dif_neg (by decide), dif_pos (show (0 : Fin 3) < 2 by decide)]
  show -piProj (imHolonomy (spikeU (torus t)) (p4Site, ⟨(0, 2), _⟩)) = _
  rw [show (p4Site, (⟨(0, 2), by decide⟩ : PeriodicPlaquetteDirections)) = p4 from rfl,
    piProj_imHolonomy_p4]

theorem shiftBack_witnessY_1 : periodicLatticeShiftBack witnessY 1 = p3Site := by
  rw [← shift_p3Site_eq, periodicLatticeShiftBack_shift]

theorem shiftBack_witnessY_2 : periodicLatticeShiftBack witnessY 2 = p4Site := by
  rw [← shift_p4Site_eq, periodicLatticeShiftBack_shift]

/-- **`(D*₁ F₁₀)(witnessY) = 2·diag(sin t, −sin t)`.**  The transport is trivial because
`spikeU g (p3Site, 1) = 1`, and the two `F` values enter with opposite signs, so they ADD. -/
theorem DstarDir_1_spike (t : ℝ) :
    DstarDir (spikeU (torus t)) 1 (fun y => FnuMu (spikeU (torus t)) 1 0 y) witnessY
      = dg ((Real.sin t : ℝ) : ℂ) (-((Real.sin t : ℝ) : ℂ))
        + dg ((Real.sin t : ℝ) : ℂ) (-((Real.sin t : ℝ) : ℂ)) := by
  unfold DstarDir
  dsimp only
  rw [shiftBack_witnessY_1, FnuMu_spike_1_0_p3Site, FnuMu_spike_1_0_witnessY,
    spikeU_at_p3Site_nu, inv_one, conjByAmbient_one_apply]
  rw [imHolonomy_spike_torus_p3, imHolonomy_spike_torus_wp]
  abel

theorem DstarDir_2_spike (t : ℝ) :
    DstarDir (spikeU (torus t)) 2 (fun y => FnuMu (spikeU (torus t)) 2 0 y) witnessY
      = dg ((Real.sin t : ℝ) : ℂ) (-((Real.sin t : ℝ) : ℂ))
        + dg ((Real.sin t : ℝ) : ℂ) (-((Real.sin t : ℝ) : ℂ)) := by
  unfold DstarDir
  dsimp only
  rw [shiftBack_witnessY_2, FnuMu_spike_2_0_p4Site, FnuMu_spike_2_0_witnessY,
    spikeU_at_p4Site_nu, inv_one, conjByAmbient_one_apply]
  rw [imHolonomy_spike_torus_p4, imHolonomy_spike_torus_wp2]
  abel

/-- **THE SOURCE, IN CLOSED FORM.**  `J(U*)(witnessY, 0) = 4·diag(sin t, −sin t)`.

This is an EQUALITY, not a bound: the `ν = 0` term is killed by `Jfield`'s own guard, and the
`ν = 1, 2` terms each contribute `2·diag(sin t, −sin t)`. -/
theorem Jfield_spike (t : ℝ) :
    Jfield (spikeU (torus t)) witnessY 0
      = dg ((4 * Real.sin t : ℝ) : ℂ) (-((4 * Real.sin t : ℝ) : ℂ)) := by
  unfold Jfield
  rw [Fin.sum_univ_three]
  rw [if_pos rfl, if_neg (by decide : (1 : Fin 3) ≠ 0), if_neg (by decide : (2 : Fin 3) ≠ 0)]
  rw [DstarDir_1_spike, DstarDir_2_spike, dg_add, zero_add, dg_add]
  refine dg_congr ?_ ?_ <;> push_cast <;> ring

/-! ## §5 — THE SOURCE IS ACTIVE: `J ≠ 0` AT EVERY `0 < t < π` -/

/-- **THE SOURCE IS NONZERO.**  The `(0,0)` entry of `J(U*)(witnessY,0)` is `4 sin t`, and
`sin t > 0` on `(0, π)`. -/
theorem Jsource_spike_ne_zero {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    Jsource (spikeU (torus t)) (witnessY, (0 : Fin 3)) ≠ 0 := by
  have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht htpi
  show Jfield (spikeU (torus t)) witnessY 0 ≠ 0
  rw [Jfield_spike]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  rw [dg_00, Matrix.zero_apply] at h00
  have hz : (4 * Real.sin t : ℝ) = 0 := by exact_mod_cast h00
  linarith

/-- **AND ON THE TRUE BOND CARRIER.**  `JsuTwo U* ≠ 0`, hence `0 < ‖JsuTwo U*‖`: the source vector
the terminal composition actually consumes is nonzero. -/
theorem JsuTwo_spike_ne_zero {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    JsuTwo (spikeU (torus t)) ≠ 0 := by
  intro h
  refine Jsource_spike_ne_zero ht htpi ?_
  have hzero : ((WithLp.ofLp (JsuTwo (spikeU (torus t))) (witnessY, (0 : Fin 3)) : SuTwo) : M₂)
      = 0 := by rw [h]; rfl
  rw [AdalyFormal.Balaban.SourceWiredJ.JsuTwo_apply] at hzero
  have := congrArg (fun X : M₂ => (Complex.I⁻¹ : ℂ) • X) hzero
  simpa [smul_smul, Complex.I_ne_zero] using this

theorem norm_JsuTwo_spike_pos {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    0 < ‖JsuTwo (spikeU (torus t))‖ :=
  norm_pos_iff.mpr (JsuTwo_spike_ne_zero ht htpi)

/-! ## §6 — BOTH SMALLNESS CLASSES, AT THE SAME PARAMETER

The entrywise (SOURCE-side) class and the Frobenius sup (COVARIANCE-side) class are evaluated at the
same `t`.  Both are `O(t)`.  This is the arithmetic the prosecution asked for: the two classes are
not in tension, because they are controlled by the same parameter with the same power. -/

/-- `frobSupBond` of a spike is the Frobenius norm of `g − 1`: the sup over `192` bonds is attained
at the excited one, every other bond contributing `0`. -/
theorem frobSupBond_spikeU (g : SU₂) :
    frobSupBond (spikeU g) = AdalyFormal.Balaban.RMapLipschitz.frobNorm ((g : M₂) - 1) := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ (fun b _ => ?_)
    by_cases hb : b = (witnessY, (0 : Fin 3))
    · subst hb; rw [spikeU_at_x_mu]
    · have h1 : spikeU g b = 1 := by unfold spikeU; rw [if_neg hb]
      rw [h1]
      have hz : (((1 : SU₂) : M₂) - 1) = 0 := by
        rw [show ((1 : SU₂) : M₂) = 1 from rfl, sub_self]
      rw [hz, AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
      exact AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _
  · have h := frobNorm_le_frobSupBond (spikeU g) (witnessY, (0 : Fin 3))
    rwa [spikeU_at_x_mu] at h

/-- **THE COVARIANCE-SIDE QUANTITY, EXACTLY.**  `frobSupBond U* = √(4(1−cos t)) = √8·|sin(t/2)|`. -/
theorem frobSupBond_spike_torus (t : ℝ) :
    frobSupBond (spikeU (torus t)) = Real.sqrt (4 * (1 - Real.cos t)) := by
  rw [frobSupBond_spikeU, frobNorm_torus_sub_one]

/-- `2|sin(t/2)| ≤ t` on `[0, π]` — the one calculus step, used for both classes. -/
theorem two_abs_sin_half_le {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ Real.pi) :
    2 * |Real.sin (t / 2)| ≤ t := by
  have hhalf : 0 ≤ t / 2 := by linarith
  have hhpi : t / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hnn : 0 ≤ Real.sin (t / 2) := Real.sin_nonneg_of_nonneg_of_le_pi hhalf hhpi
  rw [abs_of_nonneg hnn]
  have := Real.sin_le hhalf
  linarith

/-- **THE COVARIANCE-SIDE BOUND.**  `frobSupBond U* ≤ √2·t`. -/
theorem frobSupBond_spike_le {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ Real.pi) :
    frobSupBond (spikeU (torus t)) ≤ Real.sqrt 2 * t := by
  rw [frobSupBond_spike_torus, sqrt_four_one_sub_cos]
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h8]
  have hkey := two_abs_sin_half_le ht htpi
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [hkey, h2]

/-- **THE SOURCE-SIDE CLASS.**  `LinkDev t U*` — every entry of `U*(b) − 1` is bounded by `t`.
Off the excited bond the matrix is `0`; at the excited bond the entries are `e^{±it} − 1`, of
modulus `2|sin(t/2)| ≤ t`, and the off-diagonal entries vanish. -/
theorem norm_cexp_sub_one (s : ℝ) :
    ‖Complex.exp ((s : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (s / 2)| := by
  have hform : Complex.exp ((s : ℂ) * Complex.I) - 1
      = ((Real.cos s - 1 : ℝ) : ℂ) + ((Real.sin s : ℝ) : ℂ) * Complex.I := by
    rw [cexp_pos_form, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  rw [hform, Complex.norm_add_mul_I]
  have hdouble : Real.cos s = 2 * Real.cos (s / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (s / 2)
    rw [show (2 : ℝ) * (s / 2) = s by ring] at h
    exact h
  have hpy := Real.sin_sq_add_cos_sq (s / 2)
  have hid : (Real.cos s - 1) ^ 2 + Real.sin s ^ 2 = (2 * |Real.sin (s / 2)|) ^ 2 := by
    have hpys := Real.sin_sq_add_cos_sq s
    rw [mul_pow, sq_abs]
    nlinarith [hpys, hdouble, hpy]
  rw [hid, Real.sqrt_sq (by positivity)]

/-- Entrywise bound for a diagonal matrix, from bounds on the two diagonal entries. -/
theorem EB_dg {a b : ℂ} {c : ℝ} (hc : 0 ≤ c) (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : EB c (dg a b) := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [dg, Matrix.diagonal] using ha
  · simpa [dg, Matrix.diagonal] using hc
  · simpa [dg, Matrix.diagonal] using hc
  · simpa [dg, Matrix.diagonal] using hb

/-- **THE SOURCE-SIDE CLASS.**  `LinkDev t U*` — every entry of `U*(b) − 1` is bounded by `t`.
Off the excited bond the matrix is `0`; at the excited bond the entries are `e^{±it} − 1`, of
modulus `2|sin(t/2)| ≤ t`, and the off-diagonal entries vanish. -/
theorem linkDev_spike_torus {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ Real.pi) :
    LinkDev t (spikeU (torus t)) := by
  intro b
  by_cases hb : b = (witnessY, (0 : Fin 3))
  · subst hb
    rw [spikeU_at_x_mu]
    have hentry : ((torus t : SU₂) : M₂) - 1
        = dg (Complex.exp ((t : ℂ) * Complex.I) - 1)
            (Complex.exp (-((t : ℂ) * Complex.I)) - 1) := by
      rw [coe_torus_dg, ← dg_one, dg_sub]
    rw [hentry]
    refine EB_dg ht ?_ ?_
    · rw [norm_cexp_sub_one]; exact two_abs_sin_half_le ht htpi
    · rw [show Complex.exp (-((t : ℂ) * Complex.I))
          = Complex.exp (((-t : ℝ) : ℂ) * Complex.I) by push_cast; ring_nf]
      rw [norm_cexp_sub_one (-t), show (-t) / 2 = -(t / 2) by ring, Real.sin_neg, abs_neg]
      exact two_abs_sin_half_le ht htpi
  · have h1 : spikeU (torus t) b = 1 := by unfold spikeU; rw [if_neg hb]
    rw [h1]
    have hz : (((1 : SU₂) : M₂) - 1) = 0 := by
      rw [show ((1 : SU₂) : M₂) = 1 from rfl, sub_self]
    rw [hz]
    intro i j
    simpa using ht

/-- **CURVATURE IS NONZERO, AND SO IS THE COVARIANCE-SIDE QUANTITY.**  `0 < frobSupBond U*` and the
plaquette holonomy differs from `1`, on `0 < t < π`. -/
theorem spike_is_curved {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    holonomyElem (spikeU (torus t)) witnessPlaquette ≠ 1
      ∧ 0 < frobSupBond (spikeU (torus t)) := by
  have hsin : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfrob : frobSupBond (spikeU (torus t)) = Real.sqrt 8 * |Real.sin (t / 2)| := by
    rw [frobSupBond_spike_torus, sqrt_four_one_sub_cos]
  have h8 : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hpos : 0 < frobSupBond (spikeU (torus t)) := by
    rw [hfrob, abs_of_pos hsin]; positivity
  refine ⟨?_, hpos⟩
  rw [holonomy_spikeU_witnessPlaquette]
  intro hone
  have : frobSupBond (spikeU (torus t)) = 0 := by
    rw [frobSupBond_spikeU, hone, show ((1 : SU₂) : M₂) = 1 from rfl, sub_self]
    exact AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero
  linarith

/-! ## §7 — THE TWO CLASSES ARE COMPATIBLE: THE WINDOW, IN CLOSED FORM

§6 gives `LinkDev t` and `frobSupBond ≤ √2·t` at the SAME `t`.  Both thresholds are therefore met by
making `t` small, and the only question is whether the required smallness is attainable — it is,
because every threshold in sight is a strictly positive number and both classes are LINEAR in `t`.
§7 states that as an arithmetic lemma with no reference to the lattice, so that it can be checked
independently of everything above. -/

/-- **THE WINDOW IS NONEMPTY, IN CLOSED FORM.**  For any coefficient `K > 0` and any positive floor
`γ`, there is a `t` in `(0, 1]` meeting the covariance threshold `√2·t ≤ 1/1488` (the `ℓ = 2` value
of `1/(186ℓ³)`) and the source threshold `2·(K t)² < γ` simultaneously.  The witness is explicit:
`t = min 1 (min (1/2976) (γ/(4K²)))`. -/
theorem window_nonempty (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ Real.sqrt 2 * t ≤ 1 / 1488 ∧ 2 * (K * t) ^ 2 < γ := by
  refine ⟨min 1 (min (1 / 2976) (γ / (4 * K ^ 2))), ?_, min_le_left _ _, ?_, ?_⟩
  · exact lt_min one_pos (lt_min (by norm_num) (by positivity))
  · have h1 : min 1 (min (1 / 2976) (γ / (4 * K ^ 2))) ≤ 1 / 2976 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have h0 : 0 < min 1 (min (1 / 2976) (γ / (4 * K ^ 2))) :=
      lt_min one_pos (lt_min (by norm_num) (by positivity))
    nlinarith [h1, h2, h0, Real.sqrt_nonneg 2]
  · set t := min 1 (min (1 / 2976) (γ / (4 * K ^ 2))) with hdef
    have h0 : 0 < t := lt_min one_pos (lt_min (by norm_num) (by positivity))
    have hle1 : t ≤ 1 := min_le_left _ _
    have hleg : t ≤ γ / (4 * K ^ 2) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hK2 : 0 < 4 * K ^ 2 := by positivity
    have hmul : t * (4 * K ^ 2) ≤ γ := by
      rw [← le_div_iff₀ hK2]; exact hleg
    nlinarith [h0, hle1, hmul, hK2, sq_nonneg (K * t)]


/-! ## §8 — THE COMPOSITION: TERMINAL POSITIVITY AT A CURVED, SOURCE-BEARING BACKGROUND

`end_to_end_flat` runs `terminal_posDef_of_source_bound` at `U = 1`, where `‖J‖ ≤ 0` and the source
term is identically zero.  §8 runs the SAME theorem at `U*`, on the `4³` torus at `ℓ = 2`
(`2 < 4` and `2 ∣ 4`, so the tiling hypotheses hold), with

* `v := J(U*)`, so the source operator of `assemblyDatum_isSourceOperator` is `‖J(U*)‖²·I`, which
  is NONZERO by §5 — the degeneracy `end_to_end_flat` discloses is absent by construction, not by
  assumption;
* `c₂ := ‖v‖ = ‖J(U*)‖`, the datum's own constant;
* `R := spikeK·t`, the §6 bound on `‖J(U*)‖`.

Everything except `hthr` and `hRthr` is generic in `U` and is taken from `TerminalAssembly`
unchanged. -/

open AdalyFormal.Balaban.VariationalProjectorH1 (solutionOperator)
open AdalyFormal.Balaban.TerminalCompose (gammaBrick gammaBrick_pos)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.ConstructCDC (TildeFn cZero)
open AdalyFormal.Balaban.FullReparamC (dinvC)
open AdalyFormal.Balaban.DeltaKWiring (cdcFormTrue bondQext sourceTerm bondDtilde2
  norm_cZero_pos)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.TerminalAssembly (assemblyDatum assemblyDatum_isPrintedG1Form
  assemblyDatum_hraw assemblyDatum_isSourceOperator assemblyDatum_hD2 assemblyDatum_H1_eq_id
  terminal_posDef_of_source_bound sharpFloorConst sharpFloorConst_eq_at_zero)

/-- The `4³` torus tiles at `ℓ = 2`, strictly. -/
theorem witnessL_strict : ∀ ν : Fin 3, 2 < witnessL ν + 1 := by decide

theorem witnessL_dvd : ∀ ν : Fin 3, 2 ∣ (witnessL ν + 1) := by decide

/-- **`‖H₁‖ ≤ 1` AT THE ASSEMBLY DATUM.**  `assemblyDatum_H1_eq_id` says `H₁` acts as the identity;
this turns that into the operator-norm bound the threshold needs.  (`TerminalAssembly` proves
`1 ≤ ‖H₁‖` there; together `‖H₁‖ = 1` exactly, so nothing is lost by using `1`.) -/
theorem norm_H1_assembly_le_one (U : PeriodicLinkConfiguration SU₂ witnessL) {a : ℝ} (ha : 0 < a) :
    ‖solutionOperator (assemblyDatum U ha)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun B => ?_)
  rw [assemblyDatum_H1_eq_id U ha B, one_mul]

/-- The source-bound coefficient `√(2|Bond|)·495` of `norm_JsuTwo_le`, named so the threshold
arithmetic can be done once. -/
noncomputable def spikeK : ℝ := Real.sqrt (2 * (Fintype.card (Bond witnessL))) * 495

theorem spikeK_pos : 0 < spikeK := by
  have hc : 0 < Fintype.card (Bond witnessL) := Fintype.card_pos
  have hcR : (0 : ℝ) < (Fintype.card (Bond witnessL) : ℝ) := by exact_mod_cast hc
  unfold spikeK
  have : 0 < Real.sqrt (2 * (Fintype.card (Bond witnessL) : ℝ)) :=
    Real.sqrt_pos.mpr (by linarith)
  positivity

/-- **THE SOURCE BOUND AT THE SPIKE.**  `‖J(U*)‖ ≤ spikeK·t`, from `norm_JsuTwo_le` fed with §6's
`LinkDev t`. -/
theorem norm_JsuTwo_spike_le {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ Real.pi) :
    ‖JsuTwo (spikeU (torus t))‖ ≤ spikeK * t := by
  have h := norm_JsuTwo_le (spikeU (torus t)) (linkDev_spike_torus ht htpi)
  unfold spikeK
  calc ‖JsuTwo (spikeU (torus t))‖
      ≤ Real.sqrt (2 * (Fintype.card (Bond witnessL))) * (495 * t) := h
    _ = Real.sqrt (2 * (Fintype.card (Bond witnessL))) * 495 * t := by ring

/-- **THE COMPOSED POSITIVITY, AT THE CURVED SOURCE-BEARING BACKGROUND.**

At `ℓ = 2` on the `4³` torus, at `U* = spikeU (torus t)`, at the §9-of-`TerminalAssembly` witness
datum, with the source vector `v := J(U*)` — the printed `C*Δ_kC` is positive definite on `ℓ²(Λ̃)`.

The two hypotheses that are NOT generic in `U` are exactly the two smallness classes, stated in the
same parameter `t`: `hcov` is the covariance class `√2·t ≤ 1/1488 = 1/(186·2³)`, and `hsrc` is the
source threshold.  §7 proves both are met simultaneously by an explicit `t`. -/
theorem terminal_posDef_at_curved_spike {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hcov : Real.sqrt 2 * t ≤ 1 / 1488)
    (hsrc : 2 * (spikeK * t) ^ 2 < gammaBrick 2)
    (bc : BaseConstant) (ha : 0 < usedAt bc 0)
    (w : TildeFn witnessL 2) (hw : w ≠ 0) :
    0 < cdcFormTrue (assemblyDatum (spikeU (torus t)) ha) bc
        (bondQext (JsuTwo (spikeU (torus t)))) (JsuTwo (spikeU (torus t)))
        (spikeU (torus t)) 2 (dinvC (spikeU (torus t)) 2) w := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have htpi : t ≤ Real.pi := by linarith
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  -- the covariance class, in the exact shape `terminal_posDef_of_source_bound` consumes
  have hthr : frobSupBond (spikeU (torus t)) ≤ 1 / (186 * (2 : ℝ) ^ 3) := by
    have h1 := frobSupBond_spike_le ht0 htpi
    have h2 : (1 : ℝ) / (186 * (2 : ℝ) ^ 3) = 1 / 1488 := by norm_num
    rw [h2]
    linarith
  have hJle := norm_JsuTwo_spike_le ht0 htpi
  have hJnn : (0 : ℝ) ≤ ‖JsuTwo (spikeU (torus t))‖ := norm_nonneg _
  have hKt : (0 : ℝ) ≤ spikeK * t := by
    have := spikeK_pos; positivity
  have hH1 := norm_H1_assembly_le_one (spikeU (torus t)) ha
  have hH1nn : (0 : ℝ) ≤ ‖solutionOperator (assemblyDatum (spikeU (torus t)) ha)‖ :=
    norm_nonneg _
  have hγ : 0 < gammaBrick 2 := gammaBrick_pos (by norm_num)
  have hsharp : sharpFloorConst (gammaBrick 2) 0 1 = gammaBrick 2 := by
    rw [sharpFloorConst_eq_at_zero (by norm_num : 0 < 2) 1]
    norm_num
  refine terminal_posDef_of_source_bound (le_refl 2) witnessL_strict witnessL_dvd
    (spikeU (torus t)) hthr (assemblyDatum (spikeU (torus t)) ha) bc
    (curlCovariantCLM_L2 (spikeU (torus t))) (0 : BondFnL2 witnessL →L[ℝ] BondFnL2 witnessL)
    (assemblyDatum_isPrintedG1Form (spikeU (torus t)) ha)
    1 0 one_pos le_rfl (by positivity)
    (assemblyDatum_hraw (spikeU (torus t)) ha)
    (bondQext (JsuTwo (spikeU (torus t)))) (JsuTwo (spikeU (torus t))) _
    (assemblyDatum_isSourceOperator (spikeU (torus t)) ha _ _)
    ‖JsuTwo (spikeU (torus t))‖ hJnn (assemblyDatum_hD2 _)
    (spikeK * t) hJle ?_ w hw
  rw [hsharp]
  have step1 : 2 * ‖solutionOperator (assemblyDatum (spikeU (torus t)) ha)‖
        * ‖JsuTwo (spikeU (torus t))‖ * (spikeK * t)
      ≤ 2 * ‖JsuTwo (spikeU (torus t))‖ * (spikeK * t) := by
    nlinarith [mul_nonneg (mul_nonneg hJnn hKt) (sub_nonneg.mpr hH1)]
  have step2 : 2 * ‖JsuTwo (spikeU (torus t))‖ * (spikeK * t)
      ≤ 2 * (spikeK * t) * (spikeK * t) := by
    nlinarith [mul_nonneg hKt (sub_nonneg.mpr hJle)]
  have step3 : 2 * (spikeK * t) * (spikeK * t) = 2 * (spikeK * t) ^ 2 := by ring
  linarith

/-! ### §8d — THE SOURCE TERM DOES NOT MERELY EXIST: IT STRICTLY OPPOSES THE FLOOR

`cdcFormTrue` is `deltaKForm`, whose printed split (`DeltaKWiring.deltaKForm_split`) is

    ⟨B, CompInv B⟩ − a‖B‖² − 2·sourceTerm ,      sourceTerm D Qext J B = ⟨H₁ D̃⁽²⁾(B), J⟩ .

So the source enters with coefficient `−2`.  "The source term is not identically zero" is therefore
a WEAKER statement than the one available here: at this witness the source term is STRICTLY
POSITIVE, hence `−2·sourceTerm` is STRICTLY NEGATIVE, and the positivity of §8 is obtained in spite
of a term that is actively subtracting.

At the witness datum `H₁ = I` and `D̃⁽²⁾(B) = ‖B‖²·v`, so with `v := J` the term is exactly
`‖B‖²·‖J‖²` — evaluated, not estimated. -/

theorem sourceTerm_at_spike_eq {t : ℝ} {a : ℝ} (ha : 0 < a) (w : TildeFn witnessL 2) :
    sourceTerm (assemblyDatum (spikeU (torus t)) ha)
        (bondQext (JsuTwo (spikeU (torus t)))) (JsuTwo (spikeU (torus t)))
        (cZero (spikeU (torus t)) 2 (dinvC (spikeU (torus t)) 2) w)
      = ‖cZero (spikeU (torus t)) 2 (dinvC (spikeU (torus t)) 2) w‖ ^ 2
        * ‖JsuTwo (spikeU (torus t))‖ ^ 2 := by
  unfold sourceTerm
  rw [bondDtilde2, assemblyDatum_H1_eq_id, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- **THE SOURCE TERM IS STRICTLY POSITIVE AT THE WITNESS**, hence its contribution
`−2·sourceTerm` to `cdcFormTrue` is strictly negative.  Both factors are nonzero for a reason:
`‖C₀B̃‖ > 0` is `DeltaKWiring.norm_cZero_pos` at `w ≠ 0`, and `‖J‖ > 0` is §5 — the curvature. -/
theorem sourceTerm_at_spike_pos {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) {a : ℝ} (ha : 0 < a)
    (w : TildeFn witnessL 2) (hw : w ≠ 0) :
    0 < sourceTerm (assemblyDatum (spikeU (torus t)) ha)
        (bondQext (JsuTwo (spikeU (torus t)))) (JsuTwo (spikeU (torus t)))
        (cZero (spikeU (torus t)) 2 (dinvC (spikeU (torus t)) 2) w)
      ∧ (-2 : ℝ) * sourceTerm (assemblyDatum (spikeU (torus t)) ha)
        (bondQext (JsuTwo (spikeU (torus t)))) (JsuTwo (spikeU (torus t)))
        (cZero (spikeU (torus t)) 2 (dinvC (spikeU (torus t)) 2) w) < 0 := by
  have hB : 0 < ‖cZero (spikeU (torus t)) 2 (dinvC (spikeU (torus t)) 2) w‖ :=
    norm_cZero_pos (spikeU (torus t)) (dinvC (spikeU (torus t)) 2) w hw
  have hJ : 0 < ‖JsuTwo (spikeU (torus t))‖ := norm_JsuTwo_spike_pos ht htpi
  have hpos : 0 < sourceTerm (assemblyDatum (spikeU (torus t)) ha)
      (bondQext (JsuTwo (spikeU (torus t)))) (JsuTwo (spikeU (torus t)))
      (cZero (spikeU (torus t)) 2 (dinvC (spikeU (torus t)) 2) w) := by
    rw [sourceTerm_at_spike_eq ha w]; positivity
  exact ⟨hpos, by linarith⟩

/-! ### §8c — THE SAME, AT AN ARBITRARY DATUM: WHAT THIS LANE ACTUALLY SETTLES

`terminal_posDef_of_source_bound` has ten hypotheses.  Exactly TWO of them are about the background
`U`: `hthr` (the covariance class) and — through `hJbound` — the size of `J(U)`.  Everything else is
about the covariance datum `D`, and this lane says nothing about it.

§8c is therefore the honest statement of the contribution: for EVERY datum on the bond carrier, the
two `U`-dependent hypotheses are DISCHARGED at a curved, source-bearing background.  The remaining
hypotheses are passed through untouched, so a reader can see precisely what is and is not supplied
here.

**In particular this lane does NOT remove the datum-level degeneracy.**  `TerminalAssembly`
§9d proves that at its `assemblyDatum` the Schur complement collapses (`Q = I`,
`assemblyDatum_Q_bijective`) and the composed floor IS the brick
(`assemblyDatum_deltaKQuadForm_eq_curl_energy`), so §8's instantiation inherits that.  Of the two
degeneracies `end_to_end_flat` discloses, this lane removes the SECOND (the vanishing source) and
leaves the FIRST (`Q = I`) exactly where it was. -/

theorem terminal_posDef_at_spike_any_datum {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hcov : Real.sqrt 2 * t ≤ 1 / 1488)
    {P₁ P₃ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₃] [InnerProductSpace ℝ P₃]
    (D : AdalyFormal.Balaban.VariationalProjectorH1.BalabanCovarianceData
          (BondFnL2 witnessL) (BondFnL2 witnessL))
    (bc : BaseConstant) (d : BondFnL2 witnessL →L[ℝ] P₁) (pen : BondFnL2 witnessL →L[ℝ] P₃)
    (hform : AdalyFormal.Balaban.TerminalAssembly.IsPrintedG1Form D (usedAt bc 0) d pen)
    (σ₀ κ : ℝ) (hσ₀ : 0 < σ₀) (hκ : 0 ≤ κ) (hhalf : κ ≤ Real.sqrt (gammaBrick 2) / 2)
    (hraw : ∀ A : BondFnL2 witnessL,
      ‖curlCovariantCLM_L2 (spikeU (torus t)) (D.Q A)‖ ≤ σ₀ * ‖d A‖ + κ * ‖D.Q A‖)
    (Qext : BondFnL2 witnessL → BondFnL2 witnessL)
    (S : BondFnL2 witnessL →L[ℝ] BondFnL2 witnessL)
    (hS : AdalyFormal.Balaban.DeltaKWiring.IsSourceOperator D Qext
      (JsuTwo (spikeU (torus t))) S)
    (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hD2 : ∀ B : BondFnL2 witnessL,
      ‖AdalyFormal.Balaban.SourceJ.Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (hRthr : 2 * ‖solutionOperator D‖ * c₂ * (spikeK * t)
      < sharpFloorConst (gammaBrick 2) κ σ₀)
    (w : TildeFn witnessL 2) (hw : w ≠ 0) :
    0 < cdcFormTrue D bc Qext (JsuTwo (spikeU (torus t))) (spikeU (torus t)) 2
        (dinvC (spikeU (torus t)) 2) w := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have htpi : t ≤ Real.pi := by linarith
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  have hthr : frobSupBond (spikeU (torus t)) ≤ 1 / (186 * (2 : ℝ) ^ 3) := by
    have h1 := frobSupBond_spike_le ht0 htpi
    have h2 : (1 : ℝ) / (186 * (2 : ℝ) ^ 3) = 1 / 1488 := by norm_num
    rw [h2]; linarith
  exact terminal_posDef_of_source_bound (le_refl 2) witnessL_strict witnessL_dvd
    (spikeU (torus t)) hthr D bc d pen hform σ₀ κ hσ₀ hκ hhalf hraw
    Qext (JsuTwo (spikeU (torus t))) S hS c₂ hc₂ hD2
    (spikeK * t) (norm_JsuTwo_spike_le ht0 htpi) hRthr w hw

/-- **THE HEADLINE.**  There EXISTS a parameter at which all four clauses hold at once:

1. the background is CURVED — a plaquette holonomy `≠ 1`, and `0 < frobSupBond U*`;
2. it is in the SOURCE-side class — `LinkDev t U*`, at a `t` below the source threshold;
3. it is in the COVARIANCE-side class — `frobSupBond U* ≤ 1/(186·2³)`;
4. the terminal positivity holds AT it, with the source vector `J(U*) ≠ 0`, so the source term is
   NOT identically zero.

This is the statement `TerminalAssembly` §11 records as missing: *"No configuration in the tree is
proved to satisfy the first with a curvature that is nonzero."* -/
theorem curved_source_bearing_witness_exists
    (bc : BaseConstant) (ha : 0 < usedAt bc 0) (w : TildeFn witnessL 2) (hw : w ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      holonomyElem (spikeU (torus t)) witnessPlaquette ≠ 1 ∧
      0 < frobSupBond (spikeU (torus t)) ∧
      LinkDev t (spikeU (torus t)) ∧
      frobSupBond (spikeU (torus t)) ≤ 1 / (186 * (2 : ℝ) ^ 3) ∧
      JsuTwo (spikeU (torus t)) ≠ 0 ∧
      0 < sourceTerm (assemblyDatum (spikeU (torus t)) ha)
          (bondQext (JsuTwo (spikeU (torus t)))) (JsuTwo (spikeU (torus t)))
          (cZero (spikeU (torus t)) 2 (dinvC (spikeU (torus t)) 2) w) ∧
      0 < cdcFormTrue (assemblyDatum (spikeU (torus t)) ha) bc
          (bondQext (JsuTwo (spikeU (torus t)))) (JsuTwo (spikeU (torus t)))
          (spikeU (torus t)) 2 (dinvC (spikeU (torus t)) 2) w := by
  obtain ⟨t, ht, ht1, hcov, hsrc⟩ :=
    window_nonempty spikeK (gammaBrick 2) spikeK_pos (gammaBrick_pos (by norm_num))
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have htpi : t < Real.pi := by linarith
  have htpi' : t ≤ Real.pi := le_of_lt htpi
  obtain ⟨hcurv, hfrobpos⟩ := spike_is_curved ht htpi
  refine ⟨t, ht, ht1, hcurv, hfrobpos, linkDev_spike_torus (le_of_lt ht) htpi', ?_,
    JsuTwo_spike_ne_zero ht htpi, (sourceTerm_at_spike_pos ht htpi ha w hw).1,
    terminal_posDef_at_curved_spike ht ht1 hcov hsrc bc ha w hw⟩
  have h1 := frobSupBond_spike_le (le_of_lt ht) htpi'
  have h2 : (1 : ℝ) / (186 * (2 : ℝ) ^ 3) = 1 / 1488 := by norm_num
  rw [h2]
  linarith

/-! ## §9 — CONTROLS: WHAT MAKES THE ABOVE NON-VACUOUS, AND WHAT IT IS NOT

Three separate things could make §8 empty of content, and each is excluded by a theorem rather than
by a remark. -/

/-- **§9a — THE SOURCE TERM IS GENUINELY PRESENT.**  With `v := J(U*)` the source operator of
`assemblyDatum_isSourceOperator` is `⟪v, J⟫·I = ‖J(U*)‖²·I`, and `‖J(U*)‖² > 0`.  Contrast
`end_to_end_flat`, whose own docstring records that at `U = 1` the source contributes nothing, and
that its `v ≠ 0` binder is retained precisely because `c₂ = ‖v‖ = 0` would be a second degeneracy. -/
theorem source_coefficient_pos {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    0 < (inner ℝ (JsuTwo (spikeU (torus t))) (JsuTwo (spikeU (torus t))) : ℝ) := by
  rw [real_inner_self_eq_norm_sq]
  have := norm_JsuTwo_spike_pos ht htpi
  positivity

/-- **§9b — FALSIFIABILITY (S82).**  The same statement shape at `t = 0` is FALSE: the spike
collapses to the flat configuration and `J` vanishes identically.  So `Jsource_spike_ne_zero` is not
forced by the construction's type — it is carried by `sin t ≠ 0`. -/
theorem spike_at_zero_is_flat : spikeU (torus 0) = trivialU (L := witnessL) := by
  rw [torus_zero]; exact spikeU_one

theorem Jsource_spike_zero_eq_zero :
    Jsource (spikeU (torus 0)) (witnessY, (0 : Fin 3)) = 0 := by
  rw [spike_at_zero_is_flat]
  exact AdalyFormal.Balaban.SourceJ.Jsource_trivialU_eq_zero _

theorem mutation_at_zero_breaks_the_claim :
    ¬ (Jsource (spikeU (torus 0)) (witnessY, (0 : Fin 3)) ≠ 0) := by
  rw [Jsource_spike_zero_eq_zero]; simp

/-- **§9c — THE CURVATURE CLAUSE IS NOT IMPLIED BY LINK NON-FLATNESS**, and that is why §8 states a
plaquette holonomy rather than `0 < frobSupBond`.

`J` is built from `π Im ∂U` — the PLAQUETTE holonomy — so a configuration with large `frobSupBond`
but trivial holonomy has `J = 0`.  The witness is the tree's own `trivialU` composed with the
observation that `frobSupBond` and the holonomy are independent: here it is exhibited at the
one place where the two can be compared inside this file, namely that `J` at the flat background
vanishes for EVERY bond while `frobSupBond` is a sup over links.  Stated as the implication that
matters: `J(U*) ≠ 0` requires the holonomy clause, and §8 supplies it. -/
theorem source_needs_curvature_not_just_links :
    (∀ b : Bond witnessL, Jsource (trivialU (L := witnessL)) b = 0)
      ∧ frobSupBond (trivialU (L := witnessL)) = 0 := by
  refine ⟨fun b => AdalyFormal.Balaban.SourceJ.Jsource_trivialU_eq_zero b, ?_⟩
  rw [← spikeU_one, frobSupBond_spikeU, show ((1 : SU₂) : M₂) = 1 from rfl, sub_self]
  exact AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero

/-- **§9d — THE TWO CLASSES ARE NOT THE SAME CLASS.**  The source-side quantity (entrywise) and the
covariance-side quantity (Frobenius sup) are BOTH evaluated at the spike, in closed form, and they
differ by exactly the factor `√2`: `frobSupBond = √(4(1−cos t))` while the entrywise deviation is
`√(2−2cos t)`.  Recorded so that no reader can take §6 to be proving one class twice. -/
theorem two_classes_differ_by_sqrt_two (t : ℝ) :
    frobSupBond (spikeU (torus t)) = Real.sqrt 8 * |Real.sin (t / 2)|
      ∧ ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (t / 2)| := by
  refine ⟨?_, norm_cexp_sub_one t⟩
  rw [frobSupBond_spike_torus, sqrt_four_one_sub_cos]

/-! ### §9e — **`frobSupBond > 0` IS STRICTLY WEAKER THAN WHAT THE SOURCE NEEDS**

This is the control that decides how §8 must be read, and it is the reason the headline states a
PLAQUETTE HOLONOMY clause and not merely `0 < frobSupBond`.

`J = D*π Im ∂U` is built from the plaquette holonomy.  A CONSTANT configuration `U ≡ g` has every
plaquette holonomy equal to `g g g⁻¹ g⁻¹ = 1` (`ClassPropagationUbar.holonomyElem_constU`), so its
`J` vanishes at every bond — while its `frobSupBond` is `‖g − 1‖_F`, which is as large as one likes.

Hence "the links are not the identity" does NOT make the source active, and a witness offered on
that basis would reproduce the very degeneracy `end_to_end_flat` discloses, with a nonzero number
attached to it.  The spike of §1 is not a constant configuration, and §9e is what makes that
distinction load-bearing rather than incidental. -/

/-- `D*_ν` kills the zero function, at ANY background (the tree's version is stated at `trivialU`;
only `hG` is used, so it generalises). -/
theorem DstarDir_eq_zero_of_G_zero (U : PeriodicLinkConfiguration SU₂ witnessL) (ν : Fin 3)
    (G : PeriodicLatticeSite witnessL → M₂) (hG : ∀ y, G y = 0)
    (x : PeriodicLatticeSite witnessL) : DstarDir U ν G x = 0 := by
  unfold DstarDir
  rw [hG, hG]
  simp [conjByAmbient_apply]

theorem imHolonomy_constU (g : SU₂) (p : PeriodicLatticePlaquette witnessL) :
    imHolonomy (AdalyFormal.Balaban.CovariantFibreTransfer.constU g witnessL) p = 0 := by
  unfold imHolonomy holonomyElemInv
  rw [AdalyFormal.Balaban.ClassPropagationUbar.holonomyElem_constU]
  simp

theorem FnuMu_constU (g : SU₂) (ν μ : Fin 3) (y : PeriodicLatticeSite witnessL) :
    FnuMu (AdalyFormal.Balaban.CovariantFibreTransfer.constU g witnessL) ν μ y = 0 := by
  unfold FnuMu
  split_ifs
  · rw [imHolonomy_constU]; unfold piProj; simp
  · rw [imHolonomy_constU]; unfold piProj; simp
  · rfl

/-- **THE SOURCE VANISHES IDENTICALLY ON EVERY CONSTANT CONFIGURATION.** -/
theorem Jsource_constU_eq_zero (g : SU₂) (b : Bond witnessL) :
    Jsource (AdalyFormal.Balaban.CovariantFibreTransfer.constU g witnessL) b = 0 := by
  show Jfield _ b.1 b.2 = 0
  unfold Jfield
  refine Finset.sum_eq_zero (fun ν _ => ?_)
  split_ifs with h
  · rfl
  · exact DstarDir_eq_zero_of_G_zero _ ν _ (fun y => FnuMu_constU g ν b.2 y) b.1

/-- **THE SEPARATION, AS ONE STATEMENT.**  There is a configuration with STRICTLY POSITIVE
`frobSupBond` — indeed one in the covariance-side smallness class, with `t` as small as one likes —
whose source `J` is identically zero.  So clause (a) "`frobSupBond U > 0`" cannot substitute for the
curvature clause, and a composed positivity read off such a background would again be a statement
about a vanishing source. -/
theorem frobSupBond_pos_does_not_activate_the_source {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    0 < frobSupBond (AdalyFormal.Balaban.CovariantFibreTransfer.constU (torus t) witnessL)
      ∧ (∀ b : Bond witnessL,
          Jsource (AdalyFormal.Balaban.CovariantFibreTransfer.constU (torus t) witnessL) b = 0)
      ∧ (∀ p : PeriodicLatticePlaquette witnessL,
          holonomyElem (AdalyFormal.Balaban.CovariantFibreTransfer.constU (torus t) witnessL) p
            = 1) := by
  refine ⟨?_, fun b => Jsource_constU_eq_zero _ b,
    fun p => AdalyFormal.Balaban.ClassPropagationUbar.holonomyElem_constU _ p⟩
  rw [AdalyFormal.Balaban.BlockedBackground.frobSupBond_constU, frobNorm_torus_sub_one,
    sqrt_four_one_sub_cos]
  have hsin : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have h8 : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  rw [abs_of_pos hsin]
  positivity

/-! ## §10 — AXIOM AUDIT: TOTAL COVERAGE (every declaration in this file) -/

#print axioms spikeU
#print axioms spikeU_witnessMElem
#print axioms spikeU_one
#print axioms spikeU_at_x_mu
#print axioms spikeU_at_y_nu
#print axioms spikeU_at_x_nu
#print axioms spikeU_at_w_mu
#print axioms spikeU_at_y_nu2
#print axioms spikeU_at_w_mu2
#print axioms spikeU_at_x_nu2
#print axioms spikeU_at_p3Site_mu
#print axioms spikeU_at_p3Site_shift0_nu
#print axioms spikeU_at_p3Site_nu
#print axioms spikeU_at_p4Site_mu
#print axioms spikeU_at_p4Site_shift0_nu
#print axioms spikeU_at_p4Site_nu
#print axioms holonomy_spikeU_witnessPlaquette
#print axioms holonomy_spikeU_myWitnessPlaquette2
#print axioms holonomy_spikeU_p3
#print axioms holonomy_spikeU_p4
#print axioms holonomyElemInv_spikeU_witnessPlaquette
#print axioms holonomyElemInv_spikeU_myWitnessPlaquette2
#print axioms holonomyElemInv_spikeU_p3
#print axioms holonomyElemInv_spikeU_p4
#print axioms dg_add
#print axioms inv_two_I_mul
#print axioms coe_torus_dg
#print axioms coe_torus_neg_dg
#print axioms imOfTorus
#print axioms imHolonomy_spike_torus_wp
#print axioms imHolonomy_spike_torus_wp2
#print axioms imHolonomy_spike_torus_p3
#print axioms imHolonomy_spike_torus_p4
#print axioms trace_dgSin
#print axioms piProj_imHolonomy_wp
#print axioms piProj_imHolonomy_wp2
#print axioms piProj_imHolonomy_p3
#print axioms piProj_imHolonomy_p4
#print axioms FnuMu_spike_1_0_witnessY
#print axioms FnuMu_spike_1_0_p3Site
#print axioms FnuMu_spike_2_0_witnessY
#print axioms FnuMu_spike_2_0_p4Site
#print axioms shiftBack_witnessY_1
#print axioms shiftBack_witnessY_2
#print axioms DstarDir_1_spike
#print axioms DstarDir_2_spike
#print axioms Jfield_spike
#print axioms Jsource_spike_ne_zero
#print axioms JsuTwo_spike_ne_zero
#print axioms norm_JsuTwo_spike_pos
#print axioms frobSupBond_spikeU
#print axioms frobSupBond_spike_torus
#print axioms two_abs_sin_half_le
#print axioms frobSupBond_spike_le
#print axioms norm_cexp_sub_one
#print axioms EB_dg
#print axioms linkDev_spike_torus
#print axioms spike_is_curved
#print axioms window_nonempty
#print axioms witnessL_strict
#print axioms witnessL_dvd
#print axioms norm_H1_assembly_le_one
#print axioms spikeK
#print axioms spikeK_pos
#print axioms norm_JsuTwo_spike_le
#print axioms terminal_posDef_at_curved_spike
#print axioms sourceTerm_at_spike_eq
#print axioms sourceTerm_at_spike_pos
#print axioms terminal_posDef_at_spike_any_datum
#print axioms curved_source_bearing_witness_exists
#print axioms source_coefficient_pos
#print axioms spike_at_zero_is_flat
#print axioms Jsource_spike_zero_eq_zero
#print axioms mutation_at_zero_breaks_the_claim
#print axioms source_needs_curvature_not_just_links
#print axioms two_classes_differ_by_sqrt_two
#print axioms DstarDir_eq_zero_of_G_zero
#print axioms imHolonomy_constU
#print axioms FnuMu_constU
#print axioms Jsource_constU_eq_zero
#print axioms frobSupBond_pos_does_not_activate_the_source

end AdalyFormal.Balaban.CurvedContent
