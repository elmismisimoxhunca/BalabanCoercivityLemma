/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import CurvedFine
import AdalyFormal.Balaban.AbelianBlockingRate

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 40000
set_option linter.style.longLine false

/-!
# `SpikeBlocked` — WHAT `Ū` DOES TO THE RUNG'S FINE BACKGROUND, IN CLOSED FORM

Nothing in this file is graded by this lane (BUILD DISCIPLINE 8): it reports facts.

## §0 — THE QUESTION

The rung discharge (`BinderDerivUncond.rung_unconditional`) carries TWO free backgrounds: the fine
`UfineStar t` on `fineL` (`8³`) and the coarse `spikeU (torus tc)` on `witnessL` (`4³`), with `tc`
free of `t` (`BinderDerivTie.two_distinct_coarse_at_one_fine`). The source has ONE configuration
(CMP99b p.427–428). Tying them means DERIVING the coarse background as `Ū(U_fine)`.

So: what IS `Ū(U*_fine t)`? This file computes it, exactly, with no estimate anywhere in the chain.

## §1 — THE TOOL, AND THE ONE PIECE THAT HAD TO BE BUILT

`AbelianBlockingRate.ubarSU2_torusCfg` already proves that on a configuration valued in the maximal
torus the blocking map is EXACTLY `torus ∘ blkAngle`, an affine map on bond angles — **provided
every block loop angle lies in `[0, π)`**. That is `SuTwoLogExp.su2Log_torus`'s one-sided domain,
and **it is not satisfiable here**: the rung's fine background is a single POSITIVE spike, and six
of the eight blocked loop angles at its own coarse bond are `−t`. A one-sided branch cannot see
this configuration at all.

§2 removes the one-sidedness. `su2Log_torus_abs` proves `log (torus θ) = θ·J` on the FULL principal
branch `|θ| < π`; route: `su2Angle (torus θ) = |θ|` because `cos` is even, hence
`su2Kappa (torus θ) = |θ|/sin|θ| = θ/sin θ` — the SAME expression on both sides of `0`, the two sign
flips cancelling — after which the existing computation closes verbatim. `ubarSU2_torusCfg_abs` is
the transfer theorem with the two-sided hypothesis. **Both are reusable**: any torus-valued
configuration whose angles change sign needs them, and every configuration with a curl has both
signs.

## §2 — THE ANSWER

`UfineStar t = torusCfg (fSpike t)` definitionally (§3): `spikeAt` puts `torus t` on one bond and
`torus 0 = 1` on every other. The blocked angles at the five coarse bonds computed below are exact
rational multiples of `t`, none estimated:

| coarse bond (fine base, direction) | `blkAngle 1 2 (fSpike t)` |
|---|---|
| `b00 = ((0,0,0), 0)` — the spike's own coarse bond | `t/4` |
| `b01 = ((0,0,0), 1)` | `t/8` |
| `b20 = ((0,2,0), 0)` | `0` |
| `b21 = ((2,0,0), 1)` | `0` |
| `bw1 = ((0,6,0), 1)` — a bond of a block that does NOT contain the spike | `−t/8` |

At `b00`: the coarse bond's own telescoping contributes `+t` (only the FIRST of its two fine bonds
is excited) and six of the eight block loops contribute `−t` at weight `ell^{-3} = 1/8`, giving
`t − 6t/8 = t/4`. Counted, not fitted.

**Three facts follow, and they are the deliverable:**

1. **The blocked spike is NOT a coarse spike** (`blocked_not_single_bond`): it is non-trivial at TWO
   distinct coarse bonds, while `spikeAt e g` is non-trivial at exactly one.
2. **The spike is DAMPED at its own bond**, `t ↦ t/4` (`blocked_deviation_at_own_bond`). That is
   consistent with, not a counterexample to, the sup-over-`V` growth constants for this map
   (`≥ 19/4`, `≤ 2+5π`): a single spike is nowhere near the extremiser, which is a torus
   configuration with an aligned sign pattern on 24 bonds (`AbelianBlockingRate.fW`).
3. **The blocked background is CURVED on the coarse plaquette at the origin**
   (`blocked_curved_at_coarse_plaquette`): holonomy `torus (t/8) ≠ 1` for `0 < t < π`. Coarse-scale
   curvature is DERIVED from the fine background, not posited by a second free amplitude.

`blocked_nonlocal_support` adds a fourth, smaller one: the blocked background is non-trivial in a
coarse block that does not contain the spike at all, so the tie is not block-local.

## §3 — HOW §5 IS PRODUCED

§5's 40 loop-angle lemmas are emitted by `gen_spike.py`, which re-implements `coarseGammaPath`,
`pathAngle`, `loopAngle` and `blkAngle` over the spike field and computes every coefficient
independently of the hand analysis. **That script signs nothing** (`certificates-are-not-evidence`):
the evidential path is the Lean kernel, which re-derives each emitted number from the tree's own
definitions, so an emitted coefficient that is wrong makes the emitted `simp`/`decide` FAIL. The
two computations agree; only the kernel's is evidence.
-/

namespace AdalyFormal.SpikeBlocked

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp torus torus_add torus_zero coe_torus
  torusM su2J psiR su2Exp_psiR su2Log_torus su2Log_one su2Angle su2Kappa torusM_sub_conjTranspose)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf card_stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.Balaban.BlockingLinkEstimate (blockExponent)
open AdalyFormal.Balaban.AbelianBlockingRate (torusCfg pathAngle pathAngle_cons pathAngle_nil
  bondAngle loopAngle blkAngle coarsePathHolonomy_torusCfg coarseBondVar_torusCfg loopVar_torusCfg
  torus_inv frobNorm_torus_sub_one sqrt_four_one_sub_cos)
open AdalyFormal.CurvedFine (spikeAt spikeAt_self spikeAt_of_ne fineOrigin fineBond UfineStar)
open AdalyFormal.DatumWitness (fineL)

/-! ## §4 — THE FULL PRINCIPAL BRANCH OF `log` ON THE MAXIMAL TORUS -/

/-- `su2Angle (torus θ) = −θ` for `−π ≤ θ ≤ 0`: the mirror of `SuTwoLogExp.su2Angle_torus`. -/
theorem su2Angle_torus_neg {t : ℝ} (h0 : t ≤ 0) (h1 : -Real.pi ≤ t) : su2Angle (torus t) = -t := by
  rw [su2Angle, coe_torus, torusM, AdalyFormal.Balaban.SuTwoLogExp.dg_trace]
  rw [show (Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-((t : ℂ) * Complex.I))).re
      = 2 * Real.cos t by
    rw [Complex.add_re, AdalyFormal.Balaban.SuTwoLogExp.cexp_re,
      AdalyFormal.Balaban.SuTwoLogExp.cexp_neg_re]; ring]
  rw [show 2 * Real.cos t / 2 = Real.cos (-t) by rw [Real.cos_neg]; ring]
  exact Real.arccos_cos (by linarith) (by linarith)

/-- **`log (torus θ) = θ·J` ON THE FULL PRINCIPAL BRANCH `|θ| < π`.** Reusable. -/
theorem su2Log_torus_abs {t : ℝ} (h : |t| < Real.pi) : su2Log (torus t) = psiR t := by
  rcases eq_or_ne t 0 with rfl | hne
  · rw [torus_zero, su2Log_one, psiR]
    simp
  obtain ⟨hlo, hhi⟩ := abs_lt.mp h
  have hsin : Real.sin t ≠ 0 := by
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hpos' : 0 < Real.sin (-t) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      rw [Real.sin_neg] at hpos'
      exact ne_of_lt (by linarith)
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hhi)
  have hkap : su2Kappa (torus t) = t / Real.sin t := by
    rcases le_or_gt 0 t with h0 | h0
    · rw [su2Kappa, AdalyFormal.Balaban.SuTwoLogExp.su2Angle_torus h0 (le_of_lt hhi)]
    · rw [su2Kappa, su2Angle_torus_neg (le_of_lt h0) (le_of_lt hlo), Real.sin_neg]
      field_simp
  rw [su2Log, hkap, coe_torus, torusM_sub_conjTranspose, smul_smul, psiR]
  congr 1
  have hsinC : Complex.sin (t : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]
    exact Complex.ofReal_ne_zero.mpr hsin
  push_cast
  field_simp

/-- **THE TRANSFER THEOREM ON THE FULL BRANCH.** -/
theorem ubarSU2_torusCfg_abs {L : PeriodicLatticeExtent} (s ell : ℕ)
    (f : PeriodicLatticeEdge L → ℝ) (c : PeriodicLatticeEdge L)
    (hbr : ∀ x ∈ stepBlockOf c.1 s ell, |loopAngle s ell f c x| < Real.pi) :
    ubarSU2 s ell (torusCfg f) c = torus (blkAngle s ell f c) := by
  rw [AdalyFormal.Balaban.BlockedBackground.ubarSU2_eq_blockedLink]
  show su2Exp (blockExponent (stepBlockOf c.1 s ell) (fun _ => ((ell : ℝ) ^ 3)⁻¹)
      (fun x => loopVar s ell (torusCfg f) c x)) * coarseBondVar s ell (torusCfg f) c = _
  have hexp : blockExponent (stepBlockOf c.1 s ell) (fun _ => ((ell : ℝ) ^ 3)⁻¹)
      (fun x => loopVar s ell (torusCfg f) c x)
      = psiR (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ * loopAngle s ell f c x) := by
    unfold blockExponent psiR
    rw [Complex.ofReal_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    dsimp only
    rw [loopVar_torusCfg, su2Log_torus_abs (hbr x hx)]
    unfold psiR
    rw [smul_smul]
    congr 1
    push_cast
    ring
  rw [hexp, su2Exp_psiR, coarseBondVar_torusCfg, ← torus_add, blkAngle]

/-! ## §5 — THE RUNG'S FINE BACKGROUND IS TORUS-VALUED -/

/-- The spike's angle field: `t` on `fineBond`, `0` elsewhere. -/
def fSpike (t : ℝ) : PeriodicLatticeEdge fineL → ℝ := fun b => if b = fineBond then t else 0

/-- **`U*_fine t` IS a torus configuration**, definitionally. -/
theorem UfineStar_eq_torusCfg (t : ℝ) : UfineStar t = torusCfg (fSpike t) := by
  funext b
  show spikeAt fineBond (torus t) b = torus (fSpike t b)
  unfold spikeAt fSpike
  split_ifs with hb
  · rfl
  · rw [torus_zero]

/-- Explicit fine site of the `8³` torus. -/
def fs (a b c : Fin 8) : PeriodicLatticeSite fineL := ![a, b, c]

theorem fs_origin : fs 0 0 0 = fineOrigin := by decide

/-- **THE AFFORDABLE BLOCK ENUMERATION.** `stepBlockOf y 1 2 = S` from `S.card = 8`,
`S ⊆ stepBlockOf y 1 2` and `hfit`, via `Finset.eq_of_subset_of_card_le` +
`QjComposite.card_stepBlockOf`. The direct `decide` route filters all `512` sites of the `8³` torus
per block; this one touches `8`. **Reusable** at any base site meeting `hfit`. -/
theorem block_of (y : PeriodicLatticeSite fineL)
    (hfit : ∀ μ, (y μ).val + 1 * 2 ≤ fineL μ + 1)
    (S : Finset (PeriodicLatticeSite fineL)) (hcard : S.card = 8)
    (hsub : S ⊆ stepBlockOf y 1 2) : stepBlockOf y 1 2 = S := by
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [card_stepBlockOf y 1 2 one_pos hfit, hcard]
  norm_num

/-! ## §6 — THE FIVE COARSE BONDS, COMPUTED (emitted by `gen_spike.py`, checked by the kernel) -/

/-- Coarse bond `b00`: fine base `(0, 0, 0)`, direction `0`. -/
def b00 : PeriodicLatticeEdge fineL := (fs 0 0 0, 0)
theorem b00_fst : b00.1 = fs 0 0 0 := rfl

/-- Coarse bond `b01`: fine base `(0, 0, 0)`, direction `1`. -/
def b01 : PeriodicLatticeEdge fineL := (fs 0 0 0, 1)
theorem b01_fst : b01.1 = fs 0 0 0 := rfl

/-- Coarse bond `b20`: fine base `(0, 2, 0)`, direction `0`. -/
def b20 : PeriodicLatticeEdge fineL := (fs 0 2 0, 0)
theorem b20_fst : b20.1 = fs 0 2 0 := rfl

/-- Coarse bond `b21`: fine base `(2, 0, 0)`, direction `1`. -/
def b21 : PeriodicLatticeEdge fineL := (fs 2 0 0, 1)
theorem b21_fst : b21.1 = fs 2 0 0 := rfl

/-- Coarse bond `bw1`: fine base `(0, 6, 0)`, direction `1`. -/
def bw1 : PeriodicLatticeEdge fineL := (fs 0 6 0, 1)
theorem bw1_fst : bw1.1 = fs 0 6 0 := rfl

theorem block_b00 : stepBlockOf b00.1 1 2 = ({fs 0 0 0, fs 0 0 1, fs 0 1 0, fs 0 1 1, fs 1 0 0, fs 1 0 1, fs 1 1 0, fs 1 1 1} : Finset (PeriodicLatticeSite fineL)) :=
  block_of b00.1 (by decide) _ (by decide) (by decide)
theorem cplus_b00 : cPlusS 1 2 b00 = fs 2 0 0 := by decide
theorem rep_b00 : List.replicate 2 b00.2 = [(0 : Fin 3), 0] := by decide

theorem block_b01 : stepBlockOf b01.1 1 2 = ({fs 0 0 0, fs 0 0 1, fs 0 1 0, fs 0 1 1, fs 1 0 0, fs 1 0 1, fs 1 1 0, fs 1 1 1} : Finset (PeriodicLatticeSite fineL)) :=
  block_of b01.1 (by decide) _ (by decide) (by decide)
theorem cplus_b01 : cPlusS 1 2 b01 = fs 0 2 0 := by decide
theorem rep_b01 : List.replicate 2 b01.2 = [(1 : Fin 3), 1] := by decide

theorem block_b20 : stepBlockOf b20.1 1 2 = ({fs 0 2 0, fs 0 2 1, fs 0 3 0, fs 0 3 1, fs 1 2 0, fs 1 2 1, fs 1 3 0, fs 1 3 1} : Finset (PeriodicLatticeSite fineL)) :=
  block_of b20.1 (by decide) _ (by decide) (by decide)
theorem cplus_b20 : cPlusS 1 2 b20 = fs 2 2 0 := by decide
theorem rep_b20 : List.replicate 2 b20.2 = [(0 : Fin 3), 0] := by decide

theorem block_b21 : stepBlockOf b21.1 1 2 = ({fs 2 0 0, fs 2 0 1, fs 2 1 0, fs 2 1 1, fs 3 0 0, fs 3 0 1, fs 3 1 0, fs 3 1 1} : Finset (PeriodicLatticeSite fineL)) :=
  block_of b21.1 (by decide) _ (by decide) (by decide)
theorem cplus_b21 : cPlusS 1 2 b21 = fs 2 2 0 := by decide
theorem rep_b21 : List.replicate 2 b21.2 = [(1 : Fin 3), 1] := by decide

theorem block_bw1 : stepBlockOf bw1.1 1 2 = ({fs 0 6 0, fs 0 6 1, fs 0 7 0, fs 0 7 1, fs 1 6 0, fs 1 6 1, fs 1 7 0, fs 1 7 1} : Finset (PeriodicLatticeSite fineL)) :=
  block_of bw1.1 (by decide) _ (by decide) (by decide)
theorem cplus_bw1 : cPlusS 1 2 bw1 = fs 0 0 0 := by decide
theorem rep_bw1 : List.replicate 2 bw1.2 = [(1 : Fin 3), 1] := by decide

/-! ### the eight block loop angles at `b00` -/

theorem gam_b00_0 : coarseGammaPath 1 (fs 0 0 0) (fs 0 0 0) = [] := by decide
theorem gam_b00_1 : coarseGammaPath 1 (fs 0 0 0) (fs 0 0 1) = [(2 : Fin 3)] := by decide
theorem gam_b00_2 : coarseGammaPath 1 (fs 0 0 0) (fs 0 1 0) = [(1 : Fin 3)] := by decide
theorem gam_b00_3 : coarseGammaPath 1 (fs 0 0 0) (fs 0 1 1) = [(2 : Fin 3), (1 : Fin 3)] := by decide
theorem gam_b00_4 : coarseGammaPath 1 (fs 0 0 0) (fs 1 0 0) = [(0 : Fin 3)] := by decide
theorem gam_b00_5 : coarseGammaPath 1 (fs 0 0 0) (fs 1 0 1) = [(2 : Fin 3), (0 : Fin 3)] := by decide
theorem gam_b00_6 : coarseGammaPath 1 (fs 0 0 0) (fs 1 1 0) = [(1 : Fin 3), (0 : Fin 3)] := by decide
theorem gam_b00_7 : coarseGammaPath 1 (fs 0 0 0) (fs 1 1 1) = [(2 : Fin 3), (1 : Fin 3), (0 : Fin 3)] := by decide

theorem loop_b00_0 (t : ℝ) : loopAngle 1 2 (fSpike t) b00 (fs 0 0 0) = 0 := by
  unfold loopAngle bondAngle
  rw [b00_fst, gam_b00_0, cplus_b00, rep_b00]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b00_1 (t : ℝ) : loopAngle 1 2 (fSpike t) b00 (fs 0 0 1) = -t := by
  unfold loopAngle bondAngle
  rw [b00_fst, gam_b00_1, cplus_b00, rep_b00]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b00_2 (t : ℝ) : loopAngle 1 2 (fSpike t) b00 (fs 0 1 0) = -t := by
  unfold loopAngle bondAngle
  rw [b00_fst, gam_b00_2, cplus_b00, rep_b00]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b00_3 (t : ℝ) : loopAngle 1 2 (fSpike t) b00 (fs 0 1 1) = -t := by
  unfold loopAngle bondAngle
  rw [b00_fst, gam_b00_3, cplus_b00, rep_b00]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b00_4 (t : ℝ) : loopAngle 1 2 (fSpike t) b00 (fs 1 0 0) = 0 := by
  unfold loopAngle bondAngle
  rw [b00_fst, gam_b00_4, cplus_b00, rep_b00]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b00_5 (t : ℝ) : loopAngle 1 2 (fSpike t) b00 (fs 1 0 1) = -t := by
  unfold loopAngle bondAngle
  rw [b00_fst, gam_b00_5, cplus_b00, rep_b00]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b00_6 (t : ℝ) : loopAngle 1 2 (fSpike t) b00 (fs 1 1 0) = -t := by
  unfold loopAngle bondAngle
  rw [b00_fst, gam_b00_6, cplus_b00, rep_b00]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b00_7 (t : ℝ) : loopAngle 1 2 (fSpike t) b00 (fs 1 1 1) = -t := by
  unfold loopAngle bondAngle
  rw [b00_fst, gam_b00_7, cplus_b00, rep_b00]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring

theorem bondAngle_b00 (t : ℝ) : bondAngle 1 2 (fSpike t) b00 = t := by
  unfold bondAngle
  rw [b00_fst, rep_b00]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring

/-- **THE BLOCKED ANGLE AT `b00`: `1/4·t`.** -/
theorem blkAngle_b00 (t : ℝ) : blkAngle 1 2 (fSpike t) b00 = t / 4 := by
  unfold blkAngle
  rw [block_b00, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    loop_b00_0, loop_b00_1, loop_b00_2, loop_b00_3, loop_b00_4, loop_b00_5, loop_b00_6, loop_b00_7, bondAngle_b00]
  push_cast
  ring

theorem branch_b00 {t : ℝ} (ht : |t| < Real.pi) :
    ∀ x ∈ stepBlockOf b00.1 1 2, |loopAngle 1 2 (fSpike t) b00 x| < Real.pi := by
  intro x hx
  rw [block_b00] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [loop_b00_0, loop_b00_1, loop_b00_2, loop_b00_3, loop_b00_4, loop_b00_5, loop_b00_6, loop_b00_7, abs_zero, abs_neg] <;>
    first
      | exact Real.pi_pos
      | exact ht

/-- `Ū(U*_fine t)` at `b00`. -/
theorem ubar_at_b00 {t : ℝ} (ht : |t| < Real.pi) :
    ubarSU2 1 2 (UfineStar t) b00 = torus (t / 4) := by
  rw [UfineStar_eq_torusCfg, ubarSU2_torusCfg_abs 1 2 (fSpike t) b00 (branch_b00 ht),
    blkAngle_b00]

/-! ### the eight block loop angles at `b01` -/

theorem gam_b01_0 : coarseGammaPath 1 (fs 0 0 0) (fs 0 0 0) = [] := by decide
theorem gam_b01_1 : coarseGammaPath 1 (fs 0 0 0) (fs 0 0 1) = [(2 : Fin 3)] := by decide
theorem gam_b01_2 : coarseGammaPath 1 (fs 0 0 0) (fs 0 1 0) = [(1 : Fin 3)] := by decide
theorem gam_b01_3 : coarseGammaPath 1 (fs 0 0 0) (fs 0 1 1) = [(2 : Fin 3), (1 : Fin 3)] := by decide
theorem gam_b01_4 : coarseGammaPath 1 (fs 0 0 0) (fs 1 0 0) = [(0 : Fin 3)] := by decide
theorem gam_b01_5 : coarseGammaPath 1 (fs 0 0 0) (fs 1 0 1) = [(2 : Fin 3), (0 : Fin 3)] := by decide
theorem gam_b01_6 : coarseGammaPath 1 (fs 0 0 0) (fs 1 1 0) = [(1 : Fin 3), (0 : Fin 3)] := by decide
theorem gam_b01_7 : coarseGammaPath 1 (fs 0 0 0) (fs 1 1 1) = [(2 : Fin 3), (1 : Fin 3), (0 : Fin 3)] := by decide

theorem loop_b01_0 (t : ℝ) : loopAngle 1 2 (fSpike t) b01 (fs 0 0 0) = 0 := by
  unfold loopAngle bondAngle
  rw [b01_fst, gam_b01_0, cplus_b01, rep_b01]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b01_1 (t : ℝ) : loopAngle 1 2 (fSpike t) b01 (fs 0 0 1) = 0 := by
  unfold loopAngle bondAngle
  rw [b01_fst, gam_b01_1, cplus_b01, rep_b01]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b01_2 (t : ℝ) : loopAngle 1 2 (fSpike t) b01 (fs 0 1 0) = 0 := by
  unfold loopAngle bondAngle
  rw [b01_fst, gam_b01_2, cplus_b01, rep_b01]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b01_3 (t : ℝ) : loopAngle 1 2 (fSpike t) b01 (fs 0 1 1) = 0 := by
  unfold loopAngle bondAngle
  rw [b01_fst, gam_b01_3, cplus_b01, rep_b01]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b01_4 (t : ℝ) : loopAngle 1 2 (fSpike t) b01 (fs 1 0 0) = t := by
  unfold loopAngle bondAngle
  rw [b01_fst, gam_b01_4, cplus_b01, rep_b01]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b01_5 (t : ℝ) : loopAngle 1 2 (fSpike t) b01 (fs 1 0 1) = 0 := by
  unfold loopAngle bondAngle
  rw [b01_fst, gam_b01_5, cplus_b01, rep_b01]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b01_6 (t : ℝ) : loopAngle 1 2 (fSpike t) b01 (fs 1 1 0) = 0 := by
  unfold loopAngle bondAngle
  rw [b01_fst, gam_b01_6, cplus_b01, rep_b01]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b01_7 (t : ℝ) : loopAngle 1 2 (fSpike t) b01 (fs 1 1 1) = 0 := by
  unfold loopAngle bondAngle
  rw [b01_fst, gam_b01_7, cplus_b01, rep_b01]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring

theorem bondAngle_b01 (t : ℝ) : bondAngle 1 2 (fSpike t) b01 = 0 := by
  unfold bondAngle
  rw [b01_fst, rep_b01]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring

/-- **THE BLOCKED ANGLE AT `b01`: `1/8·t`.** -/
theorem blkAngle_b01 (t : ℝ) : blkAngle 1 2 (fSpike t) b01 = t / 8 := by
  unfold blkAngle
  rw [block_b01, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    loop_b01_0, loop_b01_1, loop_b01_2, loop_b01_3, loop_b01_4, loop_b01_5, loop_b01_6, loop_b01_7, bondAngle_b01]
  push_cast
  ring

theorem branch_b01 {t : ℝ} (ht : |t| < Real.pi) :
    ∀ x ∈ stepBlockOf b01.1 1 2, |loopAngle 1 2 (fSpike t) b01 x| < Real.pi := by
  intro x hx
  rw [block_b01] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [loop_b01_0, loop_b01_1, loop_b01_2, loop_b01_3, loop_b01_4, loop_b01_5, loop_b01_6, loop_b01_7, abs_zero, abs_neg] <;>
    first
      | exact Real.pi_pos
      | exact ht

/-- `Ū(U*_fine t)` at `b01`. -/
theorem ubar_at_b01 {t : ℝ} (ht : |t| < Real.pi) :
    ubarSU2 1 2 (UfineStar t) b01 = torus (t / 8) := by
  rw [UfineStar_eq_torusCfg, ubarSU2_torusCfg_abs 1 2 (fSpike t) b01 (branch_b01 ht),
    blkAngle_b01]

/-! ### the eight block loop angles at `b20` -/

theorem gam_b20_0 : coarseGammaPath 1 (fs 0 2 0) (fs 0 2 0) = [] := by decide
theorem gam_b20_1 : coarseGammaPath 1 (fs 0 2 0) (fs 0 2 1) = [(2 : Fin 3)] := by decide
theorem gam_b20_2 : coarseGammaPath 1 (fs 0 2 0) (fs 0 3 0) = [(1 : Fin 3)] := by decide
theorem gam_b20_3 : coarseGammaPath 1 (fs 0 2 0) (fs 0 3 1) = [(2 : Fin 3), (1 : Fin 3)] := by decide
theorem gam_b20_4 : coarseGammaPath 1 (fs 0 2 0) (fs 1 2 0) = [(0 : Fin 3)] := by decide
theorem gam_b20_5 : coarseGammaPath 1 (fs 0 2 0) (fs 1 2 1) = [(2 : Fin 3), (0 : Fin 3)] := by decide
theorem gam_b20_6 : coarseGammaPath 1 (fs 0 2 0) (fs 1 3 0) = [(1 : Fin 3), (0 : Fin 3)] := by decide
theorem gam_b20_7 : coarseGammaPath 1 (fs 0 2 0) (fs 1 3 1) = [(2 : Fin 3), (1 : Fin 3), (0 : Fin 3)] := by decide

theorem loop_b20_0 (t : ℝ) : loopAngle 1 2 (fSpike t) b20 (fs 0 2 0) = 0 := by
  unfold loopAngle bondAngle
  rw [b20_fst, gam_b20_0, cplus_b20, rep_b20]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b20_1 (t : ℝ) : loopAngle 1 2 (fSpike t) b20 (fs 0 2 1) = 0 := by
  unfold loopAngle bondAngle
  rw [b20_fst, gam_b20_1, cplus_b20, rep_b20]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b20_2 (t : ℝ) : loopAngle 1 2 (fSpike t) b20 (fs 0 3 0) = 0 := by
  unfold loopAngle bondAngle
  rw [b20_fst, gam_b20_2, cplus_b20, rep_b20]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b20_3 (t : ℝ) : loopAngle 1 2 (fSpike t) b20 (fs 0 3 1) = 0 := by
  unfold loopAngle bondAngle
  rw [b20_fst, gam_b20_3, cplus_b20, rep_b20]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b20_4 (t : ℝ) : loopAngle 1 2 (fSpike t) b20 (fs 1 2 0) = 0 := by
  unfold loopAngle bondAngle
  rw [b20_fst, gam_b20_4, cplus_b20, rep_b20]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b20_5 (t : ℝ) : loopAngle 1 2 (fSpike t) b20 (fs 1 2 1) = 0 := by
  unfold loopAngle bondAngle
  rw [b20_fst, gam_b20_5, cplus_b20, rep_b20]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b20_6 (t : ℝ) : loopAngle 1 2 (fSpike t) b20 (fs 1 3 0) = 0 := by
  unfold loopAngle bondAngle
  rw [b20_fst, gam_b20_6, cplus_b20, rep_b20]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b20_7 (t : ℝ) : loopAngle 1 2 (fSpike t) b20 (fs 1 3 1) = 0 := by
  unfold loopAngle bondAngle
  rw [b20_fst, gam_b20_7, cplus_b20, rep_b20]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring

theorem bondAngle_b20 (t : ℝ) : bondAngle 1 2 (fSpike t) b20 = 0 := by
  unfold bondAngle
  rw [b20_fst, rep_b20]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring

/-- **THE BLOCKED ANGLE AT `b20`: `0·t`.** -/
theorem blkAngle_b20 (t : ℝ) : blkAngle 1 2 (fSpike t) b20 = 0 := by
  unfold blkAngle
  rw [block_b20, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    loop_b20_0, loop_b20_1, loop_b20_2, loop_b20_3, loop_b20_4, loop_b20_5, loop_b20_6, loop_b20_7, bondAngle_b20]
  push_cast
  ring

theorem branch_b20 {t : ℝ} (ht : |t| < Real.pi) :
    ∀ x ∈ stepBlockOf b20.1 1 2, |loopAngle 1 2 (fSpike t) b20 x| < Real.pi := by
  intro x hx
  rw [block_b20] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [loop_b20_0, loop_b20_1, loop_b20_2, loop_b20_3, loop_b20_4, loop_b20_5, loop_b20_6, loop_b20_7, abs_zero, abs_neg] <;>
    first
      | exact Real.pi_pos
      | exact ht

/-- `Ū(U*_fine t)` at `b20`. -/
theorem ubar_at_b20 {t : ℝ} (ht : |t| < Real.pi) :
    ubarSU2 1 2 (UfineStar t) b20 = torus (0) := by
  rw [UfineStar_eq_torusCfg, ubarSU2_torusCfg_abs 1 2 (fSpike t) b20 (branch_b20 ht),
    blkAngle_b20]

/-! ### the eight block loop angles at `b21` -/

theorem gam_b21_0 : coarseGammaPath 1 (fs 2 0 0) (fs 2 0 0) = [] := by decide
theorem gam_b21_1 : coarseGammaPath 1 (fs 2 0 0) (fs 2 0 1) = [(2 : Fin 3)] := by decide
theorem gam_b21_2 : coarseGammaPath 1 (fs 2 0 0) (fs 2 1 0) = [(1 : Fin 3)] := by decide
theorem gam_b21_3 : coarseGammaPath 1 (fs 2 0 0) (fs 2 1 1) = [(2 : Fin 3), (1 : Fin 3)] := by decide
theorem gam_b21_4 : coarseGammaPath 1 (fs 2 0 0) (fs 3 0 0) = [(0 : Fin 3)] := by decide
theorem gam_b21_5 : coarseGammaPath 1 (fs 2 0 0) (fs 3 0 1) = [(2 : Fin 3), (0 : Fin 3)] := by decide
theorem gam_b21_6 : coarseGammaPath 1 (fs 2 0 0) (fs 3 1 0) = [(1 : Fin 3), (0 : Fin 3)] := by decide
theorem gam_b21_7 : coarseGammaPath 1 (fs 2 0 0) (fs 3 1 1) = [(2 : Fin 3), (1 : Fin 3), (0 : Fin 3)] := by decide

theorem loop_b21_0 (t : ℝ) : loopAngle 1 2 (fSpike t) b21 (fs 2 0 0) = 0 := by
  unfold loopAngle bondAngle
  rw [b21_fst, gam_b21_0, cplus_b21, rep_b21]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b21_1 (t : ℝ) : loopAngle 1 2 (fSpike t) b21 (fs 2 0 1) = 0 := by
  unfold loopAngle bondAngle
  rw [b21_fst, gam_b21_1, cplus_b21, rep_b21]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b21_2 (t : ℝ) : loopAngle 1 2 (fSpike t) b21 (fs 2 1 0) = 0 := by
  unfold loopAngle bondAngle
  rw [b21_fst, gam_b21_2, cplus_b21, rep_b21]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b21_3 (t : ℝ) : loopAngle 1 2 (fSpike t) b21 (fs 2 1 1) = 0 := by
  unfold loopAngle bondAngle
  rw [b21_fst, gam_b21_3, cplus_b21, rep_b21]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b21_4 (t : ℝ) : loopAngle 1 2 (fSpike t) b21 (fs 3 0 0) = 0 := by
  unfold loopAngle bondAngle
  rw [b21_fst, gam_b21_4, cplus_b21, rep_b21]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b21_5 (t : ℝ) : loopAngle 1 2 (fSpike t) b21 (fs 3 0 1) = 0 := by
  unfold loopAngle bondAngle
  rw [b21_fst, gam_b21_5, cplus_b21, rep_b21]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b21_6 (t : ℝ) : loopAngle 1 2 (fSpike t) b21 (fs 3 1 0) = 0 := by
  unfold loopAngle bondAngle
  rw [b21_fst, gam_b21_6, cplus_b21, rep_b21]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_b21_7 (t : ℝ) : loopAngle 1 2 (fSpike t) b21 (fs 3 1 1) = 0 := by
  unfold loopAngle bondAngle
  rw [b21_fst, gam_b21_7, cplus_b21, rep_b21]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring

theorem bondAngle_b21 (t : ℝ) : bondAngle 1 2 (fSpike t) b21 = 0 := by
  unfold bondAngle
  rw [b21_fst, rep_b21]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring

/-- **THE BLOCKED ANGLE AT `b21`: `0·t`.** -/
theorem blkAngle_b21 (t : ℝ) : blkAngle 1 2 (fSpike t) b21 = 0 := by
  unfold blkAngle
  rw [block_b21, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    loop_b21_0, loop_b21_1, loop_b21_2, loop_b21_3, loop_b21_4, loop_b21_5, loop_b21_6, loop_b21_7, bondAngle_b21]
  push_cast
  ring

theorem branch_b21 {t : ℝ} (ht : |t| < Real.pi) :
    ∀ x ∈ stepBlockOf b21.1 1 2, |loopAngle 1 2 (fSpike t) b21 x| < Real.pi := by
  intro x hx
  rw [block_b21] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [loop_b21_0, loop_b21_1, loop_b21_2, loop_b21_3, loop_b21_4, loop_b21_5, loop_b21_6, loop_b21_7, abs_zero, abs_neg] <;>
    first
      | exact Real.pi_pos
      | exact ht

/-- `Ū(U*_fine t)` at `b21`. -/
theorem ubar_at_b21 {t : ℝ} (ht : |t| < Real.pi) :
    ubarSU2 1 2 (UfineStar t) b21 = torus (0) := by
  rw [UfineStar_eq_torusCfg, ubarSU2_torusCfg_abs 1 2 (fSpike t) b21 (branch_b21 ht),
    blkAngle_b21]

/-! ### the eight block loop angles at `bw1` -/

theorem gam_bw1_0 : coarseGammaPath 1 (fs 0 6 0) (fs 0 6 0) = [] := by decide
theorem gam_bw1_1 : coarseGammaPath 1 (fs 0 6 0) (fs 0 6 1) = [(2 : Fin 3)] := by decide
theorem gam_bw1_2 : coarseGammaPath 1 (fs 0 6 0) (fs 0 7 0) = [(1 : Fin 3)] := by decide
theorem gam_bw1_3 : coarseGammaPath 1 (fs 0 6 0) (fs 0 7 1) = [(2 : Fin 3), (1 : Fin 3)] := by decide
theorem gam_bw1_4 : coarseGammaPath 1 (fs 0 6 0) (fs 1 6 0) = [(0 : Fin 3)] := by decide
theorem gam_bw1_5 : coarseGammaPath 1 (fs 0 6 0) (fs 1 6 1) = [(2 : Fin 3), (0 : Fin 3)] := by decide
theorem gam_bw1_6 : coarseGammaPath 1 (fs 0 6 0) (fs 1 7 0) = [(1 : Fin 3), (0 : Fin 3)] := by decide
theorem gam_bw1_7 : coarseGammaPath 1 (fs 0 6 0) (fs 1 7 1) = [(2 : Fin 3), (1 : Fin 3), (0 : Fin 3)] := by decide

theorem loop_bw1_0 (t : ℝ) : loopAngle 1 2 (fSpike t) bw1 (fs 0 6 0) = 0 := by
  unfold loopAngle bondAngle
  rw [bw1_fst, gam_bw1_0, cplus_bw1, rep_bw1]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_bw1_1 (t : ℝ) : loopAngle 1 2 (fSpike t) bw1 (fs 0 6 1) = 0 := by
  unfold loopAngle bondAngle
  rw [bw1_fst, gam_bw1_1, cplus_bw1, rep_bw1]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_bw1_2 (t : ℝ) : loopAngle 1 2 (fSpike t) bw1 (fs 0 7 0) = 0 := by
  unfold loopAngle bondAngle
  rw [bw1_fst, gam_bw1_2, cplus_bw1, rep_bw1]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_bw1_3 (t : ℝ) : loopAngle 1 2 (fSpike t) bw1 (fs 0 7 1) = 0 := by
  unfold loopAngle bondAngle
  rw [bw1_fst, gam_bw1_3, cplus_bw1, rep_bw1]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_bw1_4 (t : ℝ) : loopAngle 1 2 (fSpike t) bw1 (fs 1 6 0) = -t := by
  unfold loopAngle bondAngle
  rw [bw1_fst, gam_bw1_4, cplus_bw1, rep_bw1]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_bw1_5 (t : ℝ) : loopAngle 1 2 (fSpike t) bw1 (fs 1 6 1) = 0 := by
  unfold loopAngle bondAngle
  rw [bw1_fst, gam_bw1_5, cplus_bw1, rep_bw1]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_bw1_6 (t : ℝ) : loopAngle 1 2 (fSpike t) bw1 (fs 1 7 0) = 0 := by
  unfold loopAngle bondAngle
  rw [bw1_fst, gam_bw1_6, cplus_bw1, rep_bw1]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring
theorem loop_bw1_7 (t : ℝ) : loopAngle 1 2 (fSpike t) bw1 (fs 1 7 1) = 0 := by
  unfold loopAngle bondAngle
  rw [bw1_fst, gam_bw1_7, cplus_bw1, rep_bw1]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring

theorem bondAngle_bw1 (t : ℝ) : bondAngle 1 2 (fSpike t) bw1 = 0 := by
  unfold bondAngle
  rw [bw1_fst, rep_bw1]
  simp +decide [fSpike, fs, fineBond, fineOrigin] <;> ring

/-- **THE BLOCKED ANGLE AT `bw1`: `-1/8·t`.** -/
theorem blkAngle_bw1 (t : ℝ) : blkAngle 1 2 (fSpike t) bw1 = -(t / 8) := by
  unfold blkAngle
  rw [block_bw1, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    loop_bw1_0, loop_bw1_1, loop_bw1_2, loop_bw1_3, loop_bw1_4, loop_bw1_5, loop_bw1_6, loop_bw1_7, bondAngle_bw1]
  push_cast
  ring

theorem branch_bw1 {t : ℝ} (ht : |t| < Real.pi) :
    ∀ x ∈ stepBlockOf bw1.1 1 2, |loopAngle 1 2 (fSpike t) bw1 x| < Real.pi := by
  intro x hx
  rw [block_bw1] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [loop_bw1_0, loop_bw1_1, loop_bw1_2, loop_bw1_3, loop_bw1_4, loop_bw1_5, loop_bw1_6, loop_bw1_7, abs_zero, abs_neg] <;>
    first
      | exact Real.pi_pos
      | exact ht

/-- `Ū(U*_fine t)` at `bw1`. -/
theorem ubar_at_bw1 {t : ℝ} (ht : |t| < Real.pi) :
    ubarSU2 1 2 (UfineStar t) bw1 = torus (-(t / 8)) := by
  rw [UfineStar_eq_torusCfg, ubarSU2_torusCfg_abs 1 2 (fSpike t) bw1 (branch_bw1 ht),
    blkAngle_bw1]


/-! ## §7 — THE FACTS -/

theorem torus_ne_one {θ : ℝ} (h0 : 0 < θ) (hpi : θ < 2 * Real.pi) : torus θ ≠ 1 := by
  intro hEq
  have hf : frobNorm ((torus θ : M2) - 1) = 0 := by
    rw [hEq]
    show frobNorm (((1 : SU2) : M2) - 1) = 0
    rw [AdalyFormal.Balaban.SuTwoLogExp.coe_one, sub_self]
    exact AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero
  rw [frobNorm_torus_sub_one, sqrt_four_one_sub_cos] at hf
  have hs : Real.sin (θ / 2) > 0 := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h8 : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  rw [abs_of_pos hs] at hf
  nlinarith

/-- **FACT 1 — THE BLOCKED SPIKE IS NOT A SINGLE-LINK SPIKE.** -/
theorem blocked_not_single_bond {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    ubarSU2 1 2 (UfineStar t) b00 ≠ 1 ∧ ubarSU2 1 2 (UfineStar t) b01 ≠ 1 ∧ b00 ≠ b01 := by
  have habs : |t| < Real.pi := by rw [abs_of_pos ht]; exact htpi
  have hpi := Real.pi_pos
  refine ⟨?_, ?_, by decide⟩
  · rw [ubar_at_b00 habs]
    exact torus_ne_one (by linarith) (by linarith)
  · rw [ubar_at_b01 habs]
    exact torus_ne_one (by linarith) (by linarith)

/-- **FACT 1b — THE TIE IS NOT BLOCK-LOCAL.** `bw1` is a bond of a coarse block that does not
contain the spike, and the blocked background is non-trivial there. -/
theorem blocked_nonlocal_support {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    ubarSU2 1 2 (UfineStar t) bw1 ≠ 1 := by
  have habs : |t| < Real.pi := by rw [abs_of_pos ht]; exact htpi
  have hpi := Real.pi_pos
  rw [ubar_at_bw1 habs]
  intro hEq
  have h2 : torus (t / 8) = 1 := by
    have := congrArg (fun g : SU2 => g⁻¹) hEq
    simpa [torus_inv, neg_neg] using this
  exact torus_ne_one (by linarith) (by linarith) h2

/-- **FACT 2 — THE SPIKE IS DAMPED AT ITS OWN BOND.** Exact identity, not an inequality. -/
theorem blocked_deviation_at_own_bond {t : ℝ} (ht : |t| < Real.pi) :
    frobNorm (((ubarSU2 1 2 (UfineStar t) b00 : SU2) : M2) - 1)
      = Real.sqrt (4 * (1 - Real.cos (t / 4)))
    ∧ frobNorm (((UfineStar t fineBond : SU2) : M2) - 1)
      = Real.sqrt (4 * (1 - Real.cos t)) := by
  constructor
  · rw [ubar_at_b00 ht, frobNorm_torus_sub_one]
  · rw [show UfineStar t fineBond = torus t from spikeAt_self fineBond (torus t),
      frobNorm_torus_sub_one]

/-- **FACT 3 — THE BLOCKED BACKGROUND IS CURVED ON THE COARSE PLAQUETTE AT THE ORIGIN.** -/
theorem blocked_curved_at_coarse_plaquette {t : ℝ} (ht : 0 < t) (htpi : t < Real.pi) :
    ubarSU2 1 2 (UfineStar t) b00 * ubarSU2 1 2 (UfineStar t) b21
        * (ubarSU2 1 2 (UfineStar t) b20)⁻¹ * (ubarSU2 1 2 (UfineStar t) b01)⁻¹
      = torus (t / 8)
    ∧ torus (t / 8) ≠ 1 := by
  have habs : |t| < Real.pi := by rw [abs_of_pos ht]; exact htpi
  have hpi := Real.pi_pos
  refine ⟨?_, torus_ne_one (by linarith) (by linarith)⟩
  rw [ubar_at_b00 habs, ubar_at_b01 habs, ubar_at_b20 habs, ubar_at_b21 habs]
  rw [torus_inv, torus_inv, ← torus_add, ← torus_add, ← torus_add]
  congr 1
  ring


/-! ## §8 — axiom audit -/

#print axioms su2Angle_torus_neg
#print axioms su2Log_torus_abs
#print axioms ubarSU2_torusCfg_abs
#print axioms fSpike
#print axioms UfineStar_eq_torusCfg
#print axioms fs
#print axioms fs_origin
#print axioms block_of
#print axioms b00
#print axioms b00_fst
#print axioms block_b00
#print axioms cplus_b00
#print axioms rep_b00
#print axioms gam_b00_0
#print axioms gam_b00_1
#print axioms gam_b00_2
#print axioms gam_b00_3
#print axioms gam_b00_4
#print axioms gam_b00_5
#print axioms gam_b00_6
#print axioms gam_b00_7
#print axioms loop_b00_0
#print axioms loop_b00_1
#print axioms loop_b00_2
#print axioms loop_b00_3
#print axioms loop_b00_4
#print axioms loop_b00_5
#print axioms loop_b00_6
#print axioms loop_b00_7
#print axioms bondAngle_b00
#print axioms blkAngle_b00
#print axioms branch_b00
#print axioms ubar_at_b00
#print axioms b01
#print axioms b01_fst
#print axioms block_b01
#print axioms cplus_b01
#print axioms rep_b01
#print axioms gam_b01_0
#print axioms gam_b01_1
#print axioms gam_b01_2
#print axioms gam_b01_3
#print axioms gam_b01_4
#print axioms gam_b01_5
#print axioms gam_b01_6
#print axioms gam_b01_7
#print axioms loop_b01_0
#print axioms loop_b01_1
#print axioms loop_b01_2
#print axioms loop_b01_3
#print axioms loop_b01_4
#print axioms loop_b01_5
#print axioms loop_b01_6
#print axioms loop_b01_7
#print axioms bondAngle_b01
#print axioms blkAngle_b01
#print axioms branch_b01
#print axioms ubar_at_b01
#print axioms b20
#print axioms b20_fst
#print axioms block_b20
#print axioms cplus_b20
#print axioms rep_b20
#print axioms gam_b20_0
#print axioms gam_b20_1
#print axioms gam_b20_2
#print axioms gam_b20_3
#print axioms gam_b20_4
#print axioms gam_b20_5
#print axioms gam_b20_6
#print axioms gam_b20_7
#print axioms loop_b20_0
#print axioms loop_b20_1
#print axioms loop_b20_2
#print axioms loop_b20_3
#print axioms loop_b20_4
#print axioms loop_b20_5
#print axioms loop_b20_6
#print axioms loop_b20_7
#print axioms bondAngle_b20
#print axioms blkAngle_b20
#print axioms branch_b20
#print axioms ubar_at_b20
#print axioms b21
#print axioms b21_fst
#print axioms block_b21
#print axioms cplus_b21
#print axioms rep_b21
#print axioms gam_b21_0
#print axioms gam_b21_1
#print axioms gam_b21_2
#print axioms gam_b21_3
#print axioms gam_b21_4
#print axioms gam_b21_5
#print axioms gam_b21_6
#print axioms gam_b21_7
#print axioms loop_b21_0
#print axioms loop_b21_1
#print axioms loop_b21_2
#print axioms loop_b21_3
#print axioms loop_b21_4
#print axioms loop_b21_5
#print axioms loop_b21_6
#print axioms loop_b21_7
#print axioms bondAngle_b21
#print axioms blkAngle_b21
#print axioms branch_b21
#print axioms ubar_at_b21
#print axioms bw1
#print axioms bw1_fst
#print axioms block_bw1
#print axioms cplus_bw1
#print axioms rep_bw1
#print axioms gam_bw1_0
#print axioms gam_bw1_1
#print axioms gam_bw1_2
#print axioms gam_bw1_3
#print axioms gam_bw1_4
#print axioms gam_bw1_5
#print axioms gam_bw1_6
#print axioms gam_bw1_7
#print axioms loop_bw1_0
#print axioms loop_bw1_1
#print axioms loop_bw1_2
#print axioms loop_bw1_3
#print axioms loop_bw1_4
#print axioms loop_bw1_5
#print axioms loop_bw1_6
#print axioms loop_bw1_7
#print axioms bondAngle_bw1
#print axioms blkAngle_bw1
#print axioms branch_bw1
#print axioms ubar_at_bw1
#print axioms torus_ne_one
#print axioms blocked_not_single_bond
#print axioms blocked_nonlocal_support
#print axioms blocked_deviation_at_own_bond
#print axioms blocked_curved_at_coarse_plaquette

end AdalyFormal.SpikeBlocked
