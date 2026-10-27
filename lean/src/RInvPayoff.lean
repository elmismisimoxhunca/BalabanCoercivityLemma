/-
# `RInvPayoff.lean` — THE COMPOSED RIGHT INVERSE, `‖H₁‖`, AND A **CURVED** FINE WITNESS.

LANE `compute/qsurj_rinverse/`.  Write scope: that directory only.  Never `lake build`.

`QSurjRInverse.lean` built `R_U : CoarseFnL2 L ell →L[ℝ] BondFnL2 L` with
`qCLM U ell ∘L R_U = id` at EVERY background and `‖R_U‖ = ell³`, a number that does not mention
`U`.  This file spends it, in the order `compute/terminal_binder/SCOPE.md` §4 lays out.

1. **§1 — through the extent identification.**  `composedQ h Ufine = coarseFnL2Equiv h ∘L qCLM Ufine ell`
   with `coarseFnL2Equiv h` a `LinearIsometryEquiv`, so `R := R_U ∘L (coarseFnL2Equiv h).symm`
   interpolates `composedQ` and inherits `‖R‖ = ell³` EXACTLY.
2. **§2 — `‖H₁‖ ≤ √(ell⁶+1)`**, by `TerminalBinder.norm_H1_le_of_rightInverse_bound` (REUSED).
3. **§3 — the product line becomes a pure smallness condition on the FINE deviation**, in closed
   form with every factor named.
4. **§4 — a GENUINELY CURVED fine background that meets it**, with `0 < frobSupBond U_fine` proved,
   on a concrete non-degenerate tower (`8³` fine, `4³` coarse, `ell = ell₀ = 2`), and the upstream
   general-fine terminal theorem instantiated there with `hsmallFine` DISCHARGED.

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.
-/
import QSurjRInverse
import TerminalBinder

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.longLine false

noncomputable section

namespace QSurjRInverse

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.BridgeInverse (qCLM CoarseFnL2)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.VariationalProjectorH1 (solutionOperator)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg
  frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq frobNorm_nonneg)
open AdalyFormal.Balaban.NonFlatBackground (rotElem rotElem_coe rotM frobSq_rotM_sub_one
  nonflatU_defect_le sqrt_eight_mul_sq)
open AdalyFormal.MechEdges.G16 (rawErrorCoeff rawErrorCoeff_nonneg)
open AdalyFormal.HrawCarriers (ScaleQuotient ell_pos_of_scale dvd_of_scale coarseFnL2Equiv
  composedQ composedQ_apply)
open AdalyFormal.TerminalBinder (feedDatumGen norm_H1_le_of_rightInverse_bound
  hsmallFine_of_alphaFine_small terminal_at_composed_carriers_generalFine)

variable {L L' : PeriodicLatticeExtent}

/-! ## §1 — THE RIGHT INVERSE OF `composedQ`, WITH ITS NORM

`composedQ` = block average on the FINER torus, then the extent identification.  The identification
is an isometry, so it changes nothing but the index set. -/

/-- **`R` for `composedQ`**: the corner-line section pulled back through the extent
identification. -/
def rInvComposed {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L' →L[ℝ] BondFnL2 L :=
  (rInv Ufine (ell_pos_of_scale h)).comp
    ((coarseFnL2Equiv h).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem rInvComposed_apply {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : BondFnL2 L') :
    rInvComposed h Ufine B = rInv Ufine (ell_pos_of_scale h) ((coarseFnL2Equiv h).symm B) := rfl

/-- **`composedQ ∘ R = id` AT EVERY FINE BACKGROUND.** -/
theorem composedQ_rInvComposed {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : BondFnL2 L') : composedQ h Ufine (rInvComposed h Ufine B) = B := by
  rw [composedQ_apply, rInvComposed_apply,
    qCLM_rInv_apply Ufine (ell_pos_of_scale h) (dvd_of_scale h) ((coarseFnL2Equiv h).symm B)]
  exact (coarseFnL2Equiv h).apply_symm_apply B

theorem norm_rInvComposed_apply {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : BondFnL2 L') : ‖rInvComposed h Ufine B‖ = ((ell : ℝ) ^ 3) * ‖B‖ := by
  rw [rInvComposed_apply,
    norm_rInv_apply Ufine (ell_pos_of_scale h) (dvd_of_scale h) ((coarseFnL2Equiv h).symm B),
    (coarseFnL2Equiv h).symm.norm_map B]

/-- **`‖R‖ = ell³` for `composedQ` too — still no `U_fine` on the right-hand side.** -/
theorem opNorm_rInvComposed {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ‖rInvComposed h Ufine‖ = (ell : ℝ) ^ 3 := by
  have hell := ell_pos_of_scale h
  have hpos : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (fun B => le_of_eq (norm_rInvComposed_apply h Ufine B))) ?_
  -- attained: transport the `CoarseFnL2` witness through the isometry
  set F : CoarseFnL2 L ell := WithLp.toLp 2
    (fun _ => AdalyFormal.Balaban.CovariantOperators.suTwoWitness) with hF
  have hFne : F ≠ 0 := by
    intro hcon
    have hval := congrFun (congrArg (fun u : CoarseFnL2 L ell => WithLp.ofLp u) hcon)
      (Classical.arbitrary (CoarseBond L ell))
    simp only [hF, WithLp.ofLp_toLp] at hval
    exact AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero (by simpa using hval)
  set B : BondFnL2 L' := coarseFnL2Equiv h F with hB
  have hBne : B ≠ 0 := by
    intro hcon
    exact hFne (by simpa [hB] using congrArg (fun u => (coarseFnL2Equiv h).symm u) hcon)
  have hBpos : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hBne
  have heq := norm_rInvComposed_apply h Ufine B
  have hle : ‖rInvComposed h Ufine B‖ ≤ ‖rInvComposed h Ufine‖ * ‖B‖ :=
    (rInvComposed h Ufine).le_opNorm B
  rw [heq] at hle
  exact le_of_mul_le_mul_right (by linarith [hle]) hBpos

/-- **TRANSPORT-UNIFORMITY AT THE COMPOSED OPERATOR**, stated as a comparison so that no reader has
to infer it from the absence of `U_fine` in the previous right-hand side. -/
theorem opNorm_rInvComposed_transport_uniform {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine Vfine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ‖rInvComposed h Ufine‖ = ‖rInvComposed h Vfine‖ := by
  rw [opNorm_rInvComposed h Ufine, opNorm_rInvComposed h Vfine]

/-! ## §2 — `‖H₁‖ ≤ √(ell⁶+1)` -/

/-- The `ε`-condition of `norm_H1_le_of_rightInverse_bound` is always satisfiable — `ε` is a free
parameter of the datum, so it costs nothing.  Exhibited rather than asserted. -/
theorem exists_eps_big {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {a : ℝ}
    (ha : 0 ≤ a) :
    ∃ eps : ℝ, 0 < eps ∧
      ‖(curlCovariantCLM_L2 Ufine).comp (rInvComposed h Ufine)‖ ^ 2 + a ≤ eps := by
  refine ⟨‖(curlCovariantCLM_L2 Ufine).comp (rInvComposed h Ufine)‖ ^ 2 + a + 1, ?_, by linarith⟩
  have : (0 : ℝ) ≤ ‖(curlCovariantCLM_L2 Ufine).comp (rInvComposed h Ufine)‖ ^ 2 := sq_nonneg _
  linarith

/-- **THE `‖H₁‖` BOUND, TRANSPORT-UNIFORM.**  The right-hand side is a function of `ell` alone: it
mentions neither `U_fine` nor any operator norm of the datum. -/
theorem norm_H1_le_transport_uniform {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a)
    (hbig : ‖(curlCovariantCLM_L2 Ufine).comp (rInvComposed h Ufine)‖ ^ 2 + a ≤ eps) :
    ‖solutionOperator (feedDatumGen h Ufine heps ha)‖ ≤ Real.sqrt ((ell : ℝ) ^ 6 + 1) := by
  have hb := norm_H1_le_of_rightInverse_bound h Ufine heps ha (rInvComposed h Ufine)
    (composedQ_rInvComposed h Ufine) hbig
  rwa [opNorm_rInvComposed h Ufine, show ((ell : ℝ) ^ 3) ^ 2 = (ell : ℝ) ^ 6 by ring] at hb

/-! ## §3 — THE PRODUCT LINE, AS A PURE SMALLNESS CONDITION ON THE FINE DEVIATION

`terminal_at_composed_carriers_generalFine`'s new hypothesis is the PRODUCT
`‖H₁‖ · rawErrorCoeff ℓ U_fine ≤ 1/(2356·ℓ₀³)`, and §4 of `terminal_binder/SCOPE.md` records that
it could not be turned into a condition on `α₁(U_fine)` alone because `‖H₁‖` itself depends on
`U_fine`.  §2 removes that dependence, so the conversion now goes through. -/

/-- **THE CLOSED-FORM FINE-SIDE CONDITION.**

    α₁(U_fine)  ≤  √ℓ / ( 2356 · 36√2 · (√(ℓ⁶+1) + 1) · ℓ₀³ )   ⟹   the product line holds.

Every factor is derived: `2356 = 4·589` and `36√2` are `TerminalBinder`'s
(`rawErrorCoeff ℓ U = (36√2/√ℓ)·α₁(U)`), and `√(ℓ⁶+1)` is §2's transport-uniform `‖H₁‖` bound. -/
theorem hsmallFine_of_alphaFine_transport_uniform {ell ell₀ : ℕ} (h : ScaleQuotient L ell L')
    (hell₀ : 0 < ell₀)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {eps a : ℝ} (heps : 0 < eps) (ha : 0 ≤ a)
    (hbig : ‖(curlCovariantCLM_L2 Ufine).comp (rInvComposed h Ufine)‖ ^ 2 + a ≤ eps)
    (hα : frobSupBond Ufine ≤ Real.sqrt (ell : ℝ)
      / (2356 * (36 * Real.sqrt 2) * (Real.sqrt ((ell : ℝ) ^ 6 + 1) + 1) * (ell₀ : ℝ) ^ 3)) :
    ‖solutionOperator (feedDatumGen h Ufine heps ha)‖ * rawErrorCoeff ell Ufine
      ≤ 1 / (2356 * (ell₀ : ℝ) ^ 3) := by
  have hell : 0 < ell := ell_pos_of_scale h
  have hK : (0 : ℝ) ≤ Real.sqrt ((ell : ℝ) ^ 6 + 1) := Real.sqrt_nonneg _
  have hKbound := hsmallFine_of_alphaFine_small (L := L) hell hell₀ Ufine
    (Real.sqrt ((ell : ℝ) ^ 6 + 1)) hK hα
  have hH1 := norm_H1_le_transport_uniform h Ufine heps ha hbig
  have hre : (0 : ℝ) ≤ rawErrorCoeff ell Ufine := rawErrorCoeff_nonneg ell Ufine
  exact le_trans (mul_le_mul_of_nonneg_right hH1 hre) hKbound

/-! ## §4 — A GENUINELY CURVED FINE BACKGROUND THAT MEETS IT

`terminal_binder/SCOPE.md` §4 names this as the item the lane did not close.  Two things are
needed and both are supplied: a background with `frobSupBond > 0` (so the row is not the flat
instance in disguise — S82), and the exact arithmetic verifying the threshold. -/

/-- A one-bond spike on an ARBITRARY extent.  This is `NormalizedCounterexampleSearch.singleBondU`
with the extent freed — that `def` is pinned to `AdmissibleSubspace.witnessL` (a `4³` torus), which
is too small to satisfy `terminal_at_composed_carriers_generalFine`'s `hstrict : ell₀ < L' ν + 1`
after a block quotient.  Nothing else is new: the `frobSq` computation below is
`NonFlatBackground.frobSq_rotM_sub_one`, REUSED. -/
def spikeU (e₀ : Bond L) (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L :=
  fun e => if e = e₀ then X else 1

theorem spikeU_at (e₀ : Bond L) (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    spikeU e₀ X e₀ = X := by simp [spikeU]

theorem spikeU_elsewhere (e₀ : Bond L) (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) {e : Bond L}
    (h : e ≠ e₀) : spikeU e₀ X e = 1 := by simp [spikeU, h]

theorem frobSq_one_sub_one : frobSq (((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0 := by
  have h : ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1 = 0 := by
    simp
  rw [h]
  simp [frobSq]

/-- **`α₁` OF THE SPIKE IS THE SPIKE'S OWN FROBENIUS DEVIATION** — no volume, no multiplicity. -/
theorem frobSupBond_spikeU (e₀ : Bond L) (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    frobSupBond (spikeU e₀ X) = frobNorm ((X : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  refine le_antisymm (Finset.sup'_le _ _ (fun b _ => ?_)) ?_
  · by_cases hb : b = e₀
    · rw [hb, spikeU_at]
    · rw [spikeU_elsewhere e₀ X hb, frobNorm, frobSq_one_sub_one, Real.sqrt_zero]
      exact frobNorm_nonneg _
  · have hle := frobNorm_le_frobSupBond (spikeU e₀ X) e₀
    rwa [spikeU_at] at hle

/-- **THE CURVED FINE BACKGROUND.**  `α₁ = √(8t²/(1+t²))`, EXACTLY — strictly positive for every
`t ≠ 0` and `→ 0` as `t → 0`, so the smallness class is populated by genuinely curved fields. -/
theorem frobSupBond_spike_rot (e₀ : Bond L) (t : ℝ) :
    frobSupBond (spikeU e₀ (rotElem t)) = Real.sqrt (8 * t ^ 2 / (1 + t ^ 2)) := by
  rw [frobSupBond_spikeU, rotElem_coe, frobNorm, frobSq_rotM_sub_one]

theorem frobSupBond_spike_rot_pos (e₀ : Bond L) {t : ℝ} (ht : t ≠ 0) :
    0 < frobSupBond (spikeU e₀ (rotElem t)) := by
  rw [frobSupBond_spike_rot]
  refine Real.sqrt_pos.mpr ?_
  have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have h2 : (0 : ℝ) < 8 * t ^ 2 := by positivity
  positivity

theorem frobSupBond_spike_rot_le (e₀ : Bond L) (t : ℝ) :
    frobSupBond (spikeU e₀ (rotElem t)) ≤ 2 * Real.sqrt 2 * |t| := by
  rw [frobSupBond_spike_rot, ← sqrt_eight_mul_sq]
  exact Real.sqrt_le_sqrt (nonflatU_defect_le t)

/-! ### §4a — THE CONCRETE NON-DEGENERATE TOWER

Fine torus `8³` (`L = 7`), block scale `ell = 2`, coarse torus `4³` (`L' = 3`), `ell₀ = 2`.
`hstrict : ell₀ < L' ν + 1` reads `2 < 4` — TRUE, so the instance below is NOT one of the
degenerate binder points `milestone_binders_admit_degenerate_points` warns about. -/

/-- The fine extent: an `8³` periodic torus. -/
def fineExt : PeriodicLatticeExtent := fun _ => 7

/-- The coarse extent: a `4³` periodic torus — `AdmissibleSubspace.witnessL`. -/
def coarseExt : PeriodicLatticeExtent := fun _ => 3

theorem scale8to4 : ScaleQuotient fineExt 2 coarseExt := by
  intro μ; rfl

theorem coarse_ell0_strict : ∀ ν : Fin 3, 2 < coarseExt ν + 1 := by
  intro ν; simp [coarseExt]

theorem coarse_ell0_dvd : ∀ ν : Fin 3, (2 : ℕ) ∣ (coarseExt ν + 1) := by
  intro ν; exact ⟨2, rfl⟩

/-- A fine bond of the `8³` torus, to carry the spike. -/
def spikeBond : Bond fineExt := ((fun _ => (0 : Fin 8)), (0 : Fin 3))

/-- **THE CURVED FINE BACKGROUND OF THE WITNESS.**  `t = 10⁻⁸`. -/
def curvedFine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) fineExt :=
  spikeU spikeBond (rotElem (1 / 100000000))

/-- **IT IS GENUINELY CURVED.**  `α₁(U_fine) > 0`, so no statement below is the flat instance. -/
theorem curvedFine_curved : 0 < frobSupBond curvedFine :=
  frobSupBond_spike_rot_pos spikeBond (by norm_num)

theorem curvedFine_ne_trivial : curvedFine ≠ trivialU fineExt := by
  intro hc
  have h0 : frobSupBond curvedFine = 0 := by
    rw [hc]
    exact AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU fineExt
  exact absurd h0 (ne_of_gt curvedFine_curved)

theorem sqrt65_le_nine : Real.sqrt ((2 : ℝ) ^ 6 + 1) ≤ 9 := by
  have h : ((2 : ℝ) ^ 6 + 1) ≤ 9 ^ 2 := by norm_num
  calc Real.sqrt ((2 : ℝ) ^ 6 + 1) ≤ Real.sqrt (9 ^ 2) := Real.sqrt_le_sqrt h
    _ = 9 := Real.sqrt_sq (by norm_num)

theorem sqrt_two_le_three_halves : Real.sqrt 2 ≤ 3 / 2 := by
  have h : (2 : ℝ) ≤ (3 / 2) ^ 2 := by norm_num
  calc Real.sqrt 2 ≤ Real.sqrt ((3 / 2) ^ 2) := Real.sqrt_le_sqrt h
    _ = 3 / 2 := Real.sqrt_sq (by norm_num)

theorem one_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt 2 := by
  have h : Real.sqrt 1 ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
  rwa [Real.sqrt_one] at h

/-- **THE THRESHOLD IS MET, IN EXACT ARITHMETIC.**  The §3 condition at `ℓ = 2`, `ℓ₀ = 2` reads

    α₁(U_fine) ≤ √2 / (2356 · 36√2 · (√65 + 1) · 8)  =  1 / (678528 · (√65 + 1)),

and `√65 + 1 ≤ 10` gives a right-hand side `≥ 1/6785280`, while
`α₁(curvedFine) ≤ 2√2·10⁻⁸ ≤ 3·10⁻⁸` and `3 · 6785280 = 20355840 ≤ 10⁸`. -/
theorem curvedFine_meets_threshold :
    frobSupBond curvedFine ≤ Real.sqrt ((2 : ℕ) : ℝ)
      / (2356 * (36 * Real.sqrt 2)
        * (Real.sqrt ((((2 : ℕ) : ℝ)) ^ 6 + 1) + 1) * (((2 : ℕ) : ℝ)) ^ 3) := by
  have hcast : (((2 : ℕ)) : ℝ) = 2 := by norm_num
  rw [hcast]
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := sqrt_two_le_three_halves
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := one_le_sqrt_two
  have h65 : Real.sqrt ((2 : ℝ) ^ 6 + 1) ≤ 9 := sqrt65_le_nine
  have h65nn : (0 : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ 6 + 1) := Real.sqrt_nonneg _
  -- the left-hand side
  have hlhs : frobSupBond curvedFine ≤ 2 * Real.sqrt 2 * (1 / 100000000) := by
    have h := frobSupBond_spike_rot_le spikeBond (1 / 100000000 : ℝ)
    rwa [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 100000000)] at h
  have hlhs2 : frobSupBond curvedFine ≤ 3 / 100000000 := by
    have : 2 * Real.sqrt 2 * (1 / 100000000 : ℝ) ≤ 3 / 100000000 := by nlinarith [hs2]
    linarith [hlhs]
  -- the right-hand side
  have hden : (0 : ℝ) < 2356 * (36 * Real.sqrt 2) * (Real.sqrt ((2 : ℝ) ^ 6 + 1) + 1) * 2 ^ 3 := by
    positivity
  have hrhs : (3 : ℝ) / 100000000
      ≤ Real.sqrt 2 / (2356 * (36 * Real.sqrt 2) * (Real.sqrt ((2 : ℝ) ^ 6 + 1) + 1) * 2 ^ 3) := by
    rw [le_div_iff₀ hden]
    have h10 : Real.sqrt ((2 : ℝ) ^ 6 + 1) + 1 ≤ 10 := by linarith [h65]
    have hA : (2035584 / 100000000 : ℝ) * (Real.sqrt ((2 : ℝ) ^ 6 + 1) + 1) ≤ 1 := by
      have hm := mul_le_mul_of_nonneg_left h10 (by norm_num : (0:ℝ) ≤ 2035584 / 100000000)
      linarith [hm]
    calc (3 : ℝ) / 100000000
          * (2356 * (36 * Real.sqrt 2) * (Real.sqrt ((2 : ℝ) ^ 6 + 1) + 1) * 2 ^ 3)
        = ((2035584 / 100000000 : ℝ) * (Real.sqrt ((2 : ℝ) ^ 6 + 1) + 1)) * Real.sqrt 2 := by ring
      _ ≤ 1 * Real.sqrt 2 := mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 := one_mul _
  linarith [hlhs2, hrhs]

/-! ### §4b — THE UPSTREAM GENERAL-FINE THEOREM, INSTANTIATED AT A CURVED FINE BACKGROUND

The twin of `TerminalBinder.terminal_generalFine_at_flat_fine`, at nonzero fine curvature.  Every
binder of `terminal_at_composed_carriers_generalFine` is retained VERBATIM except `hsmallFine`,
which is DISCHARGED here, and the structural tiling hypotheses `hell2`/`hstrict`/`hdvd0`, which are
discharged by the concrete tower.  `hbig` is a condition on the free datum parameter `eps` alone
(`exists_eps_big` shows it is always satisfiable). -/
theorem terminal_at_curved_fine
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) coarseExt)
    (hsmallU : frobSupBond U ≤ 1 / (13336 * ((2 : ℕ) : ℝ) ^ 3))
    (bc : AdalyFormal.Balaban.ConstantA.BaseConstant) {eps : ℝ} (heps : 0 < eps)
    (hbig : ‖(curlCovariantCLM_L2 curvedFine).comp (rInvComposed scale8to4 curvedFine)‖ ^ 2
      + bc.a ≤ eps)
    (Qext : BondFnL2 coarseExt → BondFnL2 coarseExt)
    (T : BondFnL2 coarseExt →L[ℝ] BondFnL2 fineExt)
    (S : BondFnL2 coarseExt →L[ℝ] BondFnL2 coarseExt)
    (hS : AdalyFormal.Balaban.DeltaKWiring.IsSourceOperator
      (feedDatumGen scale8to4 curvedFine heps (le_of_lt bc.a_pos)) Qext
      (T (AdalyFormal.Balaban.SourceWiredJ.JsuTwo U)) S)
    (c₂ : ℝ) (hc₂ : 0 < c₂)
    (hD2 : ∀ B : BondFnL2 coarseExt,
      ‖AdalyFormal.Balaban.SourceJ.Dtilde2Shape Qext B‖ ≤ c₂ * ‖B‖ ^ 2)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hU : AdalyFormal.Balaban.SourceWired.LinkDev δ U)
    (hH1 : 0 < ‖solutionOperator (feedDatumGen scale8to4 curvedFine heps (le_of_lt bc.a_pos))‖)
    (hT : 0 < ‖T‖) (hcard : 0 < Fintype.card (Bond coarseExt))
    (hδ : δ < 1 / (1370001600 * ((2 : ℕ) : ℝ) ^ 6
      * (AdalyFormal.MechEdges.G16.rawSigmaZero 2) ^ 2
      * ‖solutionOperator (feedDatumGen scale8to4 curvedFine heps (le_of_lt bc.a_pos))‖ * c₂
      * (‖T‖ * Real.sqrt (2 * (Fintype.card (Bond coarseExt))))))
    (w : AdalyFormal.Balaban.ConstructCDC.TildeFn coarseExt 2)
    (hw : w ≠ 0) :
    0 < AdalyFormal.Balaban.DeltaKWiring.cdcFormTrue
      (feedDatumGen scale8to4 curvedFine heps (le_of_lt bc.a_pos)) bc Qext
      (T (AdalyFormal.Balaban.SourceWiredJ.JsuTwo U)) U 2
      (AdalyFormal.Balaban.FullReparamC.dinvC U 2) w := by
  have hsmallFine :
      ‖solutionOperator (feedDatumGen scale8to4 curvedFine heps (le_of_lt bc.a_pos))‖
        * rawErrorCoeff 2 curvedFine ≤ 1 / (2356 * ((2 : ℕ) : ℝ) ^ 3) :=
    hsmallFine_of_alphaFine_transport_uniform (ell₀ := 2) scale8to4 (by norm_num) curvedFine heps
      (le_of_lt bc.a_pos) hbig curvedFine_meets_threshold
  exact terminal_at_composed_carriers_generalFine scale8to4 curvedFine (by norm_num)
    coarse_ell0_strict coarse_ell0_dvd U hsmallU bc heps hsmallFine Qext T S hS c₂ hc₂ hD2 δ hδ0 hU
    hH1 hT hcard hδ w hw

/-- **THE NON-VACUITY CLAUSE, SEPARATE AND EXPLICIT (S82).**  The background of §4b is not the flat
one, and its deviation is strictly positive — so `rawErrorCoeff 2 curvedFine > 0` is not the
`rawErrorCoeff ℓ 1 = 0` row that makes `hsmallFine` free. -/
theorem curvedFine_rawErrorCoeff_pos : 0 < rawErrorCoeff 2 curvedFine := by
  have hre : rawErrorCoeff 2 curvedFine
      = (36 * Real.sqrt 2 / Real.sqrt ((2 : ℕ) : ℝ)) * frobSupBond curvedFine := rfl
  rw [hre]
  have h1 : (0 : ℝ) < 36 * Real.sqrt 2 / Real.sqrt ((2 : ℕ) : ℝ) := by
    have hs : (0 : ℝ) < Real.sqrt ((2 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  exact mul_pos h1 curvedFine_curved

end QSurjRInverse
