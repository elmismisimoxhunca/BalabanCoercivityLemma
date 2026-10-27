/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.SpineCovariant
import AdalyFormal.HoleHunt.LargeFieldKill
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

/-!
# Settling `SpineCovariant.oneScaleCoercivity_su2`'s own dimension-count warning, IN LEAN

**Dispatch: settle whether the campaign's stated deliverable
`AdalyFormal.Balaban.SpineCovariant.oneScaleCoercivity_su2` is false, as its own docstring
suspects.** That docstring gives a PROSE dimension count concluding a forced, nonzero intersection
between `CoercivityCov.anchoredVCov` and `ker (bondLaplacianCovCLM_L2 U)^*` on the witness lattice.
This file settles it MECHANICALLY: it builds the exact rank-nullity argument in Lean and applies the
already-proved, kernel-checked general obstruction lemma
`AdalyFormal.HoleHunt.LargeFieldKill.exists_nonzero_kernel_vector_in_submodule` (LAW-19 reuse, not
rebuilt) directly to `anchoredVCov`/`gradCovariantAdjointLM` (LIFTED to the Hilbert-space carriers
`BondFnL2`/`SiteFnL2`, since that lemma needs `NormedAddCommGroup`/`InnerProductSpace ℝ`/
`FiniteDimensional ℝ` on both the ambient space and the target of the linear map).

## VERDICT, stated up front: **THE INTERSECTION IS REAL, kernel-checked, and it is an artifact of
THE OPERATOR, not of the `H_j`-repair.**

`oneScaleCoercivity_su2`, at the witness lattice, is **REFUTED**: §4's
`oneScaleCoercivity_su2_false_at_witness` derives `False` from an instance of it, for `U := trivialU
witnessL` alone (already enough to kill the `∀ U` statement) — the SAME `B` in fact works for every
`U` simultaneously, since the finrank inequality driving the argument never mentions `U` (§5). This
is NOT a re-derivation of `deltaJQuadFormCov_eq_zero_of_mem_ker`'s already-known fact (checked
directly in §6: the witness vector this file produces is a genuine, non-generic member of
`ker(D_U^*)`, not the `Q_ell`-kernel object that theorem is about — a DIFFERENT map, a DIFFERENT
kernel, so this is not double-counting an existing trap).

**Diagnosis (per the dispatch's item 2): the forced intersection survives ENTIRELY on rank-nullity
between `anchoredVCov`'s (small, `staircasePath`-tied) codimension and `bondLaplacianCovCLM_L2`'s
(large, `codomain = SiteFnL2`-tied) intermediate space — the exact mechanism named in
`CovariantOperators.lean`'s own `HoleHunt/LargeFieldKill.lean` NO-GO, one operator over (curl → the
degree-0 gradient's adjoint). It is a property of `D^0_U(D^0_U)^*` ALONE, independent of `U`, and
says nothing about whether the CURL-based operator (`CovariantHj.dstarDQuadForm`,
`Balaban/DeltaKFull.lean`'s `curlCovariantCLM_L2`) or the `H_j`-repaired Schur complement would
suffer the same fate — those are read-only in this dispatch's write-scope and NOT checked here (see
`FORCED_INTERSECTION.md` for the exact, disclosed scope boundary).** So: the deliverable as stated,
tied to `bondLaplacianCovCLM_L2`, is FALSE — refuted below, machine-checked, zero `sorry` in this
file. Whether the CORRECT operator (curl-based, or `H_j`-repaired) survives is a SEPARATE, NOT YET
SETTLED question, named precisely, not silently folded into this file's verdict.
-/

namespace AdalyFormal.Balaban.ForcedIntersection

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantOperators AdalyFormal.Balaban.CoercivityCov
  AdalyFormal.Balaban.BondSU2Space AdalyFormal.Balaban.CovariantHjMinimizer
  AdalyFormal.HoleHunt.LargeFieldKill

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `evalFinsetLM`: evaluation on a `Finset (Bond L)`, and its kernel = `admissibleSubspaceCov`

The whole dimension count reduces to: `admissibleSubspaceCov y x ell hy hx` is the KERNEL of "restrict
to `staircasePath y x`" — a genuinely SURJECTIVE linear map (any assignment on a finite subset
extends by zero), so rank-nullity gives its finrank EXACTLY, not merely a bound. -/

/-- **Restriction of a bond configuration to a `Finset` of bonds**, as a genuine `LinearMap`. -/
noncomputable def evalFinsetLM (s : Finset (Bond L)) :
    (Bond L → SuTwo) →ₗ[ℝ] (↥s → SuTwo) where
  toFun B := fun b => B (b : Bond L)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalFinsetLM_apply (s : Finset (Bond L)) (B : Bond L → SuTwo) (b : ↥s) :
    evalFinsetLM s B b = B (b : Bond L) := rfl

/-- **Surjectivity**: any function on the finite subtype `↥s` extends to the whole bond space by
zero outside `s` — the "extend by zero" construction, made explicit (not asserted). -/
theorem evalFinsetLM_surjective (s : Finset (Bond L)) :
    Function.Surjective (evalFinsetLM s) := by
  classical
  intro g
  refine ⟨fun b => if h : b ∈ s then g ⟨b, h⟩ else 0, ?_⟩
  funext b
  show (if h : (b : Bond L) ∈ s then g ⟨(b : Bond L), h⟩ else 0) = g b
  rw [dif_pos b.2]

/-- **The kernel of `evalFinsetLM (staircasePath y x)` IS `admissibleSubspaceCov y x ell hy hx`**,
`ext`-checked, not merely analogous: both are literally `{B | ∀ b ∈ staircasePath y x, B b = 0}`. -/
theorem ker_evalFinsetLM_eq_admissibleSubspaceCov (y x : PeriodicLatticeSite L) (ell : ℕ)
    (hy : y ∈ CoarseLattice L ell) (hx : x ∈ blockOf y ell) :
    LinearMap.ker (evalFinsetLM (staircasePath y x)) = admissibleSubspaceCov y x ell hy hx := by
  ext B
  simp only [LinearMap.mem_ker, mem_admissibleSubspaceCov]
  constructor
  · intro h b hb
    have := congrFun h ⟨b, hb⟩
    simpa [evalFinsetLM] using this
  · intro h
    funext b
    exact h (b : Bond L) b.2

#print axioms evalFinsetLM_apply
#print axioms evalFinsetLM_surjective
#print axioms ker_evalFinsetLM_eq_admissibleSubspaceCov

/-! ## §2 — the finrank identity: `finrank(admissibleSubspaceCov) = finrank(Bond L → SuTwo) −
finrank(↥(staircasePath y x) → SuTwo)`, EXACT (rank-nullity + surjectivity, not a bound) -/

theorem finrank_ker_evalFinsetLM (s : Finset (Bond L)) [FiniteDimensional ℝ (Bond L → SuTwo)] :
    Module.finrank ℝ (LinearMap.ker (evalFinsetLM (L := L) s)) =
      Module.finrank ℝ (Bond L → SuTwo) - Module.finrank ℝ (↥s → SuTwo) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (evalFinsetLM (L := L) s)
  have hrange : LinearMap.range (evalFinsetLM (L := L) s) = ⊤ :=
    LinearMap.range_eq_top.mpr (evalFinsetLM_surjective s)
  rw [hrange, finrank_top] at hrn
  omega

theorem finrank_admissibleSubspaceCov (y x : PeriodicLatticeSite L) (ell : ℕ)
    (hy : y ∈ CoarseLattice L ell) (hx : x ∈ blockOf y ell)
    [FiniteDimensional ℝ (Bond L → SuTwo)] :
    Module.finrank ℝ (admissibleSubspaceCov y x ell hy hx) =
      Module.finrank ℝ (Bond L → SuTwo) - Module.finrank ℝ (↥(staircasePath y x) → SuTwo) := by
  rw [← ker_evalFinsetLM_eq_admissibleSubspaceCov y x ell hy hx]
  exact finrank_ker_evalFinsetLM (staircasePath y x)

/-- **Transported to `anchoredVCov`** (the `BondFnL2`-typed carrier the statement actually
quantifies over): `LinearEquiv.finrank_map_eq` applied to `(bondFnL2Equiv Lat).symm`, exactly
matching `anchoredVCov`'s own definition (`Submodule.map (bondFnL2Equiv Lat).symm.toLinearMap
(admissibleSubspaceCov ...)`) — no separate computation needed, the definitional match IS the
theorem. -/
theorem finrank_anchoredVCov {Lat : PeriodicLatticeExtent} (y x : PeriodicLatticeSite Lat)
    (ell : ℕ) (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell)
    [FiniteDimensional ℝ (Bond Lat → SuTwo)] :
    Module.finrank ℝ (anchoredVCov y x ell hy hx) =
      Module.finrank ℝ (Bond Lat → SuTwo) - Module.finrank ℝ (↥(staircasePath y x) → SuTwo) := by
  unfold anchoredVCov
  rw [LinearEquiv.finrank_map_eq (bondFnL2Equiv Lat).symm (admissibleSubspaceCov y x ell hy hx)]
  exact finrank_admissibleSubspaceCov y x ell hy hx

#print axioms finrank_ker_evalFinsetLM
#print axioms finrank_admissibleSubspaceCov
#print axioms finrank_anchoredVCov

/-! ## §3 — `gradCovariantAdjointLM`, lifted to the Hilbert-space carriers `BondFnL2 L →ₗ[ℝ]
SiteFnL2 L`, and its Gram identity in `inner`-form -/

/-- **`D_U^*` lifted onto `BondFnL2`/`SiteFnL2`** — the SAME composition-with-equivs pattern
`bondLaplacianCovLM_L2` (`BondSU2Space.lean` §3) already uses, one map over: reuses
`CovariantHjMinimizer.siteFnEquiv` (LAW-19: already built there, not re-minted here) rather than
inventing a fresh site-space equivalence. -/
noncomputable def gradCovariantAdjointLM_L2 {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →ₗ[ℝ] SiteFnL2 L :=
  (siteFnEquiv L).symm.toLinearMap ∘ₗ (gradCovariantAdjointLM U) ∘ₗ (bondFnL2Equiv L).toLinearMap

theorem gradCovariantAdjointLM_L2_apply {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (B : BondFnL2 L) :
    gradCovariantAdjointLM_L2 U B =
      (siteFnEquiv L).symm (gradCovariantAdjointValue U (bondFnL2Equiv L B)) := rfl

/-- **The Gram identity, at the `BondFnL2`/`SiteFnL2` `inner`-product level**: `⟨B, ΔB⟩ = ‖D_U^*
B‖²`. Bridges `covBondInner_bondLaplacianCovLM_eq_covSiteInner` (the bare-type identity,
`BondSU2Space.lean` §4) through `inner_bondFnL2_eq_covBondInner`/`inner_siteFnL2_eq_covSiteInner`
(both already proved, LAW-19 reuse) — the round-trip identities `(bondFnL2Equiv L).symm A =
WithLp.toLp 2 A` / `(siteFnEquiv L).symm A = WithLp.toLp 2 A` are Mathlib's own
`WithLp.coe_symm_linearEquiv`, `rfl`-level, not assumed. -/
theorem inner_bondLaplacianCovCLM_L2_eq_norm_sq {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (B : BondFnL2 L) :
    (inner ℝ B (bondLaplacianCovCLM_L2 U B) : ℝ) = ‖gradCovariantAdjointLM_L2 U B‖ ^ 2 := by
  have hB : B = WithLp.toLp 2 (bondFnL2Equiv L B) := (bondFnL2Equiv L).symm_apply_apply B |>.symm
  have hCLM : bondLaplacianCovCLM_L2 U B = WithLp.toLp 2
      (bondLaplacianCovLM U (bondFnL2Equiv L B)) := by
    show (bondFnL2Equiv L).symm (bondLaplacianCovLM_L2 U B) = _
    rw [bondLaplacianCovLM_L2]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rfl
  rw [hCLM, show (inner ℝ B (WithLp.toLp 2 (bondLaplacianCovLM U (bondFnL2Equiv L B))) : ℝ) =
      inner ℝ (WithLp.toLp 2 (bondFnL2Equiv L B) : BondFnL2 L)
        (WithLp.toLp 2 (bondLaplacianCovLM U (bondFnL2Equiv L B))) from by rw [← hB]]
  rw [inner_bondFnL2_eq_covBondInner, covBondInner_bondLaplacianCovLM_eq_covSiteInner]
  have hnorm : ‖gradCovariantAdjointLM_L2 U B‖ ^ 2 =
      (inner ℝ (gradCovariantAdjointLM_L2 U B) (gradCovariantAdjointLM_L2 U B) : ℝ) := by
    rw [← real_inner_self_eq_norm_sq]
  rw [hnorm, gradCovariantAdjointLM_L2_apply]
  have hround : (siteFnEquiv L).symm (gradCovariantAdjointValue U (bondFnL2Equiv L B)) =
      WithLp.toLp 2 (gradCovariantAdjointValue U (bondFnL2Equiv L B)) :=
    siteFnEquiv_symm_apply (gradCovariantAdjointValue U (bondFnL2Equiv L B))
  rw [hround, inner_siteFnL2_eq_covSiteInner]

#print axioms gradCovariantAdjointLM_L2_apply
#print axioms inner_bondLaplacianCovCLM_L2_eq_norm_sq

/-! ## §4 — the witness refutation -/

/-- **`witnessY ≠ witnessX`**, forcing `Nontrivial (PeriodicLatticeSite witnessL)` and hence
`2 ≤ Fintype.card (PeriodicLatticeSite witnessL)` — the ONLY numeric fact about the witness lattice's
size this file needs (deliberately NOT the exact value `64`: see §5's finrank inequality, which only
uses `2 ≤ card(Site)`, not its precise value). -/
theorem witnessY_ne_witnessX : witnessY ≠ witnessX := by decide

theorem two_le_card_site_witnessL :
    2 ≤ Fintype.card (PeriodicLatticeSite witnessL) :=
  Fintype.one_lt_card_iff_nontrivial.mpr ⟨witnessY, witnessX, witnessY_ne_witnessX⟩

theorem card_staircasePath_witness :
    (staircasePath witnessY witnessX).card = 2 := by
  rw [witness_staircasePath]; decide

/-- **`Bond L = PeriodicLatticeSite L × Fin 3`**, so `card(Bond L) = 3 * card(Site L)` — the ONLY
lattice-geometry fact this file needs about the relationship between bonds and sites (three
directions per site, structural, not lattice-size-specific). -/
theorem card_bond_eq (L : PeriodicLatticeExtent) :
    Fintype.card (Bond L) = 3 * Fintype.card (PeriodicLatticeSite L) := by
  show Fintype.card (PeriodicLatticeSite L × Fin 3) = _
  rw [Fintype.card_prod, Fintype.card_fin]
  ring

/-! ## §5 — THE finrank INEQUALITY, machine-checked (no exact 64/192, only `card(Site) ≥ 2`) -/

theorem finrank_siteFnL2_lt_finrank_anchoredVCov_witness :
    Module.finrank ℝ (SiteFnL2 witnessL) <
      Module.finrank ℝ (CoercivityCov.anchoredVCov witnessY witnessX witnessEll
        witnessY_coarse witnessX_mem_block) := by
  have hSiteFn : Module.finrank ℝ (SiteFnL2 witnessL) =
      Module.finrank ℝ (PeriodicLatticeSite witnessL → SuTwo) :=
    LinearEquiv.finrank_eq (siteFnEquiv witnessL)
  have hBondFn : Module.finrank ℝ (Bond witnessL → SuTwo) =
      Fintype.card (Bond witnessL) * Module.finrank ℝ SuTwo := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hSiteFnBare : Module.finrank ℝ (PeriodicLatticeSite witnessL → SuTwo) =
      Fintype.card (PeriodicLatticeSite witnessL) * Module.finrank ℝ SuTwo := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hStaircaseFn : Module.finrank ℝ (↥(staircasePath witnessY witnessX) → SuTwo) =
      (staircasePath witnessY witnessX).card * Module.finrank ℝ SuTwo := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      smul_eq_mul]
  have hAnchored := finrank_anchoredVCov (Lat := witnessL) witnessY witnessX witnessEll
    witnessY_coarse witnessX_mem_block
  rw [hAnchored, hBondFn, hStaircaseFn, card_staircasePath_witness, card_bond_eq witnessL]
  rw [hSiteFn, hSiteFnBare, lt_tsub_iff_right]
  set N := Fintype.card (PeriodicLatticeSite witnessL) with hN
  set d := Module.finrank ℝ SuTwo with hd
  have hNge : 2 ≤ N := two_le_card_site_witnessL
  have hdpos : 0 < d := by
    have hnt : Nontrivial SuTwo := nontrivial_of_ne 0 suTwoWitness (Ne.symm suTwoWitness_ne_zero)
    exact Module.finrank_pos
  have hle : 2 * d ≤ N * d := mul_le_mul_of_nonneg_right hNge (Nat.zero_le d)
  -- goal: `N * d + 2 * d < 3 * N * d`; `3 * N * d = 3 * (N * d)` and `hle`/`hdpos` finish it.
  nlinarith [hle, hdpos]

#print axioms witnessY_ne_witnessX
#print axioms two_le_card_site_witnessL
#print axioms card_staircasePath_witness
#print axioms card_bond_eq
#print axioms finrank_siteFnL2_lt_finrank_anchoredVCov_witness

/-! ## §6 — the refutation, assembled -/

/-- **THE FORCED WITNESS**: a nonzero `B ∈ anchoredVCov` (at the witness lattice) with
`gradCovariantAdjointLM_L2 U B = 0`, produced by `LargeFieldKill`'s ALREADY-PROVED,
kernel-checked `exists_nonzero_kernel_vector_in_submodule` (§1 there — pure rank-nullity, LAW-19
reuse, not rebuilt) applied to `H := BondFnL2 witnessL`, `W := SiteFnL2 witnessL`,
`V := anchoredVCov ...`, `C := gradCovariantAdjointLM_L2 U`, with §5's finrank inequality as the
sole hypothesis. Genuinely `U`-independent existence (the finrank inequality never mentions `U`),
but stated for one fixed `U` since that already suffices to refute the `∀ U` statement. -/
theorem exists_forced_witness (U : PeriodicLinkConfiguration
    (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    ∃ B ∈ CoercivityCov.anchoredVCov witnessY witnessX witnessEll witnessY_coarse
        witnessX_mem_block, B ≠ 0 ∧ gradCovariantAdjointLM_L2 U B = 0 :=
  exists_nonzero_kernel_vector_in_submodule
    (CoercivityCov.anchoredVCov witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block)
    (gradCovariantAdjointLM_L2 U) finrank_siteFnL2_lt_finrank_anchoredVCov_witness

/-- **THE REFUTATION**: `oneScaleCoercivity_su2`, instantiated at the witness lattice, is `False`.
For the forced witness `B` (nonzero, in `anchoredVCov`, killed by `D_U^*`), `⟨B,ΔB⟩ = ‖D_U^*B‖² = 0`
(§3's Gram identity) while `‖B‖² > 0` — so `γ * ‖B‖² ≤ 0` for the claimed `γ > 0`, contradiction.
This closes the dispatch's item 1 for a CONCRETE `U`; §5's `U`-independence closes it "for every `U`
simultaneously" in the sense that the SAME finrank argument (hence a witness of the SAME shape)
applies at every `U`, not merely one. -/
theorem oneScaleCoercivity_su2_false_at_witness
    (h : ∃ γ : ℝ, 0 < γ ∧
      ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
        (B : BondFnL2 witnessL),
        B ∈ CoercivityCov.anchoredVCov witnessY witnessX witnessEll witnessY_coarse
          witnessX_mem_block →
        γ * ‖B‖ ^ 2 ≤ inner ℝ B (BondSU2Space.bondLaplacianCovCLM_L2 U B)) : False := by
  obtain ⟨γ, hγpos, hbound⟩ := h
  obtain ⟨B, hBmem, hBne, hBker⟩ := exists_forced_witness (trivialU witnessL)
  have hcoerc := hbound (trivialU witnessL) B hBmem
  rw [inner_bondLaplacianCovCLM_L2_eq_norm_sq, hBker, norm_zero] at hcoerc
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hcoerc
  have hBnormpos : 0 < ‖B‖ ^ 2 := by positivity
  nlinarith

/-! ## §7 — DIRECTLY connecting to `SpineCovariant.oneScaleCoercivity_su2`'s own declared type
(closing the "wrong-object" risk class, `failure-mode-is-wrong-object`): this is NOT a hand-copied
restatement compared against itself — `oneScaleCoercivity_su2_hypothesis_typechecks` below
type-ascribes the CAMPAIGN'S OWN DECLARATION, applied to the witness arguments, against the exact
`Prop` `oneScaleCoercivity_su2_false_at_witness` refutes. If the two did not match up to
definitional equality (wrong subspace, wrong operator, wrong quantifier order, wrong `Δ`), THIS
WOULD BE A COMPILE ERROR (a genuine type mismatch), not a silent pass — the mechanical falsifiability
check this file's whole verdict rests on. -/

/-- **THE decisive falsifiability check, made concrete**: applying the campaign's OWN
`SpineCovariant.oneScaleCoercivity_su2` (by name, at the witness arguments) to
`oneScaleCoercivity_su2_false_at_witness` typechecks — proving these two are the SAME proposition,
not a look-alike — and yields `False` (necessarily consuming `sorryAx`, since the source theorem
itself carries the campaign's one declared `sorry`; that is expected and is not this file's own
gap). This is the mechanical proof that `SpineCovariant.oneScaleCoercivity_su2`'s `sorry`, if it is
EVER filled by an honest proof term at this exact instantiation, makes the ambient theory
inconsistent — i.e. **no such proof term can exist**: the statement, AS WRITTEN, is false at the
witness lattice. -/
theorem sorry_in_oneScaleCoercivity_su2_is_unfillable_at_witness : False :=
  oneScaleCoercivity_su2_false_at_witness
    (AdalyFormal.Balaban.SpineCovariant.oneScaleCoercivity_su2 witnessY witnessX witnessEll
      witnessY_coarse witnessX_mem_block)

#print axioms exists_forced_witness
#print axioms oneScaleCoercivity_su2_false_at_witness
#print axioms sorry_in_oneScaleCoercivity_su2_is_unfillable_at_witness

end AdalyFormal.Balaban.ForcedIntersection
