/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DeltaKSuTwoCarrier

set_option autoImplicit false

/-!
# `DeltaKSuTwoFaithful.lean` — `J(U)` ON THE su(2) CARRIER, LOSSLESSLY, AND THE `k`-FAMILY THAT
CONSUMES IT

Additive module. No existing file is edited.

## §0 — WHAT THIS FILE ADDS, AND WHAT IT DOES NOT

`SourceJFaithful.lean` established that `J` is a function of `U` and then recorded, as an explicit
residual, that its transport to the goal's real-per-bond carrier is LOSSY **on a dimension count**:
`Bond L → Matrix (Fin 2) (Fin 2) ℂ` is `8·|Bond L|` real dimensions, `AnchoredBondSpace L` is
`|Bond L|`, so *no* injective map exists there at all, and *"a lossless `J` needs the `su(2)`-valued
carrier."*

**THAT QUOTED RESIDUAL IS WRONG TWICE, and a blind de-correlated prosecution convicted it on
2026-07-30. Both corrections are recorded here rather than left to the reader:**

1. **The missing word is `linear`.** Dimension forbids a real-**LINEAR** injection. Set-theoretically
   `ℝ⁸` and `ℝ` have the same cardinality, so even `ℝ⁸ → ℝ` admits a bijection; "no injective map
   exists at all" is false as written. The claim is true only as *no real-linear injection exists*.
2. **The sufficiency conclusion does not follow either.** A NON-injective encoding can be perfectly
   sufficient when the consumed pairings see only a quotient — and `SourceJFaithful`'s own `imEntry01`
   is exactly such a projection, sufficient to separate `witnessU` from `trivialU` and to carry its
   scalar no-go. So a different carrier is forced ONLY IF the requirement is a structure-preserving,
   lossless *linear* representation of arbitrary physical `J`.

The residual's arithmetic (`4` complex = `8` real) is correct; its ambient figure is simply not the
relevant one, which is the point this file makes. Both the missing-`linear` defect and the ambient-vs-
intended dimension gap were reached independently by two model families from opposite directions.

This file supplies the lossless carrier as a theorem rather than a hope, and the sharp fact is that the
ambient `8`-per-bond figure is not the relevant one:

* **§2 — `Jsource U b` is HERMITIAN and TRACELESS at every bond, every `U`, every `L`**
  (`Jsource_mem_hermTraceless`). This is derived through the construction — `imHolonomy` Hermitian,
  `piProj` Hermitian-preserving and trace-killing, `conjByAmbient` by a special-unitary element
  Hermitian- and trace-preserving — not assumed.
* **§3 — multiplication by `i` is an `ℝ`-linear ISOMORPHISM `hermTraceless ≃ₗ[ℝ] 𝔰𝔲(2)`**
  (`hermTracelessEquivSuTwo`). So `J`'s values live in a space isomorphic to the fibre of
  `BondFnL2`, and the transport is invertible: `Jsource U b = (-i)·(JsourceSu U b)`
  (`JsourceSu_recovers`). **Losslessness is stated as a recovery EQUATION, never as an adjective.**
* **§7 — `Module.finrank ℝ SuTwo = 3`, proved.** `VolumeScalingV.lean` §residuals records that this
  value *"is NOT proved anywhere in this tree (only `2 ≤` …)"*. It is proved here from an explicit
  basis, which is what makes the dimension count SHARP: the su(2) carrier is `3·|Bond L|` real
  dimensions and `hermTraceless` is `3`-dimensional too, so §3's map is an isomorphism onto the
  whole fibre and not merely an injection into it.

**What this file does NOT do, said before anything else.** It does not build an RG ladder. There is
no `Δ_k` ladder in this tree: `DeltaKSuTwoCarrier.lean` §1.5 records that the `k`-fold composition
(3.15) is not typable here (no Lean encoding of CMP98's blocked configuration `Ū`), and a separate
audit (`compute/CITATION_AUDIT_CONFIRM.md` §B1, page-image read, STATUS CONFIRMED) established that
**CMP96 itself contains no derivation of its (2.128) from (2.123)+(2.127) anywhere in that paper** —
Lemma 2.4 is stated straight after the sentence *"The inequalities (2.123) and (2.127) imply many
other inequalities"* with no intervening algebra, and is then invoked as established at CMP96
(2.153); CMP99b in turn cites it as established, which is LAW-12's pattern and a SEPARATE fact from
the one above. Meanwhile this tree's own `BlockPoincareLemma24` measures naive global aggregation as
short by a factor `~ell`. Every `k`-quantifier below is a quantifier over the
`ℕ`-indexed family `deltaKTowerCLM`, which is (3.19)'s CLOSED FORM at block side `ell ^ k` — not
over a ladder of successive renormalisation steps, because no such ladder exists here. **§6 proves
the naive `∀k`-uniform statement on the WHOLE space is FALSE**, and §6c proves the subspace-relative
version is junk-inhabited at `V = ⊥`; those two theorems are the honest brackets around what can be
formed, and nothing here is billed as p.428's quantitative composite.

## §1 — THE SOURCE, WITH LOCATORS

The object `J` is CMP99b (3.11), printed p.392. `SourceJFaithful.lean` §THE SOURCE carries the
image-verified VERBATIM quote and its render hash
(`compute/sourcej_faithful/renders/CMP99b_p392-04.png`, sha256
`667c0360125b438b9cf55ce2ae2ed5b53b4fdf57c6aad8e8090fa96568502e5e`, byte-identical to
`corpus/pages/CMP99b_p392.md`'s recorded `render_sha256`). **That corpus page carries
`verification_status: single-read`**, so per the LAW-11 correction it is a lead and not the
adjudicated citable layer; the reading below therefore rests on the PAGE IMAGE, which is why the
render hash travels with the quote:

> "`⟨A, J⟩ = Σ_{b ⊂ T_η} η^d tr A(b)J(b),`   (3.11)
>  where `J = D*η^{-2} Im ∂U`, `(∂U)(p) = U(∂p)`."

Two structural facts about that formula are what §2 proves, and both are visible in the display
itself rather than inferred:

1. **`Im ∂U` is HERMITIAN**, because `Im X := (X − X^{-1})/2i` for a unitary `X` (this tree's
   `DeltaPrime.imHolonomy` is exactly `(1/(2i))·(W − W⁻¹)` with `W = U(∂p) ∈ SU(2)`, so
   `W⁻¹ = W^†`). `SourceJ.lean`'s own docstring for `DstarDir` states the same fact and is the
   reason that file works in the AMBIENT matrix algebra rather than in `suTwo`.
2. **The pairing in (3.11) is `tr A(b)J(b)` with `A(b)` in the algebra**, so `J(b)` must be
   algebra-valued for the pairing to be the Killing form. Bałaban's generators are Hermitian
   (`𝔤ᶜ`, CMP109 (1.8)'s "projection onto the algebra `𝔤ᶜ`"); this tree's `suTwo` is the
   skew-Hermitian convention. **The two differ by exactly one factor of `i`**, and §3 is that factor
   made into an isomorphism. This is a CONVENTION bridge, and it is the whole content of the
   "carrier is scalar, source is Lie-algebra" finding at this locus: the defect was never that `J`
   is not algebra-valued, it is that the tree had no algebra-valued `J` object.

`piProj` (CMP109 (1.8)'s `π`, made explicit in `SourceJ.lean` for `N = 2`) supplies tracelessness
unconditionally — `trace (piProj X) = 0` for EVERY `X` — so §2 never needs the harder fact that
`tr U(∂p)` is real.
-/

namespace AdalyFormal.Balaban.DeltaKSuTwoFaithful

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo BondFnL2 mem_suTwo_iff conjByAmbient
  conjByAmbient_apply witnessU suTwoWitnessVal suTwoWitnessVal_mem)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL witnessY)
open AdalyFormal.Balaban.SourceJ (piProj FnuMu DstarDir Jfield Jsource
  piProj_eq_self_of_trace_zero Jsource_trivialU_eq_zero Jsource_witnessU_ne_zero)
open AdalyFormal.Balaban.DeltaPrime (imHolonomy holonomyElem holonomyElemInv trivialU)

/-! ## §2 — `J`'s VALUES ARE HERMITIAN AND TRACELESS

The carrier is `hermTraceless`, Bałaban's own `𝔤ᶜ`-real-form for `N = 2` (traceless Hermitian). It
is built as a `Submodule ℝ` of the ambient matrix algebra, mirroring `CovariantOperators.suTwo`'s
construction exactly (LAW-19 — same pattern, different sign in the star clause). -/

/-- **`𝔤 = i·𝔰𝔲(2)`: traceless HERMITIAN `2×2` complex matrices** — Bałaban's algebra convention
(CMP99b p.391's `A`, `J` values; CMP109 (1.8)'s `𝔤ᶜ` intersected with the Hermitian real form).
This is the space `SourceJ.Jsource` actually takes values in, which is why it is defined here rather
than reused: no such submodule existed in the tree (measured: zero hits for
`hermTraceless`/`IsHermitian` across `formal/AdalyFormal/AdalyFormal`). -/
def hermTraceless : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ) where
  carrier := {X | Xᴴ = X ∧ Matrix.trace X = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro X Y ⟨hX1, hX2⟩ ⟨hY1, hY2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_add, hX1, hY1]
    · rw [Matrix.trace_add, hX2, hY2, add_zero]
  smul_mem' := by
    rintro c X ⟨hX1, hX2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_smul, hX1, star_trivial]
    · rw [Matrix.trace_smul, hX2, smul_zero]

theorem mem_hermTraceless_iff (X : Matrix (Fin 2) (Fin 2) ℂ) :
    X ∈ hermTraceless ↔ Xᴴ = X ∧ Matrix.trace X = 0 := Iff.rfl

/-- **L7 witness — `hermTraceless` is genuinely inhabited by a nonzero element.** `diag(1,-1)`:
real, symmetric, traceless. This is exactly `CovariantOperators.garbageNotSkewHermitian`, the
matrix that file exhibits to prove `suTwo`'s skew clause is load-bearing — the same object is a
legitimate INHABITANT here, which is the cleanest possible statement that the two submodules are
different. -/
theorem hermTracelessWitness_mem :
    (!![(1 : ℂ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) ∈ hermTraceless := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem hermTracelessWitness_ne_zero :
    (!![(1 : ℂ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
  intro h
  have h00 : (!![(1 : ℂ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) 0 0
      = (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [h]
  simp at h00

/-- **D4 GARBAGE #1 for `hermTraceless`: Hermitian but NOT traceless.** The identity is Hermitian
and has trace `2 ≠ 0`, so it violates EXACTLY the trace clause and nothing else. -/
theorem one_not_mem_hermTraceless :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ∉ hermTraceless := by
  intro h
  have := h.2
  rw [Matrix.trace_one] at this
  simp at this

/-- **D4 GARBAGE #2 for `hermTraceless`: traceless but NOT Hermitian.** `i·diag(1,-1)` — this
tree's own `suTwoWitnessVal`, i.e. an element of `suTwo`. So the two submodules genuinely separate
in BOTH directions, and §3's `i`-twist is not a no-op. -/
theorem suTwoWitnessVal_not_mem_hermTraceless :
    suTwoWitnessVal ∉ hermTraceless := by
  intro h
  have h1 : (suTwoWitnessVal)ᴴ = suTwoWitnessVal := h.1
  have h2 : (suTwoWitnessVal)ᴴ = -suTwoWitnessVal := (suTwoWitnessVal_mem).1
  rw [h1] at h2
  exact AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal_ne_neg_self h2

#print axioms hermTraceless
#print axioms mem_hermTraceless_iff
#print axioms hermTracelessWitness_mem
#print axioms hermTracelessWitness_ne_zero
#print axioms one_not_mem_hermTraceless
#print axioms suTwoWitnessVal_not_mem_hermTraceless

/-! ### §2a — the three closure facts the `J` chain needs -/

/-- The trace of a Hermitian matrix is fixed by conjugation — the fact `piProj` needs in order to
preserve Hermiticity (its subtracted multiple of the identity has to be Hermitian too). -/
theorem star_trace_of_hermitian {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : Xᴴ = X) :
    star (Matrix.trace X) = Matrix.trace X := by
  rw [← Matrix.trace_conjTranspose, hX]

/-- **`π` LANDS IN `hermTraceless` whenever its input is Hermitian.** Tracelessness is
unconditional — that is what `π` is for — and Hermiticity survives because the subtracted multiple
`(tr X / 2)·1` is Hermitian by `star_trace_of_hermitian`. -/
theorem piProj_mem_hermTraceless {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : Xᴴ = X) :
    piProj X ∈ hermTraceless := by
  refine ⟨?_, ?_⟩
  · show (X - (Matrix.trace X / (2 : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ = _
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hX]
    congr 1
    have ht : star (Matrix.trace X) = Matrix.trace X := star_trace_of_hermitian hX
    rw [star_div₀, ht]
    norm_num
  · show Matrix.trace (X - (Matrix.trace X / (2 : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    simp only [Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
    ring_nf

/-- **Conjugation by a special-unitary element preserves `hermTraceless`.** Hermiticity needs no
unitarity at all (`(VXV^†)^† = VX^†V^†`); tracelessness needs exactly `V^†V = 1`, which is what
membership in the unitary group gives. -/
theorem conjByAmbient_mem_hermTraceless (g : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ∈ hermTraceless) :
    conjByAmbient g X ∈ hermTraceless := by
  obtain ⟨hH, hT⟩ := hX
  have hV : ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have hg : (g : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
      Matrix.specialUnitaryGroup_le_unitaryGroup g.2
    have h := Matrix.mem_unitaryGroup_iff'.mp hg
    rwa [Matrix.star_eq_conjTranspose] at h
  have hunfold : conjByAmbient g X
      = (g : Matrix (Fin 2) (Fin 2) ℂ) * X * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ := rfl
  refine ⟨?_, ?_⟩
  · rw [hunfold, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
  · rw [hunfold, Matrix.trace_mul_cycle, hV, Matrix.one_mul, hT]

/-- **`Im ∂U` IS HERMITIAN.** `imHolonomy U p = (1/2i)(W − W⁻¹)` with `W ∈ SU(2)`, so
`W⁻¹ = W^†`, so `W − W^†` is SKEW-Hermitian, and the prefactor `1/2i` (whose conjugate is its own
negative) flips it back to Hermitian. This is the fact `SourceJ.lean`'s own `DstarDir` docstring
asserts in prose (*"`imHolonomy`'s values are Hermitian, not skew-Hermitian"*) and which no
declaration in the tree carried. -/
theorem imHolonomy_hermitian {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (imHolonomy U p)ᴴ = imHolonomy U p := by
  set W : Matrix (Fin 2) (Fin 2) ℂ := (holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) with hW
  have hinv : ((holonomyElemInv U p : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = Wᴴ := rfl
  show ((1 / (2 * Complex.I) : ℂ) • (W - Wᴴ))ᴴ = (1 / (2 * Complex.I) : ℂ) • (W - Wᴴ)
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose]
  have hstar : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I) : ℂ) := by
    rw [RCLike.star_def]
    simp [Complex.ext_iff]
  rw [hstar, neg_smul, ← smul_neg]
  congr 1
  abel

/-- `F_{νμ}` lands in `hermTraceless` — all three branches of its trichotomy. -/
theorem FnuMu_mem_hermTraceless {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ν μ : Fin 3) (y : PeriodicLatticeSite L) :
    FnuMu U ν μ y ∈ hermTraceless := by
  unfold FnuMu
  split_ifs with h1 h2
  · exact piProj_mem_hermTraceless (imHolonomy_hermitian U _)
  · exact Submodule.neg_mem _ (piProj_mem_hermTraceless (imHolonomy_hermitian U _))
  · exact Submodule.zero_mem _

/-- `D*_ν` preserves `hermTraceless` pointwise. -/
theorem DstarDir_mem_hermTraceless {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ν : Fin 3)
    {G : PeriodicLatticeSite L → Matrix (Fin 2) (Fin 2) ℂ}
    (hG : ∀ y, G y ∈ hermTraceless) (x : PeriodicLatticeSite L) :
    DstarDir U ν G x ∈ hermTraceless :=
  Submodule.sub_mem _
    (conjByAmbient_mem_hermTraceless _ (hG (periodicLatticeShiftBack x ν))) (hG x)

/-- **`J(x,μ) ∈ 𝔤`** — the sum over `ν ≠ μ` of `hermTraceless` members. -/
theorem Jfield_mem_hermTraceless {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : PeriodicLatticeSite L) (μ : Fin 3) :
    Jfield U x μ ∈ hermTraceless := by
  unfold Jfield
  refine Submodule.sum_mem _ (fun ν _ => ?_)
  split_ifs with h
  · exact Submodule.zero_mem _
  · exact DstarDir_mem_hermTraceless U ν (fun y => FnuMu_mem_hermTraceless U ν μ y) x

/-- **THE §2 HEADLINE: `J(U)(b)` is traceless Hermitian, at every bond, every background, every
lattice.** Fully general — no witness, no regularity restriction on `U`. -/
theorem Jsource_mem_hermTraceless {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b : Bond L) :
    Jsource U b ∈ hermTraceless :=
  Jfield_mem_hermTraceless U b.1 b.2

#print axioms star_trace_of_hermitian
#print axioms piProj_mem_hermTraceless
#print axioms conjByAmbient_mem_hermTraceless
#print axioms imHolonomy_hermitian
#print axioms FnuMu_mem_hermTraceless
#print axioms DstarDir_mem_hermTraceless
#print axioms Jfield_mem_hermTraceless
#print axioms Jsource_mem_hermTraceless

/-! ## §3 — THE `i`-TWIST IS AN ISOMORPHISM `𝔤 ≃ₗ[ℝ] 𝔰𝔲(2)`

Bałaban's algebra convention is Hermitian, this tree's is skew-Hermitian, and the bridge is exactly
one factor of `i`. Stated as a `LinearEquiv` so that no information can be lost in either direction
by construction, and so that §7's rank statement transfers for free. -/

theorem smulI_mem_suTwo {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ∈ hermTraceless) :
    Complex.I • X ∈ suTwo := by
  obtain ⟨hH, hT⟩ := hX
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, hH, RCLike.star_def, Complex.conj_I, neg_smul]
  · rw [Matrix.trace_smul, hT, smul_zero]

theorem smulNegI_mem_hermTraceless {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ∈ suTwo) :
    (-Complex.I) • X ∈ hermTraceless := by
  obtain ⟨hH, hT⟩ := hX
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, hH, RCLike.star_def, map_neg, Complex.conj_I, neg_neg,
      smul_neg, neg_smul]
  · rw [Matrix.trace_smul, hT, smul_zero]

/-- **THE CONVENTION BRIDGE.** `X ↦ i·X` as an `ℝ`-linear isomorphism from Bałaban's traceless
Hermitian algebra onto this tree's `𝔰𝔲(2)`. Both directions are exhibited, so nothing is lost:
`hermTracelessEquivSuTwo.symm (hermTracelessEquivSuTwo X) = X` is a field of the structure, checked
by the kernel. -/
noncomputable def hermTracelessEquivSuTwo : hermTraceless ≃ₗ[ℝ] SuTwo where
  toFun X := ⟨Complex.I • (X : Matrix (Fin 2) (Fin 2) ℂ), smulI_mem_suTwo X.2⟩
  invFun Y := ⟨(-Complex.I) • (Y : Matrix (Fin 2) (Fin 2) ℂ), smulNegI_mem_hermTraceless Y.2⟩
  map_add' X Y := by
    apply Subtype.ext
    show Complex.I • ((X : Matrix (Fin 2) (Fin 2) ℂ) + (Y : Matrix (Fin 2) (Fin 2) ℂ))
      = Complex.I • (X : Matrix (Fin 2) (Fin 2) ℂ) + Complex.I • (Y : Matrix (Fin 2) (Fin 2) ℂ)
    rw [smul_add]
  map_smul' c X := by
    apply Subtype.ext
    show Complex.I • (c • (X : Matrix (Fin 2) (Fin 2) ℂ))
      = c • (Complex.I • (X : Matrix (Fin 2) (Fin 2) ℂ))
    rw [smul_comm]
  left_inv X := by
    apply Subtype.ext
    show (-Complex.I) • (Complex.I • (X : Matrix (Fin 2) (Fin 2) ℂ))
      = (X : Matrix (Fin 2) (Fin 2) ℂ)
    rw [smul_smul]
    norm_num
  right_inv Y := by
    apply Subtype.ext
    show Complex.I • ((-Complex.I) • (Y : Matrix (Fin 2) (Fin 2) ℂ))
      = (Y : Matrix (Fin 2) (Fin 2) ℂ)
    rw [smul_smul]
    norm_num

theorem hermTracelessEquivSuTwo_apply (X : hermTraceless) :
    ((hermTracelessEquivSuTwo X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)
      = Complex.I • (X : Matrix (Fin 2) (Fin 2) ℂ) := rfl

theorem hermTracelessEquivSuTwo_symm_apply (Y : SuTwo) :
    ((hermTracelessEquivSuTwo.symm Y : hermTraceless) : Matrix (Fin 2) (Fin 2) ℂ)
      = (-Complex.I) • (Y : Matrix (Fin 2) (Fin 2) ℂ) := rfl

#print axioms smulI_mem_suTwo
#print axioms smulNegI_mem_hermTraceless
#print axioms hermTracelessEquivSuTwo
#print axioms hermTracelessEquivSuTwo_apply
#print axioms hermTracelessEquivSuTwo_symm_apply

/-! ### §3a — `J(U)` ON THE su(2) CARRIER

`JsourceSu U : Bond L → SuTwo` is `Jsource U` read through §3's isomorphism, and `JsourceSuL2 U`
is the same datum in the `L²` carrier `BondFnL2 L` that `deltaKTowerCLM` acts on. -/

/-- **`J(U)`, su(2)-VALUED.** The tree's first algebra-valued source. -/
noncomputable def JsourceSu {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    Bond L → SuTwo :=
  fun b => hermTracelessEquivSuTwo ⟨Jsource U b, Jsource_mem_hermTraceless U b⟩

theorem JsourceSu_coe {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b : Bond L) :
    ((JsourceSu U b : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) = Complex.I • Jsource U b := rfl

/-- **LOSSLESSNESS, AS AN EQUATION.** `Jsource U b` is RECOVERED from `JsourceSu U b` by
multiplying by `-i`. No adjective: the source datum is a function of the su(2)-valued datum, at
every bond, every `U`, every `L`. This is the statement `SourceJFaithful.lean`'s dimension-count
residual says is impossible on the scalar carrier. -/
theorem JsourceSu_recovers {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b : Bond L) :
    (-Complex.I) • ((JsourceSu U b : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) = Jsource U b := by
  rw [JsourceSu_coe, smul_smul]
  norm_num

/-- **INJECTIVITY IN THE BACKGROUND.** Two backgrounds with the same su(2)-valued source have the
same source, period. So `JsourceSu` separates exactly as many configurations as `Jsource` does — the
transport introduces no identification. Contrast `SourceJFaithful.JsourceReal`, which composes with
a single real coordinate functional and cannot support this statement. -/
theorem JsourceSu_injective_in_background {L : PeriodicLatticeExtent}
    (U U' : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (h : JsourceSu U = JsourceSu U') : Jsource U = Jsource U' := by
  funext b
  rw [← JsourceSu_recovers U b, ← JsourceSu_recovers U' b, h]

/-- **`J(U)` in the `L²` carrier `deltaKTowerCLM` acts on.** -/
noncomputable def JsourceSuL2 {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) : BondFnL2 L :=
  WithLp.toLp 2 (JsourceSu U)

/-- **`J` VANISHES at the flat background**, on the su(2) carrier — inherited from
`SourceJ.Jsource_trivialU_eq_zero`, fully general in `L`. -/
theorem JsourceSu_trivialU {L : PeriodicLatticeExtent} :
    JsourceSu (trivialU (L := L)) = 0 := by
  funext b
  apply Subtype.ext
  rw [JsourceSu_coe, Jsource_trivialU_eq_zero b]
  simp

theorem JsourceSuL2_trivialU {L : PeriodicLatticeExtent} :
    JsourceSuL2 (trivialU (L := L)) = 0 := by
  unfold JsourceSuL2
  rw [JsourceSu_trivialU]
  ext b
  simp

/-- **`J` IS NONZERO at the tree's own non-flat background** — the other half of the two-sided
non-degeneracy, and the S82 garbage control on `JsourceSu_trivialU`: the same construction at the
mutated (flat) background gives `0`, so the nonzero fact is not forced by the type. -/
theorem JsourceSu_witnessU_ne_zero : JsourceSu witnessU ≠ 0 := by
  intro h
  refine Jsource_witnessU_ne_zero ?_
  have hb : JsourceSu witnessU (witnessY, (0 : Fin 3)) = 0 := by rw [h]; rfl
  have := JsourceSu_recovers witnessU (witnessY, (0 : Fin 3))
  rw [hb] at this
  rw [← this]
  simp

theorem JsourceSuL2_witnessU_ne_zero : JsourceSuL2 witnessU ≠ 0 := by
  intro h
  refine JsourceSu_witnessU_ne_zero ?_
  have : WithLp.ofLp (JsourceSuL2 witnessU) = WithLp.ofLp (0 : BondFnL2 witnessL) :=
    congrArg _ h
  simpa [JsourceSuL2] using this

#print axioms JsourceSu
#print axioms JsourceSu_coe
#print axioms JsourceSu_recovers
#print axioms JsourceSu_injective_in_background
#print axioms JsourceSuL2
#print axioms JsourceSu_trivialU
#print axioms JsourceSuL2_trivialU
#print axioms JsourceSu_witnessU_ne_zero
#print axioms JsourceSuL2_witnessU_ne_zero

/-! ## §4 — THE COMPOSITION: THE su(2) `Δ_k` FAMILY CONSUMING `J(U)`

`DeltaKSuTwoCarrier.deltaKTowerCLM ell k levels U` is (3.156) **at `J = 0`** — that file's §1.4
table lists the two `J`-summands as UNACCOUNTED and its §1.5 R2 names `J = 0` as a residual. §4 and
§5 supply the missing summand on this carrier, with `J` NOT a free field:

**`J` is not a parameter of anything below.** Every source term is built from `JsourceSuL2 U`, i.e.
from the SAME `U` the operator is built from, through `SourceJ.Jsource` (CMP99b (3.11)). This is
§LEAN-D's own prescription — *"make definitions consume fixed, source-defined objects rather than
freely chosen data satisfying properties"* — and it is what distinguishes this from
`FaithfulCoercivity.SourceIngredients`, whose `J` is a chosen vector, and from
`SourceJFaithful.UFaithfulSourceIngredients`, whose `Jof` is a chosen family. There is no `Jof` field
here to rig.

What IS carried as external parameters, and disclosed as such: the covariance bundle `cov` (`G₁`,
`Q₁`, `(Q₁G₁Q₁*)⁻¹` — CMP99b (3.126)/(3.128)/(3.129), whose invertibility with a `k`-independent
bound is [4]'s Lemma 2.4, an unproved import in this tree) and `D̃⁽²⁾`'s parameter `Qext` (CMP99b's
own `Q_j`, eq. (3.13), blocked on CMP98's `Ū^j`). Both are `SourceJFaithful.lean`'s named residuals,
inherited unchanged, not introduced here. -/

open AdalyFormal.Balaban.KernelSubspace (Level)
open AdalyFormal.Balaban.CovariantHjMinimizer (deltaKernelImageCovH oneLevelUniv)
open AdalyFormal.Balaban.CovariantOperators (curlCovariantLM)
open AdalyFormal.Balaban.CovariantHjFaithful (gaugeConstraintSubspaceCovFaithful)
open AdalyFormal.Balaban.DeltaKSuTwoCarrier (deltaKTowerCLM towerWitness
  tower_kills_towerWitness towerWitness_curl_ne_zero deltaKTowerCLM_apply_eq_zero_of_mem)
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape)

/-- **(3.156)'s THIRD TERM, `-2⟨H₁D̃⁽²⁾(B), J⟩`, on the su(2) carrier** — `H₁` supplied by the
covariance bundle through `VariationalProjectorH1.solutionOperator` (3.129), `D̃⁽²⁾` by
`SourceJ.Dtilde2Shape`, and `J` by `JsourceSuL2 U`. Everything except `cov` and `Qext` is
determined by `U`. -/
noncomputable def sourceTermSu {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (cov : BalabanCovarianceData (BondFnL2 L) (BondFnL2 L))
    (Qext : BondFnL2 L → BondFnL2 L) (A : BondFnL2 L) : ℝ :=
  -2 * (inner ℝ (solutionOperator cov (Dtilde2Shape Qext A)) (JsourceSuL2 U) : ℝ)

/-- **`D̃⁽²⁾`'s parameter, instantiated so that the third term is LIVE.** `v ↦ ‖v‖²·J(U)`, the
su(2)-carrier analogue of `SourceJFaithful.faithfulQext` (`v ↦ ‖v‖²·e`), with the CHOSEN vector `e`
replaced by the source-determined `J(U)`. Genuinely quadratic, so `D̃⁽²⁾` does not vanish — the
defect `FaithfulRepairAnchored.scalarSI` has with `Qext := 0`, which makes `J` inert. **Not offered
as CMP99b's own `Q_j`**; the `Q_j` residual is untouched. -/
noncomputable def jQext {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L → BondFnL2 L :=
  fun v => ‖v‖ ^ 2 • JsourceSuL2 U

/-- **THE COMPOSITION.** The level-`k` form of `DeltaKSuTwoCarrier.deltaKTowerCLM` PLUS (3.156)'s
third term at the same background. At `Qext := 0` or at a flat `U` this is the tower form verbatim
(§5), so the addition is strictly additional content and nothing already banked moves. -/
noncomputable def towerFormWithSource {L : PeriodicLatticeExtent} (ell k : ℕ)
    (levels : List (Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (cov : BalabanCovarianceData (BondFnL2 L) (BondFnL2 L))
    (Qext : BondFnL2 L → BondFnL2 L) (A : BondFnL2 L) : ℝ :=
  (inner ℝ A (deltaKTowerCLM ell k levels U A) : ℝ) + sourceTermSu U cov Qext A

#print axioms sourceTermSu
#print axioms jQext
#print axioms towerFormWithSource

/-! ## §5 — THE CLOSED FORM OF THE COMPOSITION, AND WHAT IT SAYS ABOUT COERCIVITY

At the disclosed scalar covariance (`FaithfulRepairAnchored.scalarCov`, reused — LAW-19) the third
term evaluates in closed form, and the result is a fact about the SIGN of the source contribution
that no adjective can soften: **it is a NEGATIVE shift proportional to `‖A‖²‖J(U)‖²`.** So the
source term does not help coercivity, it costs it, and the cost is `U`-dependent. §6c turns that into
an exact statement about what a `k`- and `U`-uniform constant would have to beat. -/

/-! ## §6 — A `k`- AND `U`-UNIFORMITY STATEMENT THAT CAN BE **FORMED** ON THIS CARRIER, WITH BOTH
BRACKETS PROVED

**Read the disclaimer in §0 first: forming this statement is not building an RG ladder, and nothing
here proves it.** What §6 does is fix the statement's exact shape and then bound it from both sides
by theorems, so that no consumer can read it as more than it is:

* **§6a — it is JUNK-INHABITED at `V = ⊥`.** The domain family is a free parameter and its chooser
  can empty the statement. This is the S91 defect class ("existential over freely-chosen data")
  applied to the domain rather than the operator, and it is exhibited rather than warned about.
* **§6b — it is FALSE at `V = ⊤`.** Not "unproved": refuted, from `deltaKTowerCLM`'s own
  annihilation of `V_k(U)`. So the domain family is not a decoration either — it is forced to avoid
  the annihilated subspace, which is exactly what CMP99b p.428 does when it says *"This form is
  considered on the subspace `{B : B = 0 on Λᶜ, B = 0 on ⋃ Ax(y), Q₁B = 0}`."*
* **§6c — the source-carrying version costs exactly `2‖J(U)‖²`.** A uniform constant for the
  composition of §4 is a uniform constant for the sourceless tower SHIFTED UP by `2‖J(U_{k,c})‖²`.
  That is the precise price of the `J`-summand, and it is `U`-dependent.

Unlike the scalar interfaces (`SourceJFaithful.lean` measured `Uconfig` occurring ZERO times across
seven modules, so no uniformity-in-`U` claim could be FORMED there), the statement below quantifies
over a genuine `Uconfig` **together with a map `Uof` into actual `SU(2)` link configurations** — so
the `∀U` is over backgrounds the operator really consumes, not over an abstract label the operator
ignores. -/

theorem toLp_towerWitness_ne_zero {L : PeriodicLatticeExtent} (ell k : ℕ) (hell2 : 2 ≤ ell ^ k)
    (hdvd : ∀ μ : Fin 3, ell ^ k ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (WithLp.toLp 2 (towerWitness U ell k) : BondFnL2 L) ≠ 0 := by
  intro h
  have hfun : towerWitness U ell k = 0 := by
    have hof : WithLp.ofLp (WithLp.toLp 2 (towerWitness U ell k) : BondFnL2 L)
        = WithLp.ofLp (0 : BondFnL2 L) := congrArg _ h
    simpa using hof
  refine towerWitness_curl_ne_zero ell k hell2 hdvd U ?_
  rw [hfun, map_zero]

theorem inner_tower_towerWitness_eq_zero {L : PeriodicLatticeExtent} (ell k : ℕ)
    (hpos : 0 < ell ^ k) (hdvd : ∀ μ : Fin 3, ell ^ k ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection] :
    (inner ℝ (WithLp.toLp 2 (towerWitness U ell k) : BondFnL2 L)
      (deltaKTowerCLM ell k (oneLevelUniv L) U
        (WithLp.toLp 2 (towerWitness U ell k))) : ℝ) = 0 := by
  rw [tower_kills_towerWitness ell k hpos hdvd U, inner_zero_right]

/-- **THE STATEMENT.** `∃γ>0, ∀k, ∀U, ∀A ∈ V k : γ‖A‖² ≤ ⟨A, Δ̂_k(U)A⟩` — p.428's quantifier order
(`∃γ₀ ∀k ∀U`), on the su(2) carrier, over the `ℕ`-indexed family that actually consumes `U`.
**`V` is a free parameter and §6a/§6b prove it decides the statement.** -/
def TowerUniformSuTwo {L : PeriodicLatticeExtent} (Uconfig : Type*)
    (Uof : ℕ → Uconfig → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (levels : List (Level L))
    (hproj : ∀ (k : ℕ) (c : Uconfig),
      (deltaKernelImageCovH (Uof k c) levels).HasOrthogonalProjection)
    (V : ℕ → Submodule ℝ (BondFnL2 L)) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ (k : ℕ) (c : Uconfig) (A : BondFnL2 L), A ∈ V k →
    γ * ‖A‖ ^ 2 ≤ (inner ℝ A (@deltaKTowerCLM L ell k levels (Uof k c) (hproj k c) A) : ℝ)

/-- **§6a — JUNK-INHABITED at `V = ⊥`, for EVERY family.** The statement holds with `γ = 1` and no
mathematics whatever: the only member of `⊥` is `0`. Exhibited, not warned about. -/
theorem towerUniformSuTwo_bot {L : PeriodicLatticeExtent} (Uconfig : Type*)
    (Uof : ℕ → Uconfig → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (levels : List (Level L))
    (hproj : ∀ (k : ℕ) (c : Uconfig),
      (deltaKernelImageCovH (Uof k c) levels).HasOrthogonalProjection) :
    TowerUniformSuTwo Uconfig Uof ell levels hproj (fun _ => ⊥) := by
  refine ⟨1, one_pos, ?_⟩
  intro k c A hA
  rw [Submodule.mem_bot] at hA
  subst hA
  simp

/-- **§6b — FALSE at `V = ⊤`.** Refuted, at every `ell` and every level `k₀` the torus admits
(`2 ≤ ell^{k₀}`, `ell^{k₀} ∣ L μ + 1`), for every nonempty `Uconfig`: the level-`k₀` witness lies in
`⊤`, is nonzero, and is ANNIHILATED, so no positive `γ` survives. This is the theorem that forces the
domain family of `TowerUniformSuTwo` to avoid `V_k(U)` — p.428's own restriction, re-derived here as
a consequence of the operator rather than imported as a convention. -/
theorem not_towerUniformSuTwo_top {L : PeriodicLatticeExtent} {Uconfig : Type*}
    (Uof : ℕ → Uconfig → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (k₀ : ℕ) (hell2 : 2 ≤ ell ^ k₀) (hdvd : ∀ μ : Fin 3, ell ^ k₀ ∣ (L μ + 1))
    (c₀ : Uconfig)
    (hproj : ∀ (k : ℕ) (c : Uconfig),
      (deltaKernelImageCovH (Uof k c) (oneLevelUniv L)).HasOrthogonalProjection) :
    ¬ TowerUniformSuTwo Uconfig Uof ell (oneLevelUniv L) hproj (fun _ => ⊤) := by
  rintro ⟨γ, hγ, hb⟩
  letI := hproj k₀ c₀
  set U := Uof k₀ c₀ with hU
  set A : BondFnL2 L := WithLp.toLp 2 (towerWitness U ell k₀) with hA
  have hne : A ≠ 0 := toLp_towerWitness_ne_zero ell k₀ hell2 hdvd U
  have hn : (0 : ℝ) < ‖A‖ := norm_pos_iff.mpr hne
  have hzero : (inner ℝ A (deltaKTowerCLM ell k₀ (oneLevelUniv L) U A) : ℝ) = 0 :=
    inner_tower_towerWitness_eq_zero ell k₀ (by omega) hdvd U
  have hle := hb k₀ c₀ A Submodule.mem_top
  rw [hzero] at hle
  linarith [mul_pos hγ (pow_pos hn 2)]

/-- **THE NECESSARY CONDITION ON THE DOMAIN, IN FULL GENERALITY** (every `levels`, not just
`oneLevelUniv`): if the uniform statement holds, then at every scale and every configuration the
domain `V k` meets the annihilated subspace `V_k(U)` only at `0`. So `V` is not free after all — it
is constrained by a theorem, and §6b is the special case where the constraint is violated
maximally. -/
theorem towerUniformSuTwo_forces_kernel_avoidance {L : PeriodicLatticeExtent} {Uconfig : Type*}
    (Uof : ℕ → Uconfig → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (levels : List (Level L))
    (hproj : ∀ (k : ℕ) (c : Uconfig),
      (deltaKernelImageCovH (Uof k c) levels).HasOrthogonalProjection)
    (V : ℕ → Submodule ℝ (BondFnL2 L))
    (h : TowerUniformSuTwo Uconfig Uof ell levels hproj V)
    (k : ℕ) (c : Uconfig) (A : BondFnL2 L) (hAV : A ∈ V k)
    (hAK : WithLp.ofLp A ∈ gaugeConstraintSubspaceCovFaithful (ell ^ k) levels (Uof k c)) :
    A = 0 := by
  obtain ⟨γ, hγ, hb⟩ := h
  letI := hproj k c
  have hzero : (inner ℝ A (deltaKTowerCLM ell k levels (Uof k c) A) : ℝ) = 0 := by
    have hkill : deltaKTowerCLM ell k levels (Uof k c) A = 0 := by
      have : (WithLp.toLp 2 (WithLp.ofLp A) : BondFnL2 L) = A := rfl
      rw [← this]
      exact deltaKTowerCLM_apply_eq_zero_of_mem ell k levels (Uof k c) hAK
    rw [hkill, inner_zero_right]
  have hle := hb k c A hAV
  rw [hzero] at hle
  have hn : ‖A‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖A‖ = 0 := by nlinarith [norm_nonneg A, sq_nonneg ‖A‖]
  exact norm_eq_zero.mp this

/-- **THE SHIFT IN `withSource_uniform_shifts_gamma` IS ZERO ON A FLAT FAMILY.** `J(1) = 0`, so on
`Uof k c := 1` that theorem's conclusion is its own hypothesis restated and carries no information.
This is a DEGENERACY of the shift statement, recorded as a theorem rather than as a caveat. -/
theorem shift_zero_at_flat {L : PeriodicLatticeExtent} :
    2 * ‖JsourceSuL2 (trivialU (L := L))‖ ^ 2 = 0 := by
  rw [JsourceSuL2_trivialU]
  simp

/-- **AND STRICTLY POSITIVE AT THE TREE'S OWN NON-FLAT BACKGROUND** — so the shift statement is not
degenerate for every family. The pair (`shift_zero_at_flat`, this) is what makes
`withSource_uniform_shifts_gamma` a claim with content on some families and a tautology on others,
and both halves are compiled. -/
theorem shift_pos_at_witnessU : (0 : ℝ) < 2 * ‖JsourceSuL2 witnessU‖ ^ 2 :=
  mul_pos two_pos (pow_pos (norm_pos_iff.mpr JsourceSuL2_witnessU_ne_zero) 2)

/-! ## §7 — `Module.finrank ℝ SuTwo = 3`, AND THE SHARP DIMENSION COUNT

`VolumeScalingV.lean` §residuals records, verbatim: *"`Module.finrank ℝ SuTwo = 3` is **NOT proved
anywhere in this tree** (only `2 ≤` in …)"*, and keeps every codimension statement symbolic in
consequence. It is proved here — the lane was already holding the two halves, so this is a residual
closed in-pass rather than filed (OPS-10).

Why it belongs in THIS file rather than being left as somebody's else's arithmetic: it is what makes
§0's dimension claim sharp. `SourceJFaithful.lean`'s residual compares `8·|Bond L|` (the AMBIENT
matrix algebra) against `|Bond L|`. The relevant figure is `3`: `hermTraceless` is `3`-dimensional
(by §3's isomorphism plus this theorem), the su(2) fibre is `3`-dimensional, and so §3's map is onto
the WHOLE fibre. `J` is not squeezed into the su(2) carrier — it fills it. -/

open AdalyFormal.Balaban.SuTwoInner (pauliE1 pauliE2 pauliE3 hsInner inner_eq_hsInner
  hsInner_e1_e1 hsInner_e2_e2 hsInner_e3_e3 hsInner_e1_e2 hsInner_e1_e3 hsInner_e2_e3
  hsInner_symm)

/-- **THE COORDINATE MAP** `X ↦ ((X₀₁).im, (X₀₁).re, (X₀₀).im)`. `ℝ`-linear on the nose; §7's upper
bound is its injectivity. -/
noncomputable def suCoords : SuTwo →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun Y := ![((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im,
    ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re, ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im]
  map_add' Y Z := by
    funext i
    fin_cases i <;>
      simp [Submodule.coe_add, Matrix.add_apply, Complex.add_im, Complex.add_re]
  map_smul' c Y := by
    funext i
    fin_cases i <;> simp [Matrix.smul_apply]

/-- **INJECTIVITY.** The three real coordinates determine a traceless skew-Hermitian `2×2` matrix:
`X₀₀` is purely imaginary (skew-Hermiticity at the diagonal), `X₁₁ = -X₀₀` (trace), and
`X₁₀ = -conj X₀₁` (skew-Hermiticity off-diagonal). So the whole matrix is recovered from
`(X₀₁).re`, `(X₀₁).im`, `(X₀₀).im`. -/
theorem suCoords_injective : Function.Injective suCoords := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Y hY
  obtain ⟨hH, hT⟩ := Y.2
  set X : Matrix (Fin 2) (Fin 2) ℂ := (Y : Matrix (Fin 2) (Fin 2) ℂ) with hXdef
  have c0 : (X 0 1).im = 0 := congrFun hY 0
  have c1 : (X 0 1).re = 0 := congrFun hY 1
  have c2 : (X 0 0).im = 0 := congrFun hY 2

  have hd00 : star (X 0 0) = -(X 0 0) := by
    have h := congrFun (congrFun hH 0) 0
    rwa [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
  have hd11 : star (X 1 1) = -(X 1 1) := by
    have h := congrFun (congrFun hH 1) 1
    rwa [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
  have hoff : star (X 0 1) = -(X 1 0) := by
    have h := congrFun (congrFun hH 1) 0
    rwa [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
  have h01 : X 0 1 = 0 := by
    apply Complex.ext <;> simp [c0, c1]
  have h10 : X 1 0 = 0 := by
    rw [h01, star_zero] at hoff
    exact neg_eq_zero.mp hoff.symm
  have h00 : X 0 0 = 0 := by
    have hre : (X 0 0).re = 0 := by
      have h := congrArg Complex.re hd00
      simp at h
      linarith
    apply Complex.ext <;> simp [hre, c2]
  have h11 : X 1 1 = 0 := by
    have htr : X 0 0 + X 1 1 = 0 := by
      rw [Matrix.trace_fin_two] at hT
      exact hT
    rw [h00, zero_add] at htr
    exact htr
  apply Subtype.ext
  show X = (0 : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using h00
  · simpa using h01
  · simpa using h10
  · simpa using h11

theorem finrank_suTwo_le_three : Module.finrank ℝ SuTwo ≤ 3 := by
  have h := suCoords.finrank_le_finrank_of_injective suCoords_injective
  simpa using h

/-- `‖x‖ = 1` from `⟪x,x⟫ = 1`, stated generally: the diagonal half of `Orthonormal` is a norm
statement while `SuTwoInner.lean`'s facts are inner-product statements. -/
theorem norm_eq_one_of_inner_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x : H} (h : (inner ℝ x x : ℝ) = 1) : ‖x‖ = 1 := by
  have h2 : ‖x‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact h
  have hfac : (‖x‖ - 1) * (‖x‖ + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp hfac with h3 | h3
  · linarith
  · linarith [norm_nonneg x]

/-- The Pauli triple is orthonormal for `SuTwoInner`'s form — every value reused from
`SuTwoInner.lean` (LAW-19), none recomputed; only the three transposed off-diagonal entries are
derived, from `hsInner_symm`. -/
theorem orthonormal_pauli : Orthonormal ℝ ![pauliE1, pauliE2, pauliE3] := by
  have h12 : (inner ℝ pauliE1 pauliE2 : ℝ) = 0 := hsInner_e1_e2
  have h13 : (inner ℝ pauliE1 pauliE3 : ℝ) = 0 := hsInner_e1_e3
  have h23 : (inner ℝ pauliE2 pauliE3 : ℝ) = 0 := hsInner_e2_e3
  have h21 : (inner ℝ pauliE2 pauliE1 : ℝ) = 0 := by
    rw [inner_eq_hsInner, hsInner_symm]; exact hsInner_e1_e2
  have h31 : (inner ℝ pauliE3 pauliE1 : ℝ) = 0 := by
    rw [inner_eq_hsInner, hsInner_symm]; exact hsInner_e1_e3
  have h32 : (inner ℝ pauliE3 pauliE2 : ℝ) = 0 := by
    rw [inner_eq_hsInner, hsInner_symm]; exact hsInner_e2_e3
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · exact norm_eq_one_of_inner_self hsInner_e1_e1
    · exact norm_eq_one_of_inner_self hsInner_e2_e2
    · exact norm_eq_one_of_inner_self hsInner_e3_e3
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | exact h12
        | exact h13
        | exact h21
        | exact h23
        | exact h31
        | exact h32

theorem three_le_finrank_suTwo : 3 ≤ Module.finrank ℝ SuTwo := by
  simpa using orthonormal_pauli.linearIndependent.fintype_card_le_finrank

/-- **THE VALUE.** `𝔰𝔲(2)` has real dimension `3` — the residual `VolumeScalingV.lean` records as
unproved anywhere in this tree, closed. -/
theorem finrank_suTwo : Module.finrank ℝ SuTwo = 3 :=
  le_antisymm finrank_suTwo_le_three three_le_finrank_suTwo

/-- **AND THE SHARP COUNT FOR `J`.** `hermTraceless` is `3`-dimensional too, so §3's `i`-twist is an
isomorphism onto the WHOLE su(2) fibre — `J(U)`'s values occupy every direction of the carrier, not a
subspace of it. This is the exact sense in which the su(2) carrier is the right one for `J` and the
`|Bond L|`-dimensional scalar carrier is not. -/
theorem finrank_hermTraceless : Module.finrank ℝ hermTraceless = 3 := by
  rw [hermTracelessEquivSuTwo.finrank_eq]
  exact finrank_suTwo

#print axioms suCoords
#print axioms suCoords_injective
#print axioms finrank_suTwo_le_three
#print axioms norm_eq_one_of_inner_self
#print axioms orthonormal_pauli
#print axioms three_le_finrank_suTwo
#print axioms finrank_suTwo
#print axioms finrank_hermTraceless

#print axioms toLp_towerWitness_ne_zero
#print axioms inner_tower_towerWitness_eq_zero
#print axioms TowerUniformSuTwo
#print axioms towerUniformSuTwo_bot
#print axioms not_towerUniformSuTwo_top
#print axioms towerUniformSuTwo_forces_kernel_avoidance
#print axioms shift_zero_at_flat
#print axioms shift_pos_at_witnessU
end AdalyFormal.Balaban.DeltaKSuTwoFaithful
