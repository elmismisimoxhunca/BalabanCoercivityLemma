/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.Coercivity
import AdalyFormal.Balaban.RGLadderCoarse

set_option autoImplicit false

/-!
# `CoercUMainKernel` — the kernel-strengthening conditions, UPSTREAM of `Spine.lean`

## Why this module exists (the import cycle, measured not assumed)

`Balaban/CoercUMainRepair.lean` line 1 is `import AdalyFormal.Spine` — it ascribes the live
declaration `AdalyFormal.Spine.coerc_u_main` to its own transcription
(`oldConclusion_transcription_is_faithful`), which is only possible from DOWNSTREAM. Consequently
its `HasKernel` / `KernelMono` / `KernelGrows` / `NewConclusion` — the objects that repair
`coerc_u_main`'s statement — cannot be imported BY `Spine.lean`. `Spine.lean` says exactly this in
its own §1a-L docstring and carries local equivalents as a workaround.

This module breaks that cycle. Import direction established by grep on the transitive `import`
graph, not by assumption:

* `Anchoring.AnchoredBondSpace` / `Anchoring.anchoredVInter` / `CoercivityHypothesis` all live in
  `Balaban/Coercivity.lean` (there is a separate `Balaban/Anchoring.lean`, which `Spine.lean` does
  NOT reach — the `Anchoring` namespace `coerc_u_main` uses is the one inside `Coercivity.lean`).
* `Spine.lean` transitively imports `Balaban.Coercivity`, `Balaban.RGLadderCore` and
  `Balaban.RGLadderCoarse` (95 in-tree dependencies in total).
* Neither `Balaban.Coercivity` nor `Balaban.RGLadderCoarse` reaches `AdalyFormal.Spine`.

So this module imports only those two and is a legal import of `Spine.lean`.

## What is established here

* §1 — **the carrier cardinality facts, unconditional.** `Bond L` unfolds to
  `PeriodicLatticeSite L × Fin 3` with `PeriodicLatticeSite L = (μ : Fin 3) → Fin (L μ + 1)`
  structurally nonempty, so `3 ≤ Fintype.card (Bond L)` for EVERY extent function
  (`three_le_card_bond`), `Bond Lat` is `Nontrivial` (`bond_nontrivial`), and a rank-one coordinate
  span is a proper nonzero subspace of the carrier (`span_single_ne_top`, `span_single_ne_bot`).
  These are the lemmas `Spine.lean`'s §1a.1-R residual said the tree did not have.
* §2 — **K1 `HasKernel`, K2 `KernelMono`, K3 `KernelGrows`**, the `(Lat, ell)` guard
  `forcedBonds`/`NonDegenerate`, and the strengthened conclusion `KernelStrengthened`: the five live
  conjuncts of `Spine.coerc_u_main` verbatim, PLUS K1/K2/K3. Same conjunct order and same spelling
  as `CoercUMainRepair.NewConclusion`, so the two are definitionally equal and a downstream lane can
  ascribe one to the other by `rfl`.
* §3 — **the junk witness rebuilt upstream.** `jDelta k U = id + (k + colour U) • P_{span e_A}`,
  with all five live conjuncts discharged (`jDelta_satisfies_five_conjuncts`) at every `Lat`, every
  `ell`, every nontrivial `Uconfig`; and `KernelStrengthened` REJECTING that same witness
  (`kernelStrengthened_rejects_junk`, mechanism `jDelta_fails_HasKernel`: `id + PSD` is injective).
* §4 — **the CHAIN-REALIZATION theorem** `kernelStrengthened_of_chain`: for ANY monotone family
  `K : ℕ → Submodule ℝ (HH Lat)` inside `Vᗮ` with `K 0 ≠ ⊥` and one strict jump, the
  scaled-projector family `Δ k U := ucoef U • P_{(K k)ᗮ}` satisfies the WHOLE strengthened
  conclusion, with `ker (Δ k U) = K k` exactly. Its consequences, both proved sorry-free:
  `kernelStrengthened_of_two_forced_bonds`, and `kernelStrengthened_of_nonDegenerate` —
  **`NonDegenerate Lat ell → KernelStrengthened Lat Uconfig ell`.**
* §5 — **the finite-dimensional ceiling** `no_kernel_growth_at_every_rung`: on this carrier no
  operator family has a strictly growing kernel at every rung. So K3 (finitely many jumps) is the
  most any kernel-growth demand can ask, and §4 realizes one jump with a projector.
* §6 — **the `V = ⊤` collision** `no_hasKernel_of_V_eq_top` and
  `kernelStrengthened_false_of_V_eq_top`: where the pinned `V` is the whole carrier, K1 is
  unsatisfiable, so no kernel-carrying strengthening is TRUE there. Upstream twin of
  `EllDegeneracy.no_hasKernel_at_ell_le_one`, which `Spine.lean` can cite only in prose, being
  downstream.

## The two facts a consumer must not read past

1. **`KernelStrengthened` rejects the known junk witness and is nevertheless a THEOREM on the whole
   non-degenerate range** (§4). It is a strict logical strengthening — §3's witness inhabits the
   live conclusion and not this one — but it does not force lattice content: §4's inhabitant is an
   orthogonal projector onto the complement of a two-bond span. `Balaban/LatDegeneracy.lean`'s
   `newConclusion_iff_nonDegenerate` reaches the same conclusion downstream and independently, which
   is why the two are worth having side by side.
2. **§4 + §5 together bound the whole kernel route.** A strengthening whose added conjuncts
   constrain only the KERNEL CHAIN is either FALSE (if it demands growth at every rung, §5) or met
   by a content-free projector family (if it demands finitely many jumps inside `Vᗮ`, §4). Content
   has
   to come from pinning `Δ` itself; `Spine.lean` §1a-R (R2) names the four type blockers that stop
   that at this carrier.
-/

namespace AdalyFormal.Balaban.CoercUMainKernel

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace

variable {Lat : PeriodicLatticeExtent}

/-- `Spine.coerc_u_main`'s own carrier. -/
abbrev HH (Lat : PeriodicLatticeExtent) : Type :=
  AdalyFormal.Balaban.Anchoring.AnchoredBondSpace Lat

/-- `Spine.coerc_u_main`'s own pinned subspace. -/
noncomputable abbrev VV (ell : ℕ) : Submodule ℝ (HH Lat) :=
  AdalyFormal.Balaban.Anchoring.anchoredVInter (Lat := Lat) ell

/-! ## §1 — the carrier cardinality facts, UNCONDITIONAL

`Spine.lean`'s §1a.1-R residual read: *"the natural choice `W := ℝ ∙ EuclideanSpace.single b₀ 1`
needs `Bond Lat` to have at least two elements to be proper, and this file has no such cardinality
lemma."* It is unconditional, and it is proved here. -/

/-- Direction `0` at the origin. -/
def bondA : Bond Lat := (AdalyFormal.Balaban.RGLadderCoarse.originSite, (0 : Fin 3))

/-- Direction `1` at the origin. -/
def bondB : Bond Lat := (AdalyFormal.Balaban.RGLadderCoarse.originSite, (1 : Fin 3))

theorem bondA_ne_bondB : bondA (Lat := Lat) ≠ bondB (Lat := Lat) := by
  intro h
  have h2 : (0 : Fin 3) = (1 : Fin 3) := congrArg Prod.snd h
  exact absurd h2 (by decide)

/-- **`3 ≤ |Bond Lat|`, for every extent function.** No hypothesis: the three directions at the
origin are three distinct bonds, and the origin exists because the side length is `Lat μ + 1`. -/
theorem three_le_card_bond : 3 ≤ Fintype.card (Bond Lat) := by
  have hprod : Fintype.card (Bond Lat)
      = Fintype.card (PeriodicLatticeSite Lat) * Fintype.card (Fin 3) :=
    Fintype.card_prod _ _
  have hpos : 0 < Fintype.card (PeriodicLatticeSite Lat) :=
    Fintype.card_pos_iff.mpr ⟨AdalyFormal.Balaban.RGLadderCoarse.originSite⟩
  rw [hprod, Fintype.card_fin]
  omega

/-- **`Bond Lat` is `Nontrivial`.** -/
theorem bond_nontrivial : Nontrivial (Bond Lat) :=
  Fintype.one_lt_card_iff_nontrivial.mp (by have := three_le_card_bond (Lat := Lat); omega)

/-- A coordinate vector of the carrier is nonzero. -/
theorem single_ne_zero (b : Bond Lat) :
    (EuclideanSpace.single b (1 : ℝ) : HH Lat) ≠ 0 := by simp

theorem inner_single_single_self (b : Bond Lat) :
    (inner ℝ (EuclideanSpace.single b (1 : ℝ) : HH Lat)
      (EuclideanSpace.single b (1 : ℝ) : HH Lat) : ℝ) = 1 := by
  rw [EuclideanSpace.inner_single_left]
  simp

theorem inner_single_single_of_ne {b b' : Bond Lat} (h : b ≠ b') :
    (inner ℝ (EuclideanSpace.single b (1 : ℝ) : HH Lat)
      (EuclideanSpace.single b' (1 : ℝ) : HH Lat) : ℝ) = 0 := by
  rw [EuclideanSpace.inner_single_left]
  simp [h]

/-- `span {e_b} ≠ ⊥`. -/
theorem span_single_ne_bot (b : Bond Lat) :
    Submodule.span ℝ {(EuclideanSpace.single b (1 : ℝ) : HH Lat)} ≠ ⊥ := by
  intro h
  have hmem : (EuclideanSpace.single b (1 : ℝ) : HH Lat)
      ∈ (⊥ : Submodule ℝ (HH Lat)) := h ▸ Submodule.mem_span_singleton_self _
  simp at hmem

/-- **`span {e_b}` is PROPER** — the exact statement `Spine.lean`'s §1a.1-R residual said was
missing, unconditional in `Lat`, because a second bond always exists. -/
theorem span_single_ne_top (b : Bond Lat) :
    Submodule.span ℝ {(EuclideanSpace.single b (1 : ℝ) : HH Lat)} ≠ ⊤ := by
  haveI := bond_nontrivial (Lat := Lat)
  obtain ⟨b', hne⟩ : ∃ b' : Bond Lat, b' ≠ b := exists_ne b
  intro htop
  have hmem : (EuclideanSpace.single b' (1 : ℝ) : HH Lat)
      ∈ Submodule.span ℝ {(EuclideanSpace.single b (1 : ℝ) : HH Lat)} := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  have h2 : (inner ℝ (EuclideanSpace.single b' (1 : ℝ) : HH Lat)
        (EuclideanSpace.single b' (1 : ℝ) : HH Lat) : ℝ)
      = t * inner ℝ (EuclideanSpace.single b' (1 : ℝ) : HH Lat)
          (EuclideanSpace.single b (1 : ℝ) : HH Lat) := by
    rw [← real_inner_smul_right, ht]
  rw [inner_single_single_self b', inner_single_single_of_ne hne, mul_zero] at h2
  norm_num at h2

/-! ## §2 — the kernel conditions, the `(Lat, ell)` guard, and the strengthened conclusion

Definitions are spelled to match `CoercUMainRepair.HasKernel`/`KernelMono`/`KernelGrows` and
`CoercUMainRepair.NewConclusion` character for character, so that a downstream lane can ascribe the
two by `rfl`. They are RESTATED rather than imported for one reason only: the import direction runs
the other way (module header), and `CoercUMainRepair.lean` is another lane's write scope. -/

/-- **K1 — the operator is not injective at any scale.** A real RG step forgets something. -/
def HasKernel {Uconfig : Type*} (Δ : ℕ → Uconfig → HH Lat →L[ℝ] HH Lat) : Prop :=
  ∀ (k : ℕ) (U : Uconfig), ∃ w : HH Lat, w ≠ 0 ∧ Δ k U w = 0

/-- **K2 — kernels nest along the scale index.** What one rung forgets, no later rung recovers. -/
def KernelMono {Uconfig : Type*} (Δ : ℕ → Uconfig → HH Lat →L[ℝ] HH Lat) : Prop :=
  ∀ (k : ℕ) (U : Uconfig) (v : HH Lat), Δ k U v = 0 → Δ (k + 1) U v = 0

/-- **K3 — the nesting is STRICT somewhere.** Without this a `k`-constant kernel passes. -/
def KernelGrows {Uconfig : Type*} (Δ : ℕ → Uconfig → HH Lat →L[ℝ] HH Lat) : Prop :=
  ∃ (k : ℕ) (U : Uconfig) (w : HH Lat), Δ k U w ≠ 0 ∧ Δ (k + 1) U w = 0

/-- **The bonds `(2.121)` forces to vanish** — the union of the staircase `Γ_{y,x}` over every
coarse centre and every `x` in its block. Body identical to `Spine.forcedBonds`; the two are
definitionally equal (`Spine.forcedBonds_eq_kernel`). -/
def forcedBonds (Lat : PeriodicLatticeExtent) (ell : ℕ) : Finset (Bond Lat) :=
  (CoarseLattice Lat ell).biUnion fun y =>
    (blockOf y ell).biUnion fun x => staircasePath y x

theorem mem_forcedBonds {ell : ℕ} {b : Bond Lat} :
    b ∈ forcedBonds Lat ell ↔
      ∃ y ∈ CoarseLattice Lat ell, ∃ x ∈ blockOf y ell, b ∈ staircasePath y x := by
  unfold forcedBonds
  simp only [Finset.mem_biUnion]

/-- **The `(Lat, ell)` non-degeneracy guard.** Body identical to `Spine.NonDegenerate`. -/
def NonDegenerate (Lat : PeriodicLatticeExtent) (ell : ℕ) : Prop :=
  2 ≤ (forcedBonds Lat ell).card

instance (Lat : PeriodicLatticeExtent) (ell : ℕ) : Decidable (NonDegenerate Lat ell) := by
  unfold NonDegenerate; infer_instance

/-- **THE STRENGTHENED CONCLUSION.** `Spine.coerc_u_main`'s five live conjuncts, verbatim, PLUS
K1/K2/K3. Definitionally `CoercUMainRepair.NewConclusion`. -/
def KernelStrengthened (Lat : PeriodicLatticeExtent) (Uconfig : Type*) [Nontrivial Uconfig]
    (ell : ℕ) : Prop :=
  ∃ cohyp : AdalyFormal.Balaban.CoercivityHypothesis
      (AdalyFormal.Balaban.Anchoring.AnchoredBondSpace Lat) Uconfig,
    cohyp.V = AdalyFormal.Balaban.Anchoring.anchoredVInter (Lat := Lat) ell ∧
    (∀ (k : ℕ) (U : Uconfig), (cohyp.Δ k U).adjoint = cohyp.Δ k U) ∧
    (∀ (k : ℕ) (U : Uconfig) (v : AdalyFormal.Balaban.Anchoring.AnchoredBondSpace Lat),
      0 ≤ (inner ℝ v (cohyp.Δ k U v) : ℝ)) ∧
    (∀ (k : ℕ) (U : Uconfig) (c : ℝ), cohyp.Δ k U
      ≠ c • ContinuousLinearMap.id ℝ (AdalyFormal.Balaban.Anchoring.AnchoredBondSpace Lat)) ∧
    (∃ (U : Uconfig) (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧ cohyp.Δ k₁ U ≠ cohyp.Δ k₂ U) ∧
    HasKernel cohyp.Δ ∧ KernelMono cohyp.Δ ∧ KernelGrows cohyp.Δ

/-- The five live conjuncts alone — `Spine.coerc_u_main`'s conclusion, transcribed here so that §3's
census and §4's realization can both be stated against it upstream. -/
def LiveConclusion (Lat : PeriodicLatticeExtent) (Uconfig : Type*) [Nontrivial Uconfig]
    (ell : ℕ) : Prop :=
  ∃ cohyp : AdalyFormal.Balaban.CoercivityHypothesis
      (AdalyFormal.Balaban.Anchoring.AnchoredBondSpace Lat) Uconfig,
    cohyp.V = AdalyFormal.Balaban.Anchoring.anchoredVInter (Lat := Lat) ell ∧
    (∀ (k : ℕ) (U : Uconfig), (cohyp.Δ k U).adjoint = cohyp.Δ k U) ∧
    (∀ (k : ℕ) (U : Uconfig) (v : AdalyFormal.Balaban.Anchoring.AnchoredBondSpace Lat),
      0 ≤ (inner ℝ v (cohyp.Δ k U v) : ℝ)) ∧
    (∀ (k : ℕ) (U : Uconfig) (c : ℝ), cohyp.Δ k U
      ≠ c • ContinuousLinearMap.id ℝ (AdalyFormal.Balaban.Anchoring.AnchoredBondSpace Lat)) ∧
    (∃ (U : Uconfig) (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧ cohyp.Δ k₁ U ≠ cohyp.Δ k₂ U)

/-- The strengthening is a genuine one: it implies the live conclusion. -/
theorem liveConclusion_of_kernelStrengthened {Uconfig : Type*} [Nontrivial Uconfig] {ell : ℕ}
    (h : KernelStrengthened Lat Uconfig ell) : LiveConclusion Lat Uconfig ell := by
  obtain ⟨c, h1, h2, h3, h4, h5, -, -, -⟩ := h
  exact ⟨c, h1, h2, h3, h4, h5⟩

/-! ## §3 — the junk witness, rebuilt upstream

`Δ k U = id + (k + colour U) • P_{span e_A}`: the identity plus a positive multiple of a rank-one
coordinate projection, `k` entering only as a coefficient. No coarsening, no block structure, no
covariant derivative, no gauge geometry — and, per §1, no cardinality hypothesis on `Lat` either:
the two bonds used are two DIRECTIONS at one site. -/

section Junk

variable {Uconfig : Type*} [Nontrivial Uconfig]

noncomputable def eA : HH Lat := EuclideanSpace.single (bondA (Lat := Lat)) (1 : ℝ)

noncomputable def eB : HH Lat := EuclideanSpace.single (bondB (Lat := Lat)) (1 : ℝ)

/-- `span {e_A}`, a proper nonzero subspace by §1. -/
noncomputable def jW : Submodule ℝ (HH Lat) := Submodule.span ℝ {eA (Lat := Lat)}

noncomputable def u₀ (Uconfig : Type*) [Nontrivial Uconfig] : Uconfig :=
  Classical.choose (exists_pair_ne Uconfig)

noncomputable def u₁ (Uconfig : Type*) [Nontrivial Uconfig] : Uconfig :=
  Classical.choose (Classical.choose_spec (exists_pair_ne Uconfig))

theorem u₀_ne_u₁ (Uconfig : Type*) [Nontrivial Uconfig] : u₀ Uconfig ≠ u₁ Uconfig :=
  Classical.choose_spec (Classical.choose_spec (exists_pair_ne Uconfig))

open Classical in
/-- Two distinct positive values, so every family below genuinely depends on `U`. -/
noncomputable def ucoef {Uconfig : Type*} [Nontrivial Uconfig] (U : Uconfig) : ℝ :=
  if U = u₀ Uconfig then 1 else 2

theorem ucoef_pos (U : Uconfig) : 0 < ucoef U := by unfold ucoef; split <;> norm_num

theorem one_le_ucoef (U : Uconfig) : (1 : ℝ) ≤ ucoef U := by unfold ucoef; split <;> norm_num

theorem ucoef_u₀ : ucoef (u₀ Uconfig) = 1 := by unfold ucoef; rw [if_pos rfl]

theorem ucoef_u₁ : ucoef (u₁ Uconfig) = 2 := by
  unfold ucoef; rw [if_neg (u₀_ne_u₁ Uconfig).symm]

/-- The junk coefficient: `k` enters as a scalar, `U` only through a two-valued colouring. -/
noncomputable def jg (k : ℕ) (U : Uconfig) : ℝ := (k : ℝ) + ucoef U

theorem jg_pos (k : ℕ) (U : Uconfig) : 0 < jg k U := by
  have := ucoef_pos (Uconfig := Uconfig) U
  unfold jg; positivity

/-- **The junk operator.** -/
noncomputable def jDelta (k : ℕ) (U : Uconfig) : HH Lat →L[ℝ] HH Lat :=
  ContinuousLinearMap.id ℝ (HH Lat) + jg k U • (jW (Lat := Lat)).starProjection

theorem eA_ne_zero : eA (Lat := Lat) ≠ 0 := single_ne_zero _

theorem eB_ne_zero : eB (Lat := Lat) ≠ 0 := single_ne_zero _

theorem eA_mem_jW : eA (Lat := Lat) ∈ jW (Lat := Lat) :=
  Submodule.mem_span_singleton_self _

theorem inner_eA_eB : (inner ℝ (eA (Lat := Lat)) (eB (Lat := Lat)) : ℝ) = 0 :=
  inner_single_single_of_ne bondA_ne_bondB

theorem jproj_eA : (jW (Lat := Lat)).starProjection (eA (Lat := Lat)) = eA (Lat := Lat) :=
  Submodule.starProjection_eq_self_iff.mpr eA_mem_jW

theorem jproj_eB : (jW (Lat := Lat)).starProjection (eB (Lat := Lat)) = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff (jW (Lat := Lat))).mpr
    ((Submodule.mem_orthogonal_singleton_iff_inner_right).mpr inner_eA_eB)

/-- `id + positive · projection` is coercive with constant `1` on the WHOLE space. -/
theorem jDelta_coercive (k : ℕ) (U : Uconfig) (v : HH Lat) :
    (1 : ℝ) * ‖v‖ ^ 2 ≤ (inner ℝ v (jDelta (Lat := Lat) k U v) : ℝ) := by
  have hp : 0 ≤ (inner ℝ v ((jW (Lat := Lat)).starProjection v) : ℝ) := by
    have := (jW (Lat := Lat)).re_inner_starProjection_nonneg v
    simpa [real_inner_comm] using this
  rw [jDelta]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, one_mul]
  exact le_add_of_nonneg_right (mul_nonneg (le_of_lt (jg_pos k U)) hp)

theorem jDelta_adjoint (k : ℕ) (U : Uconfig) :
    (jDelta (Lat := Lat) k U).adjoint = jDelta (Lat := Lat) k U := by
  apply (ContinuousLinearMap.isSelfAdjoint_iff').mp
  apply (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr
  change (LinearMap.id
      + jg k U • ((jW (Lat := Lat)).starProjection : HH Lat →ₗ[ℝ] HH Lat)).IsSymmetric
  exact LinearMap.IsSymmetric.id.add
    (LinearMap.IsSymmetric.smul (by simp) (jW (Lat := Lat)).starProjection_isSymmetric)

theorem jDelta_psd (k : ℕ) (U : Uconfig) (v : HH Lat) :
    0 ≤ (inner ℝ v (jDelta (Lat := Lat) k U v) : ℝ) :=
  le_trans (sq_nonneg ‖v‖) (by simpa using jDelta_coercive (Lat := Lat) k U v)

theorem jDelta_not_scalar (k : ℕ) (U : Uconfig) (c : ℝ) :
    jDelta (Lat := Lat) k U ≠ c • ContinuousLinearMap.id ℝ (HH Lat) := by
  intro hsc
  have h1 := DFunLike.congr_fun hsc (eB (Lat := Lat))
  have h0 := DFunLike.congr_fun hsc (eA (Lat := Lat))
  simp only [jDelta, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, jproj_eB, smul_zero, add_zero] at h1
  have hc : c = 1 := by
    have hz : (1 - c) • eB (Lat := Lat) = 0 := by
      simpa [sub_smul] using sub_eq_zero.mpr h1
    rcases smul_eq_zero.mp hz with h | h
    · linarith
    · exact absurd h eB_ne_zero
  simp only [jDelta, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, jproj_eA, hc, one_smul] at h0
  have hz : jg k U • eA (Lat := Lat) = 0 := by
    apply add_left_cancel (a := eA (Lat := Lat))
    simpa using h0
  rcases smul_eq_zero.mp hz with h | h
  · exact (ne_of_gt (jg_pos k U)) h
  · exact eA_ne_zero h

theorem jDelta_U_nonconstant :
    jDelta (Lat := Lat) 0 (u₀ Uconfig) ≠ jDelta (Lat := Lat) 0 (u₁ Uconfig) := by
  intro h
  have he := DFunLike.congr_fun h (eA (Lat := Lat))
  simp only [jDelta, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, jproj_eA, jg, ucoef_u₀, ucoef_u₁,
    Nat.cast_zero, zero_add] at he
  have hz : ((1 : ℝ) - 2) • eA (Lat := Lat) = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr (add_left_cancel he)
  rcases smul_eq_zero.mp hz with hs | hv
  · norm_num at hs
  · exact eA_ne_zero hv

theorem jDelta_k_nonconstant (U : Uconfig) :
    jDelta (Lat := Lat) 0 U ≠ jDelta (Lat := Lat) 1 U := by
  intro h
  have he := DFunLike.congr_fun h (eA (Lat := Lat))
  simp only [jDelta, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, jproj_eA] at he
  have hcoef : jg (Uconfig := Uconfig) 0 U = jg (Uconfig := Uconfig) 1 U := by
    have hz : (jg (Uconfig := Uconfig) 0 U - jg (Uconfig := Uconfig) 1 U)
        • eA (Lat := Lat) = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr (add_left_cancel he)
    rcases smul_eq_zero.mp hz with hs | hv
    · linarith [sub_eq_zero.mp hs]
    · exact absurd hv eA_ne_zero
  unfold jg at hcoef
  norm_num at hcoef

/-- The junk `CoercivityHypothesis`: every field discharged, at every `ell`. -/
noncomputable def jCohyp (Uconfig : Type*) [Nontrivial Uconfig] (ell : ℕ) :
    AdalyFormal.Balaban.CoercivityHypothesis (HH Lat) Uconfig where
  Δ := jDelta
  V := AdalyFormal.Balaban.Anchoring.anchoredVInter ell
  V_ne_bot := AdalyFormal.Balaban.Anchoring.anchoredVInter_ne_bot ell
  Δ_nonconstant := ⟨0, u₀ Uconfig, u₁ Uconfig, u₀_ne_u₁ Uconfig, jDelta_U_nonconstant⟩
  γ'' := 1
  γ''_pos := one_pos
  coercive := by
    intro k U v _
    exact jDelta_coercive k U v

/-- **THE CENSUS, UPSTREAM.** Every conjunct of `Spine.coerc_u_main`'s live conclusion is satisfied
by an operator with no lattice content, for every `Lat`, every `ell`, and every nontrivial
`Uconfig`. (Downstream twin: `CoercUMainRepair.junk_satisfies_OldConclusion`.) -/
theorem jDelta_satisfies_five_conjuncts (Uconfig : Type*) [Nontrivial Uconfig] (ell : ℕ) :
    LiveConclusion Lat Uconfig ell := by
  refine ⟨jCohyp Uconfig ell, rfl, ?_, ?_, ?_, u₀ Uconfig, 0, 1, by norm_num, ?_⟩
  · exact jDelta_adjoint
  · exact jDelta_psd
  · exact jDelta_not_scalar
  · exact jDelta_k_nonconstant _

/-- `id + PSD` is injective — the single fact that kills the witness. -/
theorem jDelta_injective (k : ℕ) (U : Uconfig) {v : HH Lat}
    (h : jDelta (Lat := Lat) k U v = 0) : v = 0 := by
  have hc := jDelta_coercive (Lat := Lat) k U v
  rw [h, inner_zero_right, one_mul] at hc
  have hn : ‖v‖ = 0 := by nlinarith [norm_nonneg v, sq_nonneg ‖v‖]
  exact norm_eq_zero.mp hn

/-- **MUST-FIRE (a).** The junk operator has no kernel, so it fails K1. -/
theorem jDelta_fails_HasKernel :
    ¬ HasKernel (Lat := Lat) (Uconfig := Uconfig) jDelta := by
  intro h
  obtain ⟨w, hw, hw0⟩ := h 0 (u₀ Uconfig)
  exact hw (jDelta_injective 0 _ hw0)

/-- **MUST-FIRE (b).** Its kernel never grows either, so it fails K3. -/
theorem jDelta_fails_KernelGrows :
    ¬ KernelGrows (Lat := Lat) (Uconfig := Uconfig) jDelta := by
  rintro ⟨k, U, w, hne, hz⟩
  exact hne (by rw [jDelta_injective (k + 1) U hz]; simp)

/-- **Layer necessity.** The junk operator DOES satisfy K2 (vacuously — trivial kernel at every
scale), so K2 alone would not have rejected it. K1 is what fires. -/
theorem jDelta_satisfies_KernelMono :
    KernelMono (Lat := Lat) (Uconfig := Uconfig) jDelta := by
  intro k U v hv
  rw [jDelta_injective k U hv]
  simp

/-- **THE REJECTION, headline.** The exact `CoercivityHypothesis` that inhabits the live conclusion
does NOT inhabit `KernelStrengthened`. Same witness, two statements. -/
theorem kernelStrengthened_rejects_junk (ell : ℕ)
    (h : (jCohyp (Lat := Lat) Uconfig ell).V
          = AdalyFormal.Balaban.Anchoring.anchoredVInter (Lat := Lat) ell ∧
        (∀ (k : ℕ) (U : Uconfig), ((jCohyp (Lat := Lat) Uconfig ell).Δ k U).adjoint
          = (jCohyp (Lat := Lat) Uconfig ell).Δ k U) ∧
        (∀ (k : ℕ) (U : Uconfig) (v : HH Lat),
          0 ≤ (inner ℝ v ((jCohyp (Lat := Lat) Uconfig ell).Δ k U v) : ℝ)) ∧
        (∀ (k : ℕ) (U : Uconfig) (c : ℝ), (jCohyp (Lat := Lat) Uconfig ell).Δ k U
          ≠ c • ContinuousLinearMap.id ℝ (HH Lat)) ∧
        (∃ (U : Uconfig) (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧ (jCohyp (Lat := Lat) Uconfig ell).Δ k₁ U
          ≠ (jCohyp (Lat := Lat) Uconfig ell).Δ k₂ U) ∧
        HasKernel (jCohyp (Lat := Lat) Uconfig ell).Δ ∧
        KernelMono (jCohyp (Lat := Lat) Uconfig ell).Δ ∧
        KernelGrows (jCohyp (Lat := Lat) Uconfig ell).Δ) : False :=
  jDelta_fails_HasKernel (Lat := Lat) (Uconfig := Uconfig) h.2.2.2.2.2.1

end Junk

/-! ## §4 — CHAIN REALIZATION: every kernel chain inside `Vᗮ` is met by a scaled projector

`Δ k U := ucoef U • P_{(K k)ᗮ}` has `ker (Δ k U) = K k` EXACTLY, is self-adjoint and PSD, is
non-scalar as soon as `K 0 ≠ ⊥`, and — because `K k ≤ Vᗮ` forces `V ≤ (K k)ᗮ` — acts as
`ucoef U • id` on `V`, hence is coercive there with `γ'' = 1`. So ANY demand on the kernel chain
that some chain inside `Vᗮ` satisfies is satisfied by an operator family whose only lattice input is
the chain itself. -/

section Chain

variable {Uconfig : Type*} [Nontrivial Uconfig]

/-- The scaled-projector family attached to a subspace chain. -/
noncomputable def chainDelta (K : ℕ → Submodule ℝ (HH Lat)) (k : ℕ) (U : Uconfig) :
    HH Lat →L[ℝ] HH Lat :=
  ucoef U • (K k)ᗮ.starProjection

theorem chainDelta_apply (K : ℕ → Submodule ℝ (HH Lat)) (k : ℕ) (U : Uconfig) (v : HH Lat) :
    chainDelta (Lat := Lat) K k U v = ucoef U • (K k)ᗮ.starProjection v := rfl

/-- **The kernel is EXACTLY `K k`.** -/
theorem chainDelta_eq_zero_iff (K : ℕ → Submodule ℝ (HH Lat)) (k : ℕ) (U : Uconfig)
    (v : HH Lat) : chainDelta (Lat := Lat) K k U v = 0 ↔ v ∈ K k := by
  rw [chainDelta_apply, smul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (ne_of_gt (ucoef_pos U))
    · have := (Submodule.starProjection_apply_eq_zero_iff (K k)ᗮ).mp h
      rwa [Submodule.orthogonal_orthogonal] at this
  · intro hv
    refine Or.inr ((Submodule.starProjection_apply_eq_zero_iff _).mpr ?_)
    rw [Submodule.orthogonal_orthogonal]
    exact hv

theorem chainDelta_adjoint (K : ℕ → Submodule ℝ (HH Lat)) (k : ℕ) (U : Uconfig) :
    (chainDelta (Lat := Lat) K k U).adjoint = chainDelta (Lat := Lat) K k U := by
  apply (ContinuousLinearMap.isSelfAdjoint_iff').mp
  apply (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr
  change (ucoef U • (((K k)ᗮ).starProjection : HH Lat →ₗ[ℝ] HH Lat)).IsSymmetric
  exact LinearMap.IsSymmetric.smul (by simp) ((K k)ᗮ).starProjection_isSymmetric

theorem inner_starProjection_self (K : Submodule ℝ (HH Lat)) (v : HH Lat) :
    (inner ℝ v (K.starProjection v) : ℝ) = ‖K.starProjection v‖ ^ 2 := by
  have hsplit : K.starProjection v + Kᗮ.starProjection v = v :=
    K.starProjection_add_starProjection_orthogonal v
  have hcross : (inner ℝ (Kᗮ.starProjection v) (K.starProjection v) : ℝ) = 0 := by
    have hm1 : Kᗮ.starProjection v ∈ Kᗮ := Submodule.starProjection_apply_mem _ _
    have hm2 : K.starProjection v ∈ K := Submodule.starProjection_apply_mem _ _
    have := (Submodule.mem_orthogonal K (Kᗮ.starProjection v)).mp hm1 _ hm2
    rw [real_inner_comm] at this
    exact this
  calc (inner ℝ v (K.starProjection v) : ℝ)
      = inner ℝ (K.starProjection v + Kᗮ.starProjection v) (K.starProjection v) := by rw [hsplit]
    _ = ‖K.starProjection v‖ ^ 2 := by
        rw [inner_add_left, hcross, add_zero, real_inner_self_eq_norm_sq]

theorem chainDelta_psd (K : ℕ → Submodule ℝ (HH Lat)) (k : ℕ) (U : Uconfig) (v : HH Lat) :
    0 ≤ (inner ℝ v (chainDelta (Lat := Lat) K k U v) : ℝ) := by
  rw [chainDelta_apply, inner_smul_right, inner_starProjection_self]
  exact mul_nonneg (le_of_lt (ucoef_pos U)) (sq_nonneg _)

/-- `K ≤ Vᗮ` forces `V ≤ Kᗮ`, so the projector acts as the identity on `V`. -/
theorem mem_orthogonal_of_le_orthogonal {K V : Submodule ℝ (HH Lat)} (hK : K ≤ Vᗮ)
    {v : HH Lat} (hv : v ∈ V) : v ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal]
  intro x hx
  have h := (Submodule.mem_orthogonal V x).mp (hK hx) v hv
  rw [real_inner_comm] at h
  exact h

theorem chainDelta_on_V {K : ℕ → Submodule ℝ (HH Lat)} {V : Submodule ℝ (HH Lat)}
    (hK : ∀ k, K k ≤ Vᗮ) (k : ℕ) (U : Uconfig) {v : HH Lat} (hv : v ∈ V) :
    chainDelta (Lat := Lat) K k U v = ucoef U • v := by
  rw [chainDelta_apply, Submodule.starProjection_eq_self_iff.mpr
    (mem_orthogonal_of_le_orthogonal (hK k) hv)]

/-- **THE REALIZATION THEOREM.** A monotone chain inside `Vᗮ`, nonzero at rung `0`, with one strict
jump, is enough to inhabit the WHOLE strengthened conclusion. -/
theorem kernelStrengthened_of_chain {ell : ℕ} (K : ℕ → Submodule ℝ (HH Lat))
    (hmono : ∀ k, K k ≤ K (k + 1))
    (hperp : ∀ k, K k ≤ (VV (Lat := Lat) ell)ᗮ)
    (hbot : K 0 ≠ ⊥) {k₀ : ℕ} (hjump : K k₀ ≠ K (k₀ + 1)) :
    KernelStrengthened Lat Uconfig ell := by
  classical
  -- a nonzero vector of `V`, on which every rung is nonzero
  obtain ⟨v₀, hv₀V, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (AdalyFormal.Balaban.Anchoring.anchoredVInter_ne_bot (Lat := Lat) ell)
  have hv₀nz : ∀ (k : ℕ) (U : Uconfig), chainDelta (Lat := Lat) K k U v₀ ≠ 0 := by
    intro k U h
    rw [chainDelta_on_V hperp k U hv₀V] at h
    rcases smul_eq_zero.mp h with hs | hv
    · exact (ne_of_gt (ucoef_pos U)) hs
    · exact hv₀ne hv
  -- a nonzero kernel vector at rung `0`, hence at every rung
  obtain ⟨u, huK, hune⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hu_mem : ∀ k : ℕ, u ∈ K k := by
    intro k
    induction k with
    | zero => exact huK
    | succ n ih => exact hmono n ih
  -- the strict jump gives a vector that dies exactly one rung later
  obtain ⟨w, hwmem, hwnot⟩ : ∃ w, w ∈ K (k₀ + 1) ∧ w ∉ K k₀ := by
    by_contra hcon
    refine hjump (le_antisymm (hmono k₀) ?_)
    intro z hz
    by_contra hzn
    exact hcon ⟨z, hz, hzn⟩
  refine ⟨{ Δ := chainDelta (Lat := Lat) K
            V := VV (Lat := Lat) ell
            V_ne_bot := AdalyFormal.Balaban.Anchoring.anchoredVInter_ne_bot ell
            Δ_nonconstant := ⟨0, u₀ Uconfig, u₁ Uconfig, u₀_ne_u₁ Uconfig, ?_⟩
            γ'' := 1
            γ''_pos := one_pos
            coercive := ?_ }, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `U`-nonconstancy, on `v₀`
    intro hEq
    have he := DFunLike.congr_fun hEq v₀
    rw [chainDelta_on_V hperp 0 (u₀ Uconfig) hv₀V,
      chainDelta_on_V hperp 0 (u₁ Uconfig) hv₀V, ucoef_u₀, ucoef_u₁] at he
    have hz : ((1 : ℝ) - 2) • v₀ = 0 := by
      rw [sub_smul]; exact sub_eq_zero.mpr he
    rcases smul_eq_zero.mp hz with hs | hv
    · norm_num at hs
    · exact hv₀ne hv
  · -- coercivity on `V`, with `γ'' = 1`
    intro k U v hv
    rw [chainDelta_on_V hperp k U hv, real_inner_smul_right, real_inner_self_eq_norm_sq, one_mul]
    nlinarith [one_le_ucoef (Uconfig := Uconfig) U, sq_nonneg ‖v‖]
  · exact fun k U => chainDelta_adjoint K k U
  · exact fun k U v => chainDelta_psd K k U v
  · -- non-scalarity: `u` is killed, `v₀` is not
    intro k U c hsc
    have h1 := DFunLike.congr_fun hsc u
    rw [(chainDelta_eq_zero_iff (Lat := Lat) K k U u).mpr (hu_mem k)] at h1
    have hc : c = 0 := by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at h1
      rcases smul_eq_zero.mp h1.symm with h | h
      · exact h
      · exact absurd h hune
    have h2 := DFunLike.congr_fun hsc v₀
    -- `rw` + `simpa`, NOT a bare `simp only`: with `zero_smul` alone the goal is left as
    -- `… = (0 : H →L[ℝ] H) v₀`, and whether `simp only` closes that gap turned out to differ
    -- between `lake build` and `lake env lean` on this same file (measured, 2026-07-30).
    rw [hc, zero_smul] at h2
    exact hv₀nz k U (by simpa using h2)
  · -- genuine `k`-dependence: `w` survives rung `k₀` and dies at rung `k₀ + 1`
    refine ⟨u₀ Uconfig, k₀, k₀ + 1, by omega, ?_⟩
    intro hEq
    have h0 : chainDelta (Lat := Lat) K k₀ (u₀ Uconfig) w ≠ 0 := by
      intro h
      exact hwnot ((chainDelta_eq_zero_iff (Lat := Lat) K k₀ (u₀ Uconfig) w).mp h)
    exact h0 ((DFunLike.congr_fun hEq w).trans
      ((chainDelta_eq_zero_iff (Lat := Lat) K (k₀ + 1) (u₀ Uconfig) w).mpr hwmem))
  · -- K1
    exact fun k U => ⟨u, hune, (chainDelta_eq_zero_iff (Lat := Lat) K k U u).mpr (hu_mem k)⟩
  · -- K2
    intro k U v hv
    exact (chainDelta_eq_zero_iff (Lat := Lat) K (k + 1) U v).mpr
      (hmono k ((chainDelta_eq_zero_iff (Lat := Lat) K k U v).mp hv))
  · -- K3
    refine ⟨k₀, u₀ Uconfig, w, ?_, ?_⟩
    · intro h
      exact hwnot ((chainDelta_eq_zero_iff (Lat := Lat) K k₀ (u₀ Uconfig) w).mp h)
    · exact (chainDelta_eq_zero_iff (Lat := Lat) K (k₀ + 1) (u₀ Uconfig) w).mpr hwmem

end Chain

/-! ### §4b — the chain built from two forced bonds

`(2.121)` forces a bond `b` to vanish on `V`, so `e_b ∈ Vᗮ`. TWO distinct forced bonds give the
chain `span {e_{b₁}} ⊆ span {e_{b₁}, e_{b₂}}`, which is monotone, nonzero and strictly increasing
— exactly §4's hypotheses. -/

/-- **The bridge from the lattice to `Vᗮ`.** Every staircase bond of a valid `(y, x)` pair yields a
coordinate vector orthogonal to `anchoredVInter ell`. -/
theorem single_mem_anchoredVInter_orthogonal {ell : ℕ} {y x : PeriodicLatticeSite Lat}
    (hy : y ∈ CoarseLattice Lat ell) (hx : x ∈ blockOf y ell)
    {b : Bond Lat} (hb : b ∈ staircasePath y x) :
    (EuclideanSpace.single b (1 : ℝ) : HH Lat) ∈ (VV (Lat := Lat) ell)ᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro u hu
  rw [show (VV (Lat := Lat) ell) = AdalyFormal.Balaban.Anchoring.anchoredVInter (Lat := Lat) ell
    from rfl, AdalyFormal.Balaban.Anchoring.anchoredVInter, Submodule.mem_map] at hu
  obtain ⟨B, hB, rfl⟩ := hu
  rw [EuclideanSpace.inner_single_right]
  have : B b = 0 := (mem_admissibleSubspaceInter.mp hB) y hy x hx b hb
  simp [this]

/-- Every forced bond's coordinate vector lies in `Vᗮ`. -/
theorem single_mem_orthogonal_of_mem_forcedBonds {ell : ℕ} {b : Bond Lat}
    (hb : b ∈ forcedBonds Lat ell) :
    (EuclideanSpace.single b (1 : ℝ) : HH Lat) ∈ (VV (Lat := Lat) ell)ᗮ := by
  obtain ⟨y, hy, x, hx, hbp⟩ := mem_forcedBonds.mp hb
  exact single_mem_anchoredVInter_orthogonal hy hx hbp

/-- The two-step chain `span {w₁} ⊆ span {w₁, w₂}`. A named `def` (not an inline `match`) so that
its two reduction lemmas are available to `rw`. -/
noncomputable def twoStepChain (w₁ w₂ : HH Lat) : ℕ → Submodule ℝ (HH Lat)
  | 0 => Submodule.span ℝ {w₁}
  | _ + 1 => Submodule.span ℝ {w₁, w₂}

theorem twoStepChain_zero (w₁ w₂ : HH Lat) :
    twoStepChain (Lat := Lat) w₁ w₂ 0 = Submodule.span ℝ {w₁} := rfl

theorem twoStepChain_succ (w₁ w₂ : HH Lat) (k : ℕ) :
    twoStepChain (Lat := Lat) w₁ w₂ (k + 1) = Submodule.span ℝ {w₁, w₂} := rfl

/-- **SATISFIABILITY from two forced bonds.** -/
theorem kernelStrengthened_of_two_forced_bonds {Uconfig : Type*} [Nontrivial Uconfig] {ell : ℕ}
    {b₁ b₂ : Bond Lat} (h₁ : b₁ ∈ forcedBonds Lat ell) (h₂ : b₂ ∈ forcedBonds Lat ell)
    (hne : b₁ ≠ b₂) : KernelStrengthened Lat Uconfig ell := by
  classical
  have hw₁perp : (EuclideanSpace.single b₁ (1 : ℝ) : HH Lat) ∈ (VV (Lat := Lat) ell)ᗮ :=
    single_mem_orthogonal_of_mem_forcedBonds h₁
  have hw₂perp : (EuclideanSpace.single b₂ (1 : ℝ) : HH Lat) ∈ (VV (Lat := Lat) ell)ᗮ :=
    single_mem_orthogonal_of_mem_forcedBonds h₂
  refine kernelStrengthened_of_chain
    (K := twoStepChain (EuclideanSpace.single b₁ (1 : ℝ) : HH Lat)
      (EuclideanSpace.single b₂ (1 : ℝ) : HH Lat)) ?_ ?_ ?_ (k₀ := 0) ?_
  · intro k
    cases k with
    | zero =>
        rw [twoStepChain_zero, twoStepChain_succ]
        refine Submodule.span_mono ?_
        intro z hz
        simp only [Set.mem_singleton_iff] at hz
        subst hz
        simp
    | succ n => rw [twoStepChain_succ, twoStepChain_succ]
  · intro k
    cases k with
    | zero =>
        rw [twoStepChain_zero, Submodule.span_le, Set.singleton_subset_iff]
        exact hw₁perp
    | succ n =>
        rw [twoStepChain_succ, Submodule.span_le, Set.insert_subset_iff,
          Set.singleton_subset_iff]
        exact ⟨hw₁perp, hw₂perp⟩
  · rw [twoStepChain_zero]
    exact span_single_ne_bot b₁
  · -- strict jump: `e_{b₂} ∉ span {e_{b₁}}`
    rw [twoStepChain_zero, twoStepChain_succ]
    intro hEq
    have hmem : (EuclideanSpace.single b₂ (1 : ℝ) : HH Lat)
        ∈ Submodule.span ℝ {(EuclideanSpace.single b₁ (1 : ℝ) : HH Lat)} := by
      rw [hEq]
      exact Submodule.subset_span (by simp)
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    have h2 : (inner ℝ (EuclideanSpace.single b₂ (1 : ℝ) : HH Lat)
          (EuclideanSpace.single b₂ (1 : ℝ) : HH Lat) : ℝ)
        = t * inner ℝ (EuclideanSpace.single b₂ (1 : ℝ) : HH Lat)
            (EuclideanSpace.single b₁ (1 : ℝ) : HH Lat) := by
      rw [← real_inner_smul_right, ht]
    rw [inner_single_single_self b₂, inner_single_single_of_ne (Ne.symm hne), mul_zero] at h2
    norm_num at h2

/-- **THE MEASUREMENT.** `NonDegenerate Lat ell` — the weakest guard under which any kernel-carrying
strengthening can be true (`§6`, and `LatDegeneracy.newConclusion_iff_nonDegenerate` downstream) —
already IMPLIES the strengthened conclusion, sorry-free, by an operator whose only lattice input is
a pair of forced bonds. So `KernelStrengthened` is satisfiable; and it is not merely satisfiable at
a witness point, it is a THEOREM on the whole guarded range. -/
theorem kernelStrengthened_of_nonDegenerate {Uconfig : Type*} [Nontrivial Uconfig] {ell : ℕ}
    (h : NonDegenerate Lat ell) : KernelStrengthened Lat Uconfig ell := by
  have hcard : 1 < (forcedBonds Lat ell).card := by unfold NonDegenerate at h; omega
  obtain ⟨b₁, h₁, b₂, h₂, hne⟩ := Finset.one_lt_card.mp hcard
  exact kernelStrengthened_of_two_forced_bonds h₁ h₂ hne

/-! ## §5 — the finite-dimensional ceiling: no kernel growth at EVERY rung

The carrier is `EuclideanSpace ℝ (Bond Lat)` with `Bond Lat` a `Fintype`, so it is
finite-dimensional. A kernel chain that is monotone and strictly increasing at every rung would have
`finrank ≥ k` at rung `k`, exceeding `Fintype.card (Bond Lat)`. Hence K3's "the nesting is strict
SOMEWHERE" is the strongest kernel-growth demand that can be true uniformly in `k`, and §4 satisfies
it with a projector. -/

section Ceiling

variable {Uconfig : Type*}

/-- The kernel of a rung, as a submodule. -/
noncomputable def rungKer (Δ : ℕ → Uconfig → HH Lat →L[ℝ] HH Lat) (k : ℕ) (U : Uconfig) :
    Submodule ℝ (HH Lat) :=
  LinearMap.ker (Δ k U : HH Lat →ₗ[ℝ] HH Lat)

theorem mem_rungKer {Δ : ℕ → Uconfig → HH Lat →L[ℝ] HH Lat} {k : ℕ} {U : Uconfig} {v : HH Lat} :
    v ∈ rungKer Δ k U ↔ Δ k U v = 0 := LinearMap.mem_ker

/-- **THE CEILING.** No operator family on this carrier forgets something new at EVERY rung. -/
theorem no_kernel_growth_at_every_rung (Δ : ℕ → Uconfig → HH Lat →L[ℝ] HH Lat) (U : Uconfig)
    (hmono : ∀ (k : ℕ) (v : HH Lat), Δ k U v = 0 → Δ (k + 1) U v = 0)
    (hgrow : ∀ k : ℕ, ∃ w : HH Lat, Δ k U w ≠ 0 ∧ Δ (k + 1) U w = 0) : False := by
  have hlt : ∀ k : ℕ, rungKer Δ k U < rungKer Δ (k + 1) U := by
    intro k
    refine lt_of_le_of_ne (fun v hv => mem_rungKer.mpr (hmono k v (mem_rungKer.mp hv))) ?_
    obtain ⟨w, hw1, hw2⟩ := hgrow k
    intro hEq
    exact hw1 (mem_rungKer.mp (hEq ▸ mem_rungKer.mpr hw2))
  have hrank : ∀ k : ℕ, k ≤ Module.finrank ℝ (rungKer Δ k U) := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        have := Submodule.finrank_lt_finrank_of_lt (hlt n)
        omega
  have hbound : Module.finrank ℝ (rungKer Δ (Fintype.card (Bond Lat) + 1) U)
      ≤ Fintype.card (Bond Lat) := by
    have h1 : Module.finrank ℝ (rungKer Δ (Fintype.card (Bond Lat) + 1) U)
        ≤ Module.finrank ℝ (HH Lat) := Submodule.finrank_le _
    have h2 : Module.finrank ℝ (HH Lat) = Fintype.card (Bond Lat) := finrank_euclideanSpace
    omega
  have := hrank (Fintype.card (Bond Lat) + 1)
  omega

end Ceiling

/-! ## §6 — the `V = ⊤` collision: where the pinned `V` is everything, K1 is unsatisfiable

Upstream twin of `EllDegeneracy.no_hasKernel_at_ell_le_one`. `CoercivityHypothesis.coercive` with
`0 < γ''` forces injectivity on `V`; at `V = ⊤` that is injectivity everywhere. -/

/-- **No kernel where `V` is the whole carrier.** -/
theorem no_hasKernel_of_V_eq_top {Uconfig : Type*} [Nontrivial Uconfig] {ell : ℕ}
    (hV : VV (Lat := Lat) ell = ⊤)
    (cohyp : AdalyFormal.Balaban.CoercivityHypothesis (HH Lat) Uconfig)
    (hVeq : cohyp.V = VV (Lat := Lat) ell) : ¬ HasKernel cohyp.Δ := by
  intro hker
  obtain ⟨U₀⟩ : Nonempty Uconfig := ⟨Classical.choose (exists_pair_ne Uconfig)⟩
  obtain ⟨w, hw, hw0⟩ := hker 0 U₀
  refine hw (AdalyFormal.Balaban.RGLadderCore.eq_zero_of_coercive_of_apply_eq_zero
    (cohyp.Δ 0 U₀) cohyp.V cohyp.γ'' cohyp.γ''_pos (cohyp.coercive 0 U₀) ?_ hw0)
  rw [hVeq, hV]
  exact Submodule.mem_top

/-- **The strengthened conclusion is REFUTABLE**, and it is refuted exactly where the pinned `V`
degenerates to the whole carrier. So the guard is not decoration: any kernel-carrying strengthening
of `coerc_u_main` is FALSE on the degenerate range. -/
theorem kernelStrengthened_false_of_V_eq_top {Uconfig : Type*} [Nontrivial Uconfig] {ell : ℕ}
    (hV : VV (Lat := Lat) ell = ⊤) : ¬ KernelStrengthened Lat Uconfig ell := by
  rintro ⟨cohyp, hVeq, -, -, -, -, hker, -, -⟩
  exact no_hasKernel_of_V_eq_top hV cohyp hVeq hker

/-! ## §6a — WHERE THE NEXT DEMAND HAS TO LIVE, with both controls compiled

§4 + §5 bound the kernel route: a demand on the kernel chain alone is either false (growth at every
rung) or met by `chainDelta`. The precise sense in which `chainDelta` is content-free is not an
adjective — it is a theorem: **`chainDelta` is a SCALED PROJECTION**,
`Δ ∘ Δ = ucoef U • Δ` (`chainDelta_is_scaled_projection`). Its whole spectrum off the kernel is one
number. So the next demand has to constrain `Δ` OFF its kernel, and the cheapest such demand
statable at this carrier is:

    K5   ∀ k U, ∀ c : ℝ, (Δ k U) ∘ (Δ k U) ≠ c • (Δ k U)

Both controls are compiled here, and they point in OPPOSITE directions, which is the point:

* `chainDelta_fails_NotScaledProjection` — K5 REJECTS §4's projector family, the witness that makes
  the kernel bundle a theorem. So K5 is not implied by K1/K2/K3.
* `jDelta_satisfies_NotScaledProjection` — K5 does NOT reject the junk witness (`jDelta` has two
  distinct nonzero eigenvalues, so it is not a scaled projection). So K5 is not a substitute for K1
  either.

Hence `K1 ∧ K5` rejects BOTH content-free families known to this tree, which neither conjunct does
alone.

**⚠ WHAT IS NOT ESTABLISHED, and the lesson of this whole module.** Nothing here shows `K1 ∧ K5`
(with the rest) is SATISFIABLE, and nothing here shows it is not satisfiable by yet another
content-free family. This module's own headline is that a strengthening can reject every witness
anyone has built and still be a THEOREM (`kernelStrengthened_of_nonDegenerate`) — rejection of the
known witnesses is NOT evidence of content. So K5 must not be adopted into
`Spine.coerc_u_main` until someone has done for it what §4 did for K1/K2/K3: exhibited the general
inhabitant, or proved there is none. A weighted sum of orthogonal projections with three distinct
positive weights is the first candidate to try to refute it with; that computation is not done here
and is NOT claimed either way. -/

/-- **K5 — `Δ` is not a scaled orthogonal projection at any rung.** -/
def NotScaledProjection {Uconfig : Type*} (Δ : ℕ → Uconfig → HH Lat →L[ℝ] HH Lat) : Prop :=
  ∀ (k : ℕ) (U : Uconfig) (c : ℝ), (Δ k U).comp (Δ k U) ≠ c • (Δ k U)

section ScaledProjection

variable {Uconfig : Type*} [Nontrivial Uconfig]

/-- **§4's realization IS a scaled projection** — the exact sense in which it carries no content off
its kernel. `(a P)² = a (a P)`. -/
theorem chainDelta_is_scaled_projection (K : ℕ → Submodule ℝ (HH Lat)) (k : ℕ) (U : Uconfig) :
    (chainDelta (Lat := Lat) K k U).comp (chainDelta (Lat := Lat) K k U)
      = ucoef U • chainDelta (Lat := Lat) K k U := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hidem : (K k)ᗮ.starProjection ((K k)ᗮ.starProjection v)
      = (K k)ᗮ.starProjection v :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, chainDelta_apply,
    map_smul, hidem, smul_smul]

/-- **K5 rejects §4's realization.** So K5 is genuinely not implied by K1/K2/K3. -/
theorem chainDelta_fails_NotScaledProjection (K : ℕ → Submodule ℝ (HH Lat)) :
    ¬ NotScaledProjection (Lat := Lat) (Uconfig := Uconfig) (chainDelta K) := by
  intro h
  obtain ⟨U₀⟩ : Nonempty Uconfig := ⟨u₀ Uconfig⟩
  exact h 0 U₀ (ucoef U₀) (chainDelta_is_scaled_projection K 0 U₀)

/-- **K5 does NOT reject the junk witness.** `jDelta` acts as `1 + g` on `span e_A` and as `1` on
`e_B`, two distinct nonzero eigenvalues, so it is not a scaled projection. K1, not K5, is what fires
on the junk. -/
theorem jDelta_satisfies_NotScaledProjection :
    NotScaledProjection (Lat := Lat) (Uconfig := Uconfig) jDelta := by
  intro k U c hEq
  -- on `e_B` the operator is the identity, forcing `c = 1`
  have hB : jDelta (Lat := Lat) k U (eB (Lat := Lat)) = eB (Lat := Lat) := by
    rw [jDelta]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smul_apply, jproj_eB, smul_zero, add_zero]
  have heB := DFunLike.congr_fun hEq (eB (Lat := Lat))
  rw [ContinuousLinearMap.comp_apply, hB, hB, ContinuousLinearMap.smul_apply, hB] at heB
  have hc : c = 1 := by
    have hz : (1 - c) • eB (Lat := Lat) = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero.mpr heB
    rcases smul_eq_zero.mp hz with hs | hv
    · linarith [sub_eq_zero.mp hs]
    · exact absurd hv eB_ne_zero
  -- on `e_A` it is `(1 + g)`, so `c = 1` forces `g = 0`
  have hA : jDelta (Lat := Lat) k U (eA (Lat := Lat)) = (1 + jg k U) • eA (Lat := Lat) := by
    rw [jDelta]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smul_apply, jproj_eA]
    rw [add_smul, one_smul]
  have heA := DFunLike.congr_fun hEq (eA (Lat := Lat))
  rw [ContinuousLinearMap.comp_apply, hA, map_smul, hA, ContinuousLinearMap.smul_apply, hA,
    hc, one_smul, smul_smul] at heA
  have hz : ((1 + jg k U) * (1 + jg k U) - (1 + jg k U)) • eA (Lat := Lat) = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr heA
  rcases smul_eq_zero.mp hz with hs | hv
  · have hg := jg_pos (Uconfig := Uconfig) k U
    have : (1 + jg k U) * (1 + jg k U) = 1 + jg k U := sub_eq_zero.mp hs
    nlinarith
  · exact eA_ne_zero hv

end ScaledProjection

/-! ## §7 — axiom audit -/

#print axioms three_le_card_bond
#print axioms bond_nontrivial
#print axioms span_single_ne_bot
#print axioms span_single_ne_top
#print axioms mem_forcedBonds
#print axioms liveConclusion_of_kernelStrengthened
#print axioms jDelta_satisfies_five_conjuncts
#print axioms jDelta_injective
#print axioms jDelta_fails_HasKernel
#print axioms jDelta_fails_KernelGrows
#print axioms jDelta_satisfies_KernelMono
#print axioms kernelStrengthened_rejects_junk
#print axioms chainDelta_eq_zero_iff
#print axioms chainDelta_adjoint
#print axioms chainDelta_psd
#print axioms chainDelta_on_V
#print axioms kernelStrengthened_of_chain
#print axioms single_mem_anchoredVInter_orthogonal
#print axioms single_mem_orthogonal_of_mem_forcedBonds
#print axioms kernelStrengthened_of_two_forced_bonds
#print axioms kernelStrengthened_of_nonDegenerate
#print axioms no_kernel_growth_at_every_rung
#print axioms no_hasKernel_of_V_eq_top
#print axioms kernelStrengthened_false_of_V_eq_top
#print axioms chainDelta_is_scaled_projection
#print axioms chainDelta_fails_NotScaledProjection
#print axioms jDelta_satisfies_NotScaledProjection

end AdalyFormal.Balaban.CoercUMainKernel
