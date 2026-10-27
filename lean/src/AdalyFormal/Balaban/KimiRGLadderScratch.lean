/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.RGLadderCoarse

set_option autoImplicit false
set_option maxRecDepth 8192

/-!
# `KimiRGLadderScratch` — K3 prosecution scratch (write-scope exception file)

Blind-prosecution artifact for the RG-ladder no-go (`RGLadderCore`/`RGLadderCoarse`).
NEW declarations only; imports only; no edits to any existing file. Contents:

* `kimi_mem_anchoredVInter_iff` — membership in `anchoredVInter` transports exactly.
* `kimi_kerVec_not_mem_anchoredVInter_two` — the exhibit's own kernel witness `kerVec` is
  gauge-fixed OUT of `anchoredVInter 2` (its bond `(origin, 0)` lies on the staircase
  `Γ_{origin, unitSite}`). So the conditional no-go's `hmem` premise cannot be supplied by the
  consumer at `ell = 2` via the exhibit's witness.
* `kimi_w_*` — a DIFFERENT kernel vector of `rgDelta 2` (last-layer bonds) that IS in
  `anchoredVInter 2`, and `kimi_no_coercivityHypothesis_rgLadder_at_ell_two`: the `ell = 2`
  no-go the exhibit does NOT prove (its unconditional theorem covers only `ell = 1`).
-/

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice inBlock mem_blockOf
  mem_CoarseLattice admissibleSubspaceInter mem_admissibleSubspaceInter staircasePath
  axisSegment mem_axisSegment corner1 corner2)
open AdalyFormal.Balaban.RGLadderCoarse
open scoped InnerProductSpace

namespace AdalyFormal.Balaban.KimiRGLadderScratch

/-- A concrete witness lattice: 4 sites per direction, 192 bonds. -/
def Lat4 : PeriodicLatticeExtent := fun _ => 3

/-- Membership in `anchoredVInter` transports exactly across the `WithLp` linear equivalence. -/
theorem kimi_mem_anchoredVInter_iff {Lat : PeriodicLatticeExtent} {ell : ℕ}
    {v : Anchoring.AnchoredBondSpace Lat} :
    v ∈ Anchoring.anchoredVInter (Lat := Lat) ell ↔
      WithLp.ofLp v ∈ admissibleSubspaceInter Lat ell := by
  unfold Anchoring.anchoredVInter
  constructor
  · intro hv
    obtain ⟨w, hw, hweq⟩ := hv
    subst hweq
    simpa using hw
  · intro h
    exact ⟨WithLp.ofLp v, h, by simp⟩

/-! ## §1 — the exhibit's `kerVec` is NOT in `anchoredVInter 2` -/

theorem kimi_lat4_dir : (1 : ℕ) ≤ Lat4 0 := by decide

theorem kimi_origin_mem_coarseLattice_two :
    originSite (Lat := Lat4) ∈ CoarseLattice Lat4 2 := by
  rw [mem_CoarseLattice]
  intro μ
  rfl

theorem kimi_unitSite_mem_blockOf_two :
    unitSite (Lat := Lat4) 0 kimi_lat4_dir ∈ blockOf (originSite (Lat := Lat4)) 2 := by
  decide

/-- The bond `(origin, 0)` lies on the staircase `Γ_{origin, unitSite}` at direction 0:
it is the sole member of the third (`corner2`) axis segment. -/
theorem kimi_kerBondA_mem_staircase :
    (originSite (Lat := Lat4), (0 : Fin 3))
      ∈ staircasePath (originSite (Lat := Lat4)) (unitSite (Lat := Lat4) 0 kimi_lat4_dir) := by
  rw [staircasePath, Finset.mem_union, Finset.mem_union]
  refine Or.inr ?_
  rw [mem_axisSegment]
  refine ⟨rfl, ?_, by decide, by decide⟩
  intro ν hν
  fin_cases ν <;> simp_all [corner2, corner1, Function.update, unitSite, originSite]

/-- **Finding: the exhibit's kernel witness is gauge-fixed out of `V` at `ell = 2`.**
`kerVec` has value `1` on `(origin, 0)`, which lies on a staircase, so `kerVec ∉ anchoredVInter 2`. -/
theorem kimi_kerVec_not_mem_anchoredVInter_two :
    kerVec (Lat := Lat4) 0 kimi_lat4_dir ∉ Anchoring.anchoredVInter (Lat := Lat4) 2 := by
  rw [kimi_mem_anchoredVInter_iff, mem_admissibleSubspaceInter]
  intro h
  have h0 := h _ kimi_origin_mem_coarseLattice_two _ kimi_unitSite_mem_blockOf_two _
    kimi_kerBondA_mem_staircase
  rw [kerVec] at h0
  simp only [WithLp.ofLp_sub, PiLp.ofLp_single, Pi.sub_apply, Pi.single_apply, kerBondA,
    kerBondB] at h0
  have hne : (originSite (Lat := Lat4), (0 : Fin 3))
      ≠ (unitSite (Lat := Lat4) 0 kimi_lat4_dir, (0 : Fin 3)) := by
    intro hEq
    exact originSite_ne_unitSite 0 kimi_lat4_dir (congrArg Prod.fst hEq)
  simp only [hne, if_false, if_true] at h0
  norm_num at h0

/-! ## §2 — a last-layer kernel vector that IS in `anchoredVInter 2` -/

/-- Site with coordinate 0 equal to 1 (this is `unitSite 0`), direction-0 bond version of the
exhibit is reused; we need a SECOND last-layer bond differing in coordinate 1. -/
def kimiSiteB : PeriodicLatticeSite Lat4 :=
  Function.update (unitSite (Lat := Lat4) 0 kimi_lat4_dir) 1 ⟨1, by decide⟩

/-- The two last-layer bonds: direction 0, base coordinate 0 equal to 1 (the layer
`y₀ + ell − 1 = 1` of the origin block at `ell = 2`). -/
def kimiBondA : Bond Lat4 := (unitSite (Lat := Lat4) 0 kimi_lat4_dir, 0)

def kimiBondB : Bond Lat4 := (kimiSiteB, 0)

/-- **The last-layer kernel witness.** -/
noncomputable def kimiW : Anchoring.AnchoredBondSpace Lat4 :=
  EuclideanSpace.single kimiBondA (1 : ℝ) - EuclideanSpace.single kimiBondB (1 : ℝ)

theorem kimi_bondA_ne_bondB : kimiBondA ≠ kimiBondB := by
  intro hEq
  have h1 := congrFun (congrArg Prod.fst hEq) 1
  simp [kimiBondA, kimiBondB, kimiSiteB, unitSite, originSite, Function.update] at h1

theorem kimi_w_ne_zero : kimiW ≠ 0 := by
  intro hz
  have := congrFun (congrArg WithLp.ofLp hz) kimiBondA
  simp [kimiW, kimi_bondA_ne_bondB] at this

/-- Both last-layer bonds share their block representative at side 2. -/
theorem kimi_bond_same_rep :
    blockRepBond (Lat := Lat4) 2 kimiBondA = blockRepBond (Lat := Lat4) 2 kimiBondB := by
  unfold blockRepBond kimiBondA kimiBondB
  congr 1
  funext μ
  refine Fin.ext ?_
  rw [blockRepSite_val, blockRepSite_val]
  fin_cases μ <;> rfl

/-- The fibre-sum operator kills the last-layer difference. -/
theorem kimi_sumCLMof_w : sumCLMof (blockRepBond (Lat := Lat4) 2) kimiW = 0 := by
  refine euclid_eq_zero ?_
  intro c
  rw [kimiW, map_sub]
  simp only [WithLp.ofLp_sub, Pi.sub_apply]
  rw [sumCLMof_single, sumCLMof_single, kimi_bond_same_rep]
  simp

/-- `rgDelta 2` kills the last-layer difference. -/
theorem kimi_rgDelta_two_w : rgDelta (Lat := Lat4) 2 kimiW = 0 := by
  rw [rgDelta_eq_deltaOf, deltaOf]
  simp [kimi_sumCLMof_w]

/-- **The staircase exclusion, coordinate-0 form.** A direction-0 bond whose base coordinate 0
has value 1 lies on NO staircase of any valid `(y, x)` pair at `ell = 2`: the third segment
needs `min y₀ x₀ ≤ 1 < max y₀ x₀`, forcing `y₀ = 1`, but `y₀ % 2 = 0`. -/
theorem kimi_dir0_layer1_not_mem_staircase {y x : PeriodicLatticeSite Lat4}
    (hy : y ∈ CoarseLattice Lat4 2) (hx : x ∈ blockOf y 2) {site : PeriodicLatticeSite Lat4}
    (hsite0 : (site 0).val = 1) :
    (site, (0 : Fin 3)) ∉ staircasePath y x := by
  intro hb
  rw [mem_CoarseLattice] at hy
  rw [mem_blockOf] at hx
  rw [staircasePath, Finset.mem_union, Finset.mem_union] at hb
  rcases hb with (h2 | h1) | h0
  · rw [mem_axisSegment] at h2
    exact absurd h2.1 (show ¬ ((0 : Fin 3) = 2) by decide)
  · rw [mem_axisSegment] at h1
    exact absurd h1.1 (show ¬ ((0 : Fin 3) = 1) by decide)
  · rw [mem_axisSegment] at h0
    obtain ⟨-, -, hlo, hhi⟩ := h0
    have h0y := hy 0
    have hx0 := hx 0
    rw [hsite0] at hlo hhi
    omega

theorem kimi_bondA_not_mem_staircase {y x : PeriodicLatticeSite Lat4}
    (hy : y ∈ CoarseLattice Lat4 2) (hx : x ∈ blockOf y 2) :
    kimiBondA ∉ staircasePath y x :=
  kimi_dir0_layer1_not_mem_staircase hy hx (unitSite_apply_self 0 kimi_lat4_dir)

theorem kimi_bondB_not_mem_staircase {y x : PeriodicLatticeSite Lat4}
    (hy : y ∈ CoarseLattice Lat4 2) (hx : x ∈ blockOf y 2) :
    kimiBondB ∉ staircasePath y x := by
  refine kimi_dir0_layer1_not_mem_staircase hy hx ?_
  simp [kimiSiteB, Function.update, unitSite_apply_self]

/-- **The last-layer witness lies in `anchoredVInter 2`.** -/
theorem kimi_w_mem_anchoredVInter_two :
    kimiW ∈ Anchoring.anchoredVInter (Lat := Lat4) 2 := by
  rw [kimi_mem_anchoredVInter_iff, mem_admissibleSubspaceInter]
  intro y hy x hx b hb
  have hbA := kimi_bondA_not_mem_staircase hy hx (x := x) (y := y)
  have hbB := kimi_bondB_not_mem_staircase hy hx (x := x) (y := y)
  have h1 : b ≠ kimiBondA := fun h => hbA (h ▸ hb)
  have h2 : b ≠ kimiBondB := fun h => hbB (h ▸ hb)
  simp [kimiW, h1, h2]

/-- **THE `ell = 2` NO-GO THE EXHIBIT DOES NOT PROVE.** No `CoercivityHypothesis` on the
anchored carrier with `V = anchoredVInter 2` can have `Δ k₀ U₀ = rgDelta 2`. The exhibit's
unconditional theorem covers only `ell = 1` (where `V = ⊤`); its conditional theorem's witness
is excluded from `V` at `ell = 2` (§1). The obstruction at `ell = 2` is nonetheless REAL —
via the last-layer witness, not the exhibit's origin-anchored one. -/
theorem kimi_no_coercivityHypothesis_rgLadder_at_ell_two
    (cohyp : Balaban.CoercivityHypothesis (Anchoring.AnchoredBondSpace Lat4) Bool)
    (hV : cohyp.V = Anchoring.anchoredVInter (Lat := Lat4) 2)
    (k₀ : ℕ) (U₀ : Bool) (hΔ : cohyp.Δ k₀ U₀ = rgDelta (Lat := Lat4) 2) : False := by
  refine RGLadderCore.no_uniform_ladder_of_one_small_rung cohyp k₀ U₀ ?_ kimi_w_ne_zero ?_
  · rw [hV]
    exact kimi_w_mem_anchoredVInter_two
  · rw [hΔ]
    exact kimi_rgDelta_two_w

#print axioms kimi_kerVec_not_mem_anchoredVInter_two
#print axioms kimi_w_mem_anchoredVInter_two
#print axioms kimi_rgDelta_two_w
#print axioms kimi_no_coercivityHypothesis_rgLadder_at_ell_two



/-! ## §3 — the `coerc_u_main` existential at `ell = 1` is INHABITED (the no-go does not reach it)

The no-go `no_coercivityHypothesis_rgLadder_at_ell_one` rules out ONE pinned operator family
(`rgDelta n`) at `V = anchoredVInter 1 = ⊤`. It does NOT bind the existential itself: here is an
operator family on the same carrier, at the same `ell = 1`, with the same `V`, satisfying every
`coerc_u_main` conjunct — self-adjoint, globally PSD, non-scalar, genuinely `k`- and `U`-dependent,
coercive with `γ'' = 1` on `V = ⊤` — whose every rung is INJECTIVE (no coarsening anywhere), so no
premise of the no-go (`hΔ` pinning, kernel vector in `V`, small factor) can ever be supplied. -/

/-- Distinguished bonds at the origin, directions 0 and 1. -/
def kimiB0 : Bond Lat4 := (originSite (Lat := Lat4), 0)

def kimiB1 : Bond Lat4 := (originSite (Lat := Lat4), 1)

/-- Rank-one bump on coordinate `kimiB0`. -/
noncomputable def kimiProj :
    Anchoring.AnchoredBondSpace Lat4 →L[ℝ] Anchoring.AnchoredBondSpace Lat4 :=
  ContinuousLinearMap.smulRight (EuclideanSpace.proj kimiB0) (EuclideanSpace.single kimiB0 1)

/-- The coefficient: `k`-dependent (via `(k+1)⁻¹`) and `U`-dependent (via the `Bool`). -/
noncomputable def kimiT (k : ℕ) (U : Bool) : ℝ := (k + 1 : ℝ)⁻¹ + (if U then 1 else 0)

/-- **The injective ladder**: `id + t • P₀`, positive definite everywhere, so no kernel and no
small factorization — the no-go's premises are unsatisfiable for this family. -/
noncomputable def kimiDelta (k : ℕ) (U : Bool) :
    Anchoring.AnchoredBondSpace Lat4 →L[ℝ] Anchoring.AnchoredBondSpace Lat4 :=
  ContinuousLinearMap.id ℝ _ + kimiT k U • kimiProj

theorem kimiT_pos (k : ℕ) (U : Bool) : 0 < kimiT k U := by
  unfold kimiT
  positivity

theorem kimiT_nonneg (k : ℕ) (U : Bool) : 0 ≤ kimiT k U := (kimiT_pos k U).le

theorem kimiProj_apply (v : Anchoring.AnchoredBondSpace Lat4) :
    kimiProj v = (WithLp.ofLp v kimiB0) • EuclideanSpace.single kimiB0 (1 : ℝ) := by
  rw [kimiProj, ContinuousLinearMap.smulRight_apply, EuclideanSpace.coe_proj]

theorem kimi_inner_proj (v : Anchoring.AnchoredBondSpace Lat4) :
    (inner ℝ v (kimiProj v) : ℝ) = (WithLp.ofLp v kimiB0) ^ 2 := by
  rw [kimiProj_apply, inner_smul_right, EuclideanSpace.inner_single_right]
  simp
  ring

/-- The quadratic form of the ladder, explicitly. -/
theorem kimi_inner_delta (k : ℕ) (U : Bool) (v : Anchoring.AnchoredBondSpace Lat4) :
    (inner ℝ v (kimiDelta k U v) : ℝ)
      = ‖v‖ ^ 2 + kimiT k U * (WithLp.ofLp v kimiB0) ^ 2 := by
  rw [kimiDelta]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  rw [inner_add_right, inner_smul_right, kimi_inner_proj, real_inner_self_eq_norm_sq]

/-- **Coercivity with `γ'' = 1` on `V = ⊤`** (and hence on any `V`). -/
theorem kimi_coercive (k : ℕ) (U : Bool) (v : Anchoring.AnchoredBondSpace Lat4) :
    (1:ℝ) * ‖v‖ ^ 2 ≤ (inner ℝ v (kimiDelta k U v) : ℝ) := by
  rw [kimi_inner_delta]
  have hsq : 0 ≤ (WithLp.ofLp v kimiB0) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg (kimiT_nonneg k U) hsq]

/-- **Global PSD.** -/
theorem kimi_psd (k : ℕ) (U : Bool) (v : Anchoring.AnchoredBondSpace Lat4) :
    0 ≤ (inner ℝ v (kimiDelta k U v) : ℝ) :=
  le_trans (by positivity) (kimi_coercive k U v)

/-- **Self-adjointness** via the symmetry of the quadratic form. -/
theorem kimiDelta_adjoint (k : ℕ) (U : Bool) :
    (kimiDelta k U).adjoint = kimiDelta k U := by
  have h : kimiDelta k U = (kimiDelta k U).adjoint := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [kimiDelta]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    rw [inner_add_left, inner_smul_left, inner_add_right, inner_smul_right]
    rw [kimiProj_apply, kimiProj_apply, inner_smul_left, inner_smul_right,
      EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
    simp only [RCLike.conj_to_real, one_mul]
    ring
  exact h.symm

/-- **Non-scalarity**: `id + t•P₀ = c•id` forces `c = 1` (off-bump) and `t = 0` (on-bump). -/
theorem kimiDelta_not_scalar (k : ℕ) (U : Bool) (c : ℝ) :
    kimiDelta k U ≠ c • ContinuousLinearMap.id ℝ (Anchoring.AnchoredBondSpace Lat4) := by
  intro hEq
  have hb : kimiB0 ≠ kimiB1 := by decide
  have key : ∀ v : Anchoring.AnchoredBondSpace Lat4,
      ‖v‖ ^ 2 + kimiT k U * (WithLp.ofLp v kimiB0) ^ 2 = c * ‖v‖ ^ 2 := by
    intro v
    have h1 := congrArg (fun T => (inner ℝ v (T v) : ℝ)) hEq
    rw [kimi_inner_delta] at h1
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, inner_smul_right,
      real_inner_self_eq_norm_sq] at h1
    exact h1
  have h1 := key (EuclideanSpace.single kimiB1 1)
  have h0 := key (EuclideanSpace.single kimiB0 1)
  rw [PiLp.norm_single, norm_one, PiLp.ofLp_single, Pi.single_eq_of_ne hb] at h1
  rw [PiLp.norm_single, norm_one, PiLp.ofLp_single, Pi.single_eq_same] at h0
  have hc : c = 1 := by nlinarith
  have ht : kimiT k U = 0 := by nlinarith
  linarith [kimiT_pos k U]

/-- **Genuine `k`-dependence** (the coefficient `(k+1)⁻¹` separates any two rungs). -/
theorem kimiDelta_k_dependent :
    ∃ (U : Bool) (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧ kimiDelta k₁ U ≠ kimiDelta k₂ U := by
  refine ⟨true, 1, 2, by decide, ?_⟩
  intro hEq
  have h1 := congrArg (fun T => (inner ℝ (EuclideanSpace.single kimiB0 1)
    (T (EuclideanSpace.single kimiB0 1)) : ℝ)) hEq
  rw [kimi_inner_delta, kimi_inner_delta] at h1
  rw [PiLp.norm_single, norm_one, PiLp.ofLp_single, Pi.single_eq_same] at h1
  norm_num [kimiT] at h1

/-- **Genuine `U`-dependence** (the structure's `Δ_nonconstant` field). -/
theorem kimiDelta_nonconstant :
    ∃ (k : ℕ) (U₁ U₂ : Bool), U₁ ≠ U₂ ∧ kimiDelta k U₁ ≠ kimiDelta k U₂ := by
  refine ⟨0, true, false, by decide, ?_⟩
  intro hEq
  have h1 := congrArg (fun T => (inner ℝ (EuclideanSpace.single kimiB0 1)
    (T (EuclideanSpace.single kimiB0 1)) : ℝ)) hEq
  rw [kimi_inner_delta, kimi_inner_delta] at h1
  rw [PiLp.norm_single, norm_one, PiLp.ofLp_single, Pi.single_eq_same] at h1
  norm_num [kimiT] at h1

/-- **THE CONSUMER'S EXISTENTIAL AT `ell = 1`, INHABITED.** This is the exact conclusion type of
`Spine.coerc_u_main` (quoted at `Spine.lean:780`) instantiated at `Lat := Lat4`, `ell := 1`,
`Uconfig := Bool` — proved HERE with no `sorry`, after the no-go. The no-go therefore does NOT
refute `coerc_u_main`, even at the one `ell` where its unconditional theorem applies.

**[SUPERSEDED THE SAME NIGHT, 2026-07-28 — and by the very finding this gate helped produce.]**
`Spine.coerc_u_main` now carries `(hell : 2 ≤ ell)`, threaded through `gap1_main` to `main`, so
`ell = 1` is **no longer in its domain at all**. The sentence above is stale in a specific way
worth naming: it argued that the no-go fails to refute `coerc_u_main` at `ell = 1`, and `ell = 1`
has since ceased to be a value `coerc_u_main` ranges over. The argument is not wrong — it is about
a point that has left the statement.

The theorem below is UNAFFECTED and still worth keeping. It never applies `Spine.coerc_u_main`;
it restates that conclusion type standalone at `Lat4`/`Bool`/`ell = 1` and inhabits it. So it
remains a genuine record of what the OLD statement admitted — a content-free operator, `id + t·P₀`
— which is part of why the `2 ≤ ell` threading happened. Read it as evidence about the statement
we replaced, not as a live claim about the statement we now have. -/
theorem kimi_coerc_u_main_inhabited_at_ell_one :
    ∃ cohyp : Balaban.CoercivityHypothesis (Balaban.Anchoring.AnchoredBondSpace Lat4) Bool,
      cohyp.V = Balaban.Anchoring.anchoredVInter (Lat := Lat4) 1 ∧
      (∀ (k : ℕ) (U : Bool), (cohyp.Δ k U).adjoint = cohyp.Δ k U) ∧
      (∀ (k : ℕ) (U : Bool) (v : Balaban.Anchoring.AnchoredBondSpace Lat4),
        0 ≤ (inner ℝ v (cohyp.Δ k U v) : ℝ)) ∧
      (∀ (k : ℕ) (U : Bool) (c : ℝ), cohyp.Δ k U
        ≠ c • ContinuousLinearMap.id ℝ (Balaban.Anchoring.AnchoredBondSpace Lat4)) ∧
      (∃ (U : Bool) (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧ cohyp.Δ k₁ U ≠ cohyp.Δ k₂ U) := by
  refine ⟨{ Δ := kimiDelta, V := ⊤, V_ne_bot := ?_, Δ_nonconstant := kimiDelta_nonconstant,
              γ'' := 1, γ''_pos := one_pos, coercive := ?_ }, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Submodule.ne_bot_iff]
    exact ⟨EuclideanSpace.single kimiB0 1, Submodule.mem_top, by simp⟩
  · intro k U v _
    exact kimi_coercive k U v
  · rw [anchoredVInter_one_eq_top]
  · intro k U
    exact kimiDelta_adjoint k U
  · intro k U v
    exact kimi_psd k U v
  · intro k U c
    exact kimiDelta_not_scalar k U c
  · exact kimiDelta_k_dependent

#print axioms kimi_coerc_u_main_inhabited_at_ell_one



/-! ## §4 — a FIXED proper `V` DOES carry a genuinely coarsening tower (docstring claim refuted)

The exhibit's framing claims "the ENCODING `Δ : ℕ → Uconfig → H →L[ℝ] H` with a single
`V : Submodule ℝ H` cannot carry a tower whose steps genuinely coarsen". As stated that is false:
coercivity on `V` constrains `Δ` only ON `V`, so any `V` disjoint from every rung's kernel carries a
coarsening tower with a uniform constant. Here is one, on the tree's own carrier, satisfying every
`coerc_u_main` conjunct except the `V`-pinning — and whose rung 0 has an explicit nonzero kernel
vector (`kimiW`, §2). The true statement is: cannot carry a tower that coarsens WITHIN `V`. -/

/-- The constant field. -/
noncomputable def kimiConstVec : Anchoring.AnchoredBondSpace Lat4 :=
  (WithLp.linearEquiv 2 ℝ (Bond Lat4 → ℝ)).symm (fun _ => 1)

theorem kimi_ofLp_constVec : WithLp.ofLp kimiConstVec = fun _ => (1 : ℝ) := by
  show (WithLp.linearEquiv 2 ℝ (Bond Lat4 → ℝ))
    ((WithLp.linearEquiv 2 ℝ (Bond Lat4 → ℝ)).symm (fun _ => 1)) = fun _ => 1
  exact LinearEquiv.apply_symm_apply _ _

theorem kimi_card_bonds : Fintype.card (Bond Lat4) = 192 := by decide

/-- `‖const‖² = #bonds = 192`. -/
theorem kimi_norm_constVec_sq : ‖kimiConstVec‖ ^ 2 = 192 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  have h1 : ∀ i : Bond Lat4,
      (inner ℝ (WithLp.ofLp kimiConstVec i) (WithLp.ofLp kimiConstVec i) : ℝ) = 1 := by
    intro i
    rw [kimi_ofLp_constVec]
    simp
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_univ, kimi_card_bonds]
  norm_num

/-- **The fibre-count bound**: for ANY bond map `r`, the Gram operator of `r` is coercive on the
constant field with constant `1`. Each fibre sum is the fibre's cardinality `f_c`, and
`Σ_c f_c² ≥ Σ_c f_c = #bonds`. -/
theorem kimi_norm_sumCLMof_constVec_sq (r : Bond Lat4 → Bond Lat4) :
    ‖kimiConstVec‖ ^ 2 ≤ ‖sumCLMof (Lat := Lat4) r kimiConstVec‖ ^ 2 := by
  rw [kimi_norm_constVec_sq, ← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  have hstep : ∀ i : Bond Lat4, ((Finset.univ.filter (fun b => r b = i)).card : ℝ)
      ≤ (inner ℝ (WithLp.ofLp (sumCLMof (Lat := Lat4) r kimiConstVec) i)
          (WithLp.ofLp (sumCLMof (Lat := Lat4) r kimiConstVec) i) : ℝ) := by
    intro i
    rw [real_inner_self_eq_norm_sq, sumCLMof_apply]
    simp only [kimi_ofLp_constVec, Finset.sum_const, nsmul_eq_mul, mul_one, Real.norm_eq_abs]
    rw [abs_of_nonneg (Nat.cast_nonneg _), sq]
    exact_mod_cast Nat.le_mul_self _
  have hsum : ∑ i : Bond Lat4, ((Finset.univ.filter (fun b => r b = i)).card : ℝ) = 192 := by
    have h1 : ∑ i : Bond Lat4, (Finset.univ.filter (fun b => r b = i)).card = 192 := by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
      have h2 : ∀ b : Bond Lat4, ∑ i : Bond Lat4, (if r b = i then (1 : ℕ) else 0) = 1 := by
        intro b
        rw [Finset.sum_ite_eq Finset.univ (r b) (fun _ => 1)]
        simp
      rw [Finset.sum_congr rfl (fun b _ => h2 b), Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_univ, kimi_card_bonds]
    exact_mod_cast h1
  calc (192 : ℝ) = ∑ i : Bond Lat4, ((Finset.univ.filter (fun b => r b = i)).card : ℝ) := hsum.symm
    _ ≤ ∑ i : Bond Lat4, (inner ℝ (WithLp.ofLp (sumCLMof (Lat := Lat4) r kimiConstVec) i)
        (WithLp.ofLp (sumCLMof (Lat := Lat4) r kimiConstVec) i) : ℝ) :=
      Finset.sum_le_sum (fun i _ => hstep i)

/-- **The coarsening tower on a fixed `V`.** `kimiDelta2 k U = s(U) • rgDelta (2^(k+1))`: every
rung is a genuine coarsening (block side `≥ 2`, so `kimiW` is in its kernel — §2), `k`- and
`U`-dependent, self-adjoint, PSD, non-scalar. -/
noncomputable def kimiDelta2 (k : ℕ) (U : Bool) :
    Anchoring.AnchoredBondSpace Lat4 →L[ℝ] Anchoring.AnchoredBondSpace Lat4 :=
  (if U then (2 : ℝ) else 1) • rgDelta (Lat := Lat4) (2 ^ (k + 1))

/-- The scale factor is nonzero. -/
theorem kimi_scale_ne_zero (U : Bool) : (if U then (2 : ℝ) else 1) ≠ 0 := by
  split <;> norm_num

theorem kimi_scale_ge_one (U : Bool) : (1 : ℝ) ≤ (if U then (2 : ℝ) else 1) := by
  split <;> norm_num

/-- **Coercivity on `V = span{const}` with `γ'' = 1`, uniform in `k` and `U`.** -/
theorem kimi_coercive2 (k : ℕ) (U : Bool) (v : Anchoring.AnchoredBondSpace Lat4)
    (hv : v ∈ Submodule.span ℝ {kimiConstVec}) :
    (1 : ℝ) * ‖v‖ ^ 2 ≤ (inner ℝ v (kimiDelta2 k U v) : ℝ) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have hS := kimi_norm_sumCLMof_constVec_sq (blockRepBond (Lat := Lat4) (2 ^ (k + 1)))
  rw [kimiDelta2, ContinuousLinearMap.smul_apply, map_smul, inner_smul_right, inner_smul_right,
    inner_smul_left, RCLike.conj_to_real, rgDelta_eq_deltaOf, inner_deltaOf, norm_smul]
  have ha2 : ‖a‖ ^ 2 = a ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg a, kimi_scale_ge_one U, ha2, hS, kimi_norm_constVec_sq,
    mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hS),
    mul_nonneg (sub_nonneg.mpr (kimi_scale_ge_one U))
      (mul_nonneg (sq_nonneg a)
        (sq_nonneg ‖sumCLMof (blockRepBond (Lat := Lat4) (2 ^ (k + 1))) kimiConstVec‖))]

/-- **The tower genuinely coarsens**: an explicit nonzero kernel vector at rung 0. -/
theorem kimiDelta2_kernel_witness :
    ∃ v : Anchoring.AnchoredBondSpace Lat4, v ≠ 0 ∧ kimiDelta2 0 true v = 0 := by
  refine ⟨kimiW, kimi_w_ne_zero, ?_⟩
  rw [kimiDelta2]
  simp [kimi_rgDelta_two_w]

/-- **Self-adjoint at every rung.** -/
theorem kimiDelta2_adjoint (k : ℕ) (U : Bool) :
    (kimiDelta2 k U).adjoint = kimiDelta2 k U := by
  have h : kimiDelta2 k U = (kimiDelta2 k U).adjoint := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [kimiDelta2]
    simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real]
    rw [← rgDelta_adjoint, ContinuousLinearMap.adjoint_inner_left, rgDelta_adjoint]
  exact h.symm

/-- **Globally PSD.** -/
theorem kimiDelta2_psd (k : ℕ) (U : Bool) (v : Anchoring.AnchoredBondSpace Lat4) :
    0 ≤ (inner ℝ v (kimiDelta2 k U v) : ℝ) := by
  rw [kimiDelta2, ContinuousLinearMap.smul_apply, inner_smul_right]
  have h := rgDelta_psd (Lat := Lat4) (2 ^ (k + 1)) v
  have hs : (0 : ℝ) ≤ (if U then (2 : ℝ) else 1) := by split <;> norm_num
  exact mul_nonneg hs h

/-- **Non-scalar at every rung** (every rung has block side `≥ 2`, so `rgDelta_not_scalar`
applies). -/
theorem kimiDelta2_not_scalar (k : ℕ) (U : Bool) (c : ℝ) :
    kimiDelta2 k U ≠ c • ContinuousLinearMap.id ℝ (Anchoring.AnchoredBondSpace Lat4) := by
  intro hEq
  have hs := kimi_scale_ne_zero U
  have hn : 2 ≤ 2 ^ (k + 1) := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.le_add_left 1 k)
    rwa [pow_one] at h
  have hrg : rgDelta (Lat := Lat4) (2 ^ (k + 1))
      = (c / (if U then (2 : ℝ) else 1)) • ContinuousLinearMap.id ℝ _ := by
    have h1 := congrArg (fun T => ((if U then (2 : ℝ) else 1))⁻¹ • T) hEq
    rw [kimiDelta2] at h1
    simp only [smul_smul] at h1
    rw [inv_mul_cancel₀ hs, one_smul] at h1
    rw [div_eq_inv_mul]
    exact h1
  exact rgDelta_not_scalar hn 0 kimi_lat4_dir _ hrg

/-- **Genuine `U`-dependence** (the structure's `Δ_nonconstant` field). -/
theorem kimiDelta2_nonconstant :
    ∃ (k : ℕ) (U₁ U₂ : Bool), U₁ ≠ U₂ ∧ kimiDelta2 k U₁ ≠ kimiDelta2 k U₂ := by
  refine ⟨0, true, false, by decide, ?_⟩
  intro hEq
  have h2 : (2 : ℝ) • rgDelta (Lat := Lat4) 2 = (1 : ℝ) • rgDelta (Lat := Lat4) 2 := hEq
  have h4 : (2 : ℝ) • rgDelta (Lat := Lat4) 2 - (1 : ℝ) • rgDelta (Lat := Lat4) 2 = 0 := by
    rw [h2, one_smul, sub_self]
  have h5 : (2 : ℝ) • rgDelta (Lat := Lat4) 2 - (1 : ℝ) • rgDelta (Lat := Lat4) 2
      = rgDelta (Lat := Lat4) 2 := by
    ext v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
    rw [← sub_smul, show ((2 : ℝ) - 1) = 1 by norm_num, one_smul]
  rw [h5] at h4
  exact rgDelta_ne_zero 2 h4

/-- `sumCLMof` of a single is a single at the image bond. -/
theorem kimi_sumCLMof_single_eq_single (r : Bond Lat4 → Bond Lat4) (b : Bond Lat4) :
    sumCLMof (Lat := Lat4) r (EuclideanSpace.single b (1 : ℝ))
      = EuclideanSpace.single (r b) (1 : ℝ) := by
  apply WithLp.ofLp_injective 2
  funext c
  rw [sumCLMof_single, PiLp.ofLp_single]
  by_cases h : r b = c
  · subst h
    simp
  · rw [if_neg h]
    simp [Ne.symm h]

/-- Inner product of singles through the Gram operator. -/
theorem kimi_inner_single_rgDelta (n : ℕ) (b c : Bond Lat4) :
    (inner ℝ (EuclideanSpace.single c (1 : ℝ))
      (rgDelta (Lat := Lat4) n (EuclideanSpace.single b (1 : ℝ))) : ℝ)
      = (inner ℝ (EuclideanSpace.single (blockRepBond (Lat := Lat4) n c) (1 : ℝ))
          (EuclideanSpace.single (blockRepBond (Lat := Lat4) n b) (1 : ℝ)) : ℝ) := by
  rw [rgDelta_eq_deltaOf, deltaOf]
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right, kimi_sumCLMof_single_eq_single,
    kimi_sumCLMof_single_eq_single]

/-- A bond whose base has coordinate 0 equal to 2. -/
def kimiBondC : Bond Lat4 :=
  (fun μ => ⟨if μ = 0 then 2 else 0, by fin_cases μ <;> decide⟩, (0 : Fin 3))

theorem kimi_rep_two_bondC : blockRepBond (Lat := Lat4) 2 kimiBondC = kimiBondC := by
  unfold blockRepBond kimiBondC
  congr 1
  funext μ
  refine Fin.ext ?_
  rw [blockRepSite_val]
  fin_cases μ <;> rfl

theorem kimi_rep_four_bondC : blockRepBond (Lat := Lat4) 4 kimiBondC = kimiB0 := by
  unfold blockRepBond kimiBondC kimiB0
  congr 1
  funext μ
  refine Fin.ext ?_
  rw [blockRepSite_val]
  fin_cases μ <;> rfl

theorem kimi_rep_two_B0 : blockRepBond (Lat := Lat4) 2 kimiB0 = kimiB0 := by
  unfold blockRepBond kimiB0
  congr 1
  funext μ
  refine Fin.ext ?_
  rw [blockRepSite_val]
  fin_cases μ <;> rfl

theorem kimi_rep_four_B0 : blockRepBond (Lat := Lat4) 4 kimiB0 = kimiB0 := by
  unfold blockRepBond kimiB0
  congr 1
  funext μ
  refine Fin.ext ?_
  rw [blockRepSite_val]
  fin_cases μ <;> rfl

theorem kimiB0_ne_bondC : kimiB0 ≠ kimiBondC := by
  intro h
  have := congrFun (congrArg Prod.fst h) 0
  simp [kimiB0, kimiBondC, originSite] at this

/-- **Genuine `k`-dependence**: rungs 0 and 1 differ on the `(kimiB0, kimiBondC)` matrix element
(side 2 keeps them in distinct fibres; side 4 merges them). -/
theorem kimiDelta2_k_dependent :
    ∃ (U : Bool) (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧ kimiDelta2 k₁ U ≠ kimiDelta2 k₂ U := by
  refine ⟨false, 0, 1, by decide, ?_⟩
  intro hEq
  have h1 := congrArg (fun T => (inner ℝ (EuclideanSpace.single kimiB0 (1 : ℝ))
    (T (EuclideanSpace.single kimiBondC (1 : ℝ))) : ℝ)) hEq
  have hL : (inner ℝ (EuclideanSpace.single kimiB0 (1 : ℝ))
      (kimiDelta2 0 false (EuclideanSpace.single kimiBondC (1 : ℝ))) : ℝ) = 0 := by
    rw [kimiDelta2]
    simp only [Bool.false_eq_true, ite_false, ContinuousLinearMap.smul_apply, inner_smul_right,
      one_mul]
    rw [show (2 : ℕ) ^ (0 + 1) = 2 from rfl, kimi_inner_single_rgDelta, kimi_rep_two_B0,
      kimi_rep_two_bondC, EuclideanSpace.inner_single_left, map_one, one_mul, PiLp.ofLp_single,
      Pi.single_apply, if_neg kimiB0_ne_bondC]
  have hR : (inner ℝ (EuclideanSpace.single kimiB0 (1 : ℝ))
      (kimiDelta2 1 false (EuclideanSpace.single kimiBondC (1 : ℝ))) : ℝ) = 1 := by
    rw [kimiDelta2]
    simp only [Bool.false_eq_true, ite_false, ContinuousLinearMap.smul_apply, inner_smul_right,
      one_mul]
    rw [show (2 : ℕ) ^ (1 + 1) = 4 from rfl, kimi_inner_single_rgDelta, kimi_rep_four_B0,
      kimi_rep_four_bondC, EuclideanSpace.inner_single_left, map_one, one_mul, PiLp.ofLp_single,
      Pi.single_apply, if_pos rfl]
  rw [hL] at h1
  rw [hR] at h1
  norm_num at h1

/-- **THE FIXED-`V` COARSENING TOWER, ASSEMBLED.** A `CoercivityHypothesis` on the tree's own
carrier, with a FIXED proper subspace `V = span{const}`, satisfying every `coerc_u_main` conjunct
except the `V`-pinning — and genuinely coarsening at rung 0. The no-go's theorems, being
conditional on a kernel vector inside `V` (or an equivalent factorization), do not and cannot
refute this inhabitant: its `V` avoids every rung's kernel by construction. -/
theorem kimi_fixedV_coarsening_tower :
    ∃ cohyp : Balaban.CoercivityHypothesis (Balaban.Anchoring.AnchoredBondSpace Lat4) Bool,
      (∀ (k : ℕ) (U : Bool), (cohyp.Δ k U).adjoint = cohyp.Δ k U) ∧
      (∀ (k : ℕ) (U : Bool) (v : Balaban.Anchoring.AnchoredBondSpace Lat4),
        0 ≤ (inner ℝ v (cohyp.Δ k U v) : ℝ)) ∧
      (∀ (k : ℕ) (U : Bool) (c : ℝ), cohyp.Δ k U
        ≠ c • ContinuousLinearMap.id ℝ (Balaban.Anchoring.AnchoredBondSpace Lat4)) ∧
      (∃ (U : Bool) (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧ cohyp.Δ k₁ U ≠ cohyp.Δ k₂ U) ∧
      (∃ (v : Balaban.Anchoring.AnchoredBondSpace Lat4), v ≠ 0 ∧ cohyp.Δ 0 true v = 0) := by
  refine ⟨{ Δ := kimiDelta2, V := Submodule.span ℝ {kimiConstVec}, V_ne_bot := ?_,
              Δ_nonconstant := kimiDelta2_nonconstant, γ'' := 1, γ''_pos := one_pos,
              coercive := ?_ }, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Submodule.ne_bot_iff]
    refine ⟨kimiConstVec, Submodule.subset_span rfl, ?_⟩
    intro hz
    have := congrFun (congrArg WithLp.ofLp hz) kimiB0
    simp [kimi_ofLp_constVec] at this
  · intro k U v hv
    exact kimi_coercive2 k U v hv
  · intro k U
    exact kimiDelta2_adjoint k U
  · intro k U v
    exact kimiDelta2_psd k U v
  · intro k U c
    exact kimiDelta2_not_scalar k U c
  · exact kimiDelta2_k_dependent
  · exact kimiDelta2_kernel_witness

#print axioms kimi_fixedV_coarsening_tower

end AdalyFormal.Balaban.KimiRGLadderScratch
