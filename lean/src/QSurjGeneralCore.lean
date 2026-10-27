/-
`QSurjGeneralCore.lean` -- VERBATIM SUBSET of `compute/balaban_statement/dep/QSurjGeneral.lean`
lines 54-251 (the `topSpanning_general` / `qCLM_surjective_general` block), with the three lane-local
imports of that file (`QSurjSharp`, `Door3Etwo`, `Door3EtwoWitness`) REMOVED and replaced by the
single import `QSurjCriterion`.

WHY THE TRIM EXISTS, disclosed: importing `QSurjGeneral` alongside `HrawFeed` fails with
`environment already contains Thm315Core.leftFactor from AdalyFormal.Balaban.Thm315` -- the
`balaban_statement` lane stages a pre-splice root-level `Thm315` that now also lives in the formal
tree.  The trimmed block does not reference `Door3` or `Thm315` at all; only the tail of the
original file (its `qt_surjective_general` / `swAt` / `sw_qt_surjective` rows, lines 252-283) does,
and that tail is not used here.

NO MATHEMATICAL TEXT IS ALTERED.  `diff` against the original is recorded in
`compute/terminal_binder/QSURJ_TRIM.diff`.
-/
import QSurjCriterion

set_option maxHeartbeats 4000000

noncomputable section

namespace QSurjCriterion

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLinkConfiguration periodicPathHolonomy)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_one RMap_mul_apply)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf inBlock CoarseLattice
  mem_CoarseLattice coarseLattice_mem_fits)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero)
open AdalyFormal.Balaban.Q1Real (transportPath GammaPath straightSegment coordSteps)
open AdalyFormal.Balaban.BridgeInverse (qCLM bondDelta bondDelta_same bondDelta_ne)
open AdalyFormal.Balaban.ReparamCDisjoint (pathSite_apply_ne pathSite_apply_self_val)
open AdalyFormal.Balaban.RegularUQChain (coordSteps_straight_eq)
open AdalyFormal.Balaban.WitnessInequality (pathSite_add)

variable {L : PeriodicLatticeExtent}

/-! ## §11 — THE STAIRCASE DEGENERATES ON A COORDINATE LINE. -/

/-- **`Γ_{y,x}` collapses to a single leg when `x` differs from `y` in coordinate `μ` only.**
Quoted from the tree's own definition (`Q1Real.GammaPath`, CMP95 (1.7), descending order `2,1,0`):

    GammaPath y x = straightSegment y x 2
                 ++ straightSegment (update y 2 (x 2)) x 1
                 ++ straightSegment (update (update y 2 (x 2)) 1 (x 1)) x 0

If `x ν = y ν` for every `ν ≠ μ`, the two legs in the other directions have `coordSteps = 0`, hence
are `List.replicate 0 = []`, and every intermediate base point that they would have moved is left
where it was.  Proved by cases on `μ` because the staircase's ORDER is part of the definition. -/
theorem gammaPath_of_line {y x : PeriodicLatticeSite L} {μ : Fin 3}
    (h : ∀ ν, ν ≠ μ → x ν = y ν) : GammaPath y x = straightSegment y x μ := by
  fin_cases μ
  · have e2 : x 2 = y 2 := h 2 (by decide)
    have e1 : x 1 = y 1 := h 1 (by decide)
    simp [GammaPath, straightSegment, coordSteps, e2, e1, Function.update_eq_self,
      Function.update_of_ne]
    rfl
  · have e2 : x 2 = y 2 := h 2 (by decide)
    have e0 : x 0 = y 0 := h 0 (by decide)
    simp [GammaPath, straightSegment, coordSteps, e2, e0, Function.update_eq_self,
      Function.update_of_ne]
    rfl
  · have e1 : x 1 = y 1 := h 1 (by decide)
    have e0 : x 0 = y 0 := h 0 (by decide)
    simp [GammaPath, straightSegment, coordSteps, e1, e0, Function.update_of_ne]
    rfl

/-- **THE CORNER-LINE PATH IDENTITY.**  Every transport of the corner line is the SAME LIST
`replicate (ell−1) (μ,true)` — independent of the step `s`.  No group theory, no estimate: the
`Γ`-leg and the straight leg concatenate into one `μ`-segment of fixed length. -/
theorem transportPath_corner_line {y : PeriodicLatticeSite L} {μ : Fin 3} {ell s : ℕ}
    (hs : s < ell) (hfit : ell ≤ L μ + 1) :
    transportPath y (pathSite y μ s) μ (ell - 1 - s) = List.replicate (ell - 1) (μ, true) := by
  have hline : ∀ ν, ν ≠ μ → (pathSite y μ s) ν = y ν :=
    fun ν hν => pathSite_apply_ne y μ ν s hν
  rw [transportPath, gammaPath_of_line hline, straightSegment, straightSegment,
    coordSteps_straight_eq, coordSteps_straight_eq,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    ← List.replicate_add]
  congr 1
  omega

/-! ## §12 — THE CORNER LINE INSIDE THE BLOCK. -/

theorem cornerSite_val {ell : ℕ} {y : PeriodicLatticeSite L} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) {s : ℕ} (hs : s < ell) :
    ((pathSite y μ s) μ).val = (y μ).val + s := by
  have hfitμ : (y μ).val + ell ≤ L μ + 1 := coarseLattice_mem_fits hdvd hy μ
  rw [pathSite_apply_self_val, Nat.mod_eq_of_lt (by omega)]

theorem cornerSite_mem_block {ell : ℕ} (_hell : 0 < ell) {y : PeriodicLatticeSite L}
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) {s : ℕ}
    (hs : s < ell) : pathSite y μ s ∈ blockOf y ell := by
  refine mem_blockOf.mpr (fun ν => ?_)
  by_cases hν : ν = μ
  · subst hν
    rw [cornerSite_val hdvd hy ν hs]
    omega
  · rw [pathSite_apply_ne y μ ν s hν]
    omega

theorem iTop_cornerSite {ell : ℕ} (_hell : 0 < ell) {y : PeriodicLatticeSite L}
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) {s : ℕ}
    (hs : s < ell) : iTop ell (pathSite y μ s) μ = ell - 1 - s := by
  have hval := cornerSite_val hdvd hy μ hs
  have h0 : (y μ).val % ell = 0 := mem_CoarseLattice.mp hy μ
  have hmod : ((y μ).val + s) % ell = s := by
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
    rw [hk, Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
  simp only [iTop, muOff, hval, hmod]

theorem topSite_cornerSite {ell : ℕ} (hell : 0 < ell) {y : PeriodicLatticeSite L}
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) {s : ℕ}
    (hs : s < ell) : topSite ell (pathSite y μ s) μ = pathSite y μ (ell - 1) := by
  rw [topSite, iTop_cornerSite hell hdvd hy μ hs, ← pathSite_add]
  congr 1
  omega

/-- **THE CONVERSE: only the corner line reaches the corner top bond.**  If `x` is in the block and
its top-layer site is the CORNER top site, then `x` lies on the corner line.  This is what makes the
single-bond probe below read the corner line and nothing else. -/
theorem eq_cornerSite_of_topSite {ell : ℕ} (hell : 0 < ell) {y x : PeriodicLatticeSite L}
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hy : y ∈ CoarseLattice L ell) (μ : Fin 3)
    (hx : x ∈ blockOf y ell) (htop : topSite ell x μ = pathSite y μ (ell - 1)) :
    ∃ s : ℕ, s < ell ∧ x = pathSite y μ s := by
  have hxb := mem_blockOf.mp hx
  have hne : ∀ ν, ν ≠ μ → x ν = y ν := by
    intro ν hν
    have h1 : (topSite ell x μ) ν = x ν := topSite_apply_ne x μ ν hν
    have h2 : (pathSite y μ (ell - 1)) ν = y ν := pathSite_apply_ne y μ ν _ hν
    rw [htop, h2] at h1
    exact h1.symm
  have hbμ := hxb μ
  refine ⟨(x μ).val - (y μ).val, by omega, ?_⟩
  have hfitμ : (y μ).val + ell ≤ L μ + 1 := coarseLattice_mem_fits hdvd hy μ
  funext ν
  by_cases hν : ν = μ
  · subst hν
    apply Fin.ext
    have hlo := (hxb ν).1
    have hhi := (hxb ν).2
    rw [pathSite_apply_self_val, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [pathSite_apply_ne y μ ν _ hν]
    exact hne ν hν

/-! ## §13 — THE CRITERION, AT EVERY BACKGROUND. -/

/-- **`TopSpanning U ell` HOLDS FOR EVERY `U`.**

The witness is a SINGLE fine bond: the corner top bond `(pathSite y μ (ell−1), μ)` of the block,
carrying `(card)⁻¹ • R(g)⁻¹ v`.  `eq_cornerSite_of_topSite` says only the corner line reads it,
`transportPath_corner_line` says all `ell` of those reads carry the SAME transport `g`, and `R(g)`
is invertible, so the block map hits `v` exactly.  Nothing about `U` is used beyond `RMap` being a
group action. -/
theorem topSpanning_general (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    TopSpanning U ell := by
  intro b v
  classical
  obtain ⟨⟨y, hy⟩, μ⟩ := b
  have hfit : ell ≤ L μ + 1 := Nat.le_of_dvd (by omega) (hdvd μ)
  set top : PeriodicLatticeSite L := pathSite y μ (ell - 1) with htopdef
  set g : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    periodicPathHolonomy U y (List.replicate (ell - 1) (μ, true)) with hgdef
  set S : Finset (PeriodicLatticeSite L) :=
    (blockOf y ell).filter (fun x => topSite ell x μ = top) with hSdef
  -- `y` itself is on the corner line, so `S` is nonempty
  have hyS : y ∈ S := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_blockOf.mpr (fun ν => ⟨Nat.le_refl _, by omega⟩)
    · have := topSite_cornerSite hell hdvd hy μ (s := 0) hell
      rwa [pathSite_zero] at this
  have hScard : (S.card : ℝ) ≠ 0 := by
    have : 0 < S.card := Finset.card_pos.mpr ⟨y, hyS⟩
    positivity
  -- every member of `S` carries the SAME transport
  have hgcommon : ∀ x ∈ blockOf y ell, topSite ell x μ = top →
      periodicPathHolonomy U y (transportPath y x μ (iTop ell x μ)) = g := by
    intro x hx htop
    obtain ⟨s, hs, rfl⟩ := eq_cornerSite_of_topSite hell hdvd hy μ hx htop
    rw [iTop_cornerSite hell hdvd hy μ hs, transportPath_corner_line hs hfit, hgdef]
  -- the single-bond witness
  set c : SuTwo := ((S.card : ℝ))⁻¹ • RMap g⁻¹ v with hcdef
  refine ⟨bondDelta (top, μ) c, ?_⟩
  rw [blockTopMap_apply]
  have hterm : ∀ x ∈ blockOf y ell,
      RMap (periodicPathHolonomy U y (transportPath y x μ (iTop ell x μ)))
          (bondDelta (top, μ) c (topSite ell x μ, μ))
        = if topSite ell x μ = top then RMap g c else 0 := by
    intro x hx
    by_cases hxt : topSite ell x μ = top
    · rw [if_pos hxt, hgcommon x hx hxt]
      have hb : ((topSite ell x μ, μ) : Bond L) = (top, μ) := by rw [hxt]
      rw [hb, bondDelta_same]
    · rw [if_neg hxt]
      have hbne : ((topSite ell x μ, μ) : Bond L) ≠ (top, μ) := by
        intro hc
        exact hxt (congrArg Prod.fst hc)
      rw [bondDelta_ne c hbne, map_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← hSdef, Finset.sum_const, ← cast_nsmul,
    hcdef, map_smul, RMap_mul_apply, mul_inv_cancel, RMap_one, LinearMap.id_apply, smul_smul,
    mul_inv_cancel₀ hScard, one_smul]

/-- **THE RESIDUAL, CLOSED: `Q_ell(U)` IS SURJECTIVE AT EVERY BACKGROUND.**  No smallness, no
pure-gauge hypothesis, no volume condition — only the two structural guards `0 < ell` and
`∀ μ, ell ∣ L μ + 1`, both of which are THEOREMS at a `Door3Setup`. -/
theorem qCLM_surjective_general
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    Function.Surjective (qCLM U ell) :=
  qCLM_surjective_of_topSpanning U hell hdvd (topSpanning_general U hell hdvd)


end QSurjCriterion
