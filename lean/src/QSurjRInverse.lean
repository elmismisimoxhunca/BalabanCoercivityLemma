/-
# `QSurjRInverse.lean` — AN **EXPLICIT** RIGHT INVERSE OF THE COVARIANT BLOCK AVERAGE `Q_ell(U)`
# WITH A **TRANSPORT-UNIFORM** OPERATOR NORM.

LANE `compute/qsurj_rinverse/`.  Write scope: that directory only.  Never `lake build`.

## THE DENOTATION FACT THIS MODULE IS BUILT AROUND (checked against the definitions, not prose)

`AdalyFormal.HrawCarriers.composedQ h Ufine = coarseFnL2Equiv h ∘L qCLM Ufine ell`, and
`qCLM Ufine ell` is `LineIntegralCovariant.lineCoarseRestrictCov Ufine`, whose defining body
carries the background INSIDE the sum:

    lineCoarseRestrictCov U ell A b = (1/ell⁴) • Σ_{x ∈ blockOf b.1.1 ell} rZeroA U b.1.1 x A b.2 ell
    rZeroA U y x A μ ell = Σ_{i<ell} RMap (periodicPathHolonomy U y (transportPath y x μ i))
                                          (A (pathSite x μ i, μ))

So `composedQ` is **NOT background-free**, and no background-free section can be an exact right
inverse of it at general `Ufine`.  In particular `H1Bound.liftCLM` (`‖·‖ = ell²`, proved) satisfies
`qCLM (trivialU L) ell ∘L liftCLM = id` at the FLAT background only; the tree's general-`U` route
(`H1Bound.Perturbed`/`GeneralU`) buys `ell²/(1−δ)` under a transport-defect hypothesis `δ < 1`,
which is CONDITIONAL on the background.

## WHAT IS BUILT HERE, AND WHY ITS NORM IS NEVERTHELESS `U`-FREE

The section built here **does** depend on `U` — it must — but the background enters it only through
`RMap g⁻¹` for a single group element `g`, and `RMap` is an ISOMETRY of the `𝔰𝔲(2)` fibre
(`AlphaAnalyticity.norm_RMap`, REUSED).  Hence the operator norm is a function of `ell` alone.

The construction is the CORNER-LINE section that `QSurjGeneral.topSpanning_general` uses
existentially, promoted here to an OPERATOR so that a norm can be taken (LAW-19: the corner-line
path identity `transportPath_corner_line` and the block combinatorics `isTop_pathSite_iff`,
`coarseOf_topSite`, `eq_cornerSite_of_topSite` are REUSED verbatim, not rebuilt):

    (R_U F)(z,ν) = ell³ · R(g_{y,ν})⁻¹ · F(y,ν)   if `(z,ν)` is the CORNER-TOP bond of its block
                 = 0                              otherwise,
    g_{y,ν} := periodicPathHolonomy U y (replicate (ell−1) (ν,true)),  y = coarseOf ell z.

    **`qCLM U ell ∘L R_U = id`   for EVERY `U`   (`qCLM_comp_rInv`)**
    **`‖R_U‖ = ell³`  EXACTLY, for EVERY `U`   (`opNorm_rInv`)**

`ell³` and not `ell²`: the flat lift spreads a coarse value over the `ell²` top-layer bonds of the
block (weight `ell` each, `‖·‖² = ell²·ell² = ell⁴`); the corner-line section must concentrate it on
the ONE bond whose `ell` readings share a single holonomy (weight `ell³`, `‖·‖² = ell⁶`).  That
factor `ell` is the counted price of dropping the transport-defect hypothesis.  Consistency floor:
`‖Q‖ ≤ ell^{-3/2}` (`QCLMNorm`), so any right inverse has `‖R‖ ≥ ell^{3/2}`; `ell³` is admissible.

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.
-/
import QSurjGeneralCore
import AdalyFormal.Balaban.AlphaAnalyticity
import AdalyFormal.Balaban.QCLMNorm

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.longLine false

noncomputable section

namespace QSurjRInverse

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLinkConfiguration periodicPathHolonomy)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one RMap_mul_apply
  suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf inBlock CoarseLattice
  mem_CoarseLattice coarseLattice_mem_fits)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero)
open AdalyFormal.Balaban.Q1Real (rZeroA transportPath)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.BridgeInverse (qCLM qCLM_apply CoarseFnL2)
open AdalyFormal.Balaban.ReparamCDisjoint (pathSite_apply_ne pathSite_apply_self_val)
open AdalyFormal.Balaban.AlphaAnalyticity (norm_RMap)
open AdalyFormal.Balaban.QCLMNorm (norm_sq_pilp)
open QSurjCriterion (muOff IsTop iTop topSite coarseOf coarseOf_val coarseOf_mem
  coarseOf_eq_of_mem_blockOf isTop_pathSite_iff iTop_lt isTop_topSite coarseOf_topSite
  coarseBond cast_nsmul cornerSite_val cornerSite_mem_block iTop_cornerSite topSite_cornerSite
  transportPath_corner_line)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE CORNER-TOP BOND OF A BLOCK

`QSurjCriterion` already names the TOP LAYER (`IsTop`, `μ`-offset `ell−1`).  The corner-line
section is supported on the strictly smaller set of bonds whose transverse offsets all vanish as
well — one bond per coarse bond.  That predicate is what makes the support a GRAPH over the coarse
bonds, and hence the norm computable. -/

/-- **`(z,μ)` is the CORNER-TOP bond of its block**: `μ`-offset `ell−1` (the top layer, so it is
read only by its own coarse bond — `QSurjCriterion.coarseOf_topSite`) and every TRANSVERSE offset
`0` (so it sits on the corner line, where `Γ_{y,x}` degenerates — `gammaPath_of_line`). -/
def IsCornerTop (ell : ℕ) (z : PeriodicLatticeSite L) (μ : Fin 3) : Prop :=
  (z μ).val % ell = ell - 1 ∧ ∀ ν : Fin 3, ν ≠ μ → (z ν).val % ell = 0

instance instDecidableIsCornerTop (ell : ℕ) (z : PeriodicLatticeSite L) (μ : Fin 3) :
    Decidable (IsCornerTop ell z μ) := by
  unfold IsCornerTop; infer_instance

theorem isCornerTop_isTop {ell : ℕ} {z : PeriodicLatticeSite L} {μ : Fin 3}
    (h : IsCornerTop ell z μ) : IsTop ell z μ := h.1

/-- The corner-top SITE of the block based at a coarse site `y`, in direction `μ`. -/
def cornerTopSite (ell : ℕ) (y : PeriodicLatticeSite L) (μ : Fin 3) : PeriodicLatticeSite L :=
  pathSite y μ (ell - 1)

/-- The corner-top BOND of a coarse bond — the support of the section, one fine bond per coarse
bond. -/
def cornerBondOf {ell : ℕ} (b : CoarseBond L ell) : Bond L :=
  (cornerTopSite ell b.1.1 b.2, b.2)

/-- **The single group element the whole corner line carries.**  `QSurjGeneral`'s
`transportPath_corner_line` proves every one of the `ell` transports of the corner line is the list
`replicate (ell−1) (μ,true)`; this names its holonomy. -/
def cornerHol (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (y : PeriodicLatticeSite L) (μ : Fin 3) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  periodicPathHolonomy U y (List.replicate (ell - 1) (μ, true))

theorem cornerTopSite_apply_ne (ell : ℕ) (y : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) :
    (cornerTopSite ell y μ) ν = y ν := pathSite_apply_ne y μ ν _ h

theorem cornerTopSite_val {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) :
    ((cornerTopSite ell y μ) μ).val = (y μ).val + (ell - 1) :=
  cornerSite_val hdvd hy μ (by omega)

/-- `y` is in its own block — the trivial membership used repeatedly below. -/
theorem self_mem_blockOf {ell : ℕ} (hell : 0 < ell) (y : PeriodicLatticeSite L) :
    y ∈ blockOf y ell := mem_blockOf.mpr (fun _ => ⟨Nat.le_refl _, by omega⟩)

/-- `iTop` at a COARSE site is `ell−1`: the corner-top site is `y`'s own top site. -/
theorem iTop_coarse {ell : ℕ} {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    (μ : Fin 3) : iTop ell y μ = ell - 1 := by
  simp only [iTop, muOff, mem_CoarseLattice.mp hy μ, Nat.sub_zero]

theorem topSite_coarse {ell : ℕ} {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    (μ : Fin 3) : topSite ell y μ = cornerTopSite ell y μ := by
  rw [topSite, iTop_coarse hy μ, cornerTopSite]

/-- **The corner-top bond of a coarse bond really is corner-top.** -/
theorem isCornerTop_cornerTopSite {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) :
    IsCornerTop ell (cornerTopSite ell y μ) μ := by
  refine ⟨?_, ?_⟩
  · rw [cornerTopSite_val hell hdvd hy μ]
    have h0 : (y μ).val % ell = 0 := mem_CoarseLattice.mp hy μ
    have h1 : (ell - 1) % ell = ell - 1 := Nat.mod_eq_of_lt (by omega)
    rw [Nat.add_mod, h0, Nat.zero_add, h1, h1]
  · intro ν hν
    rw [cornerTopSite_apply_ne ell y μ ν hν]
    exact mem_CoarseLattice.mp hy ν

/-- **The coarse site of a corner-top site is the block's own centre.** -/
theorem coarseOf_cornerTopSite {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) :
    coarseOf ell (cornerTopSite ell y μ) = y := by
  rw [← topSite_coarse hy μ]
  exact coarseOf_topSite hell hdvd hy (self_mem_blockOf hell y) μ

/-- **THE CONVERSE — every corner-top bond IS the corner-top bond of its own coarse bond.**
This is what makes `cornerBondOf` a BIJECTION onto the support, and hence the norm exactly
computable rather than merely bounded. -/
theorem cornerTopSite_coarseOf {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {z : PeriodicLatticeSite L} {μ : Fin 3}
    (hz : IsCornerTop ell z μ) : cornerTopSite ell (coarseOf ell z) μ = z := by
  have hcm : coarseOf ell z ∈ CoarseLattice L ell := coarseOf_mem hell z
  funext ρ
  apply Fin.ext
  by_cases hρ : ρ = μ
  · subst hρ
    rw [cornerTopSite_val hell hdvd hcm ρ, coarseOf_val]
    have hmod : (z ρ).val % ell = ell - 1 := hz.1
    have hle : (z ρ).val % ell ≤ (z ρ).val := Nat.mod_le _ _
    omega
  · rw [cornerTopSite_apply_ne ell (coarseOf ell z) μ ρ hρ, coarseOf_val, hz.2 ρ hρ]
    omega

/-- The coarse bond a corner-top bond belongs to, as an EQUATION on `CoarseBond` — the form the
section's proofs consume. -/
theorem coarseBond_cornerBondOf {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (b : CoarseBond L ell) :
    coarseBond hell (cornerBondOf b).1 (cornerBondOf b).2 = b := by
  obtain ⟨⟨y, hy⟩, μ⟩ := b
  refine Prod.ext (Subtype.ext ?_) rfl
  exact coarseOf_cornerTopSite hell hdvd hy μ

/-! ## §2 — THE SECTION, AS AN OPERATOR -/

/-- **THE CORNER-LINE SECTION.**  `ell³ · R(g)⁻¹` at the corner-top bond of each block, `0`
elsewhere.  The `ell³` is `ell⁴` (the block average's normalisation `η^{d+1}`) divided by the `ell`
readings of the corner line — both counted, neither fitted. -/
def secFun (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (hell : 0 < ell) (F : CoarseBond L ell → SuTwo) : Bond L → SuTwo :=
  fun bd => if IsCornerTop ell bd.1 bd.2 then
      ((ell : ℝ) ^ 3) • RMap (cornerHol U ell (coarseOf ell bd.1) bd.2)⁻¹
        (F (coarseBond hell bd.1 bd.2))
    else 0

theorem secFun_corner {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    {ell : ℕ} (hell : 0 < ell) (F : CoarseBond L ell → SuTwo) {bd : Bond L}
    (h : IsCornerTop ell bd.1 bd.2) :
    secFun U hell F bd = ((ell : ℝ) ^ 3) • RMap (cornerHol U ell (coarseOf ell bd.1) bd.2)⁻¹
      (F (coarseBond hell bd.1 bd.2)) := by
  rw [secFun, if_pos h]

theorem secFun_zero {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    {ell : ℕ} (hell : 0 < ell) (F : CoarseBond L ell → SuTwo) {bd : Bond L}
    (h : ¬ IsCornerTop ell bd.1 bd.2) : secFun U hell F bd = 0 := by
  rw [secFun, if_neg h]

theorem secFun_add (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (F G : CoarseBond L ell → SuTwo) (bd : Bond L) :
    secFun U hell (F + G) bd = secFun U hell F bd + secFun U hell G bd := by
  by_cases h : IsCornerTop ell bd.1 bd.2
  · rw [secFun_corner hell _ h, secFun_corner hell _ h, secFun_corner hell _ h]
    show ((ell : ℝ) ^ 3) • RMap _ (F _ + G _) = _
    rw [map_add, smul_add]
  · rw [secFun_zero hell _ h, secFun_zero hell _ h, secFun_zero hell _ h, add_zero]

theorem secFun_smul (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (c : ℝ) (F : CoarseBond L ell → SuTwo) (bd : Bond L) :
    secFun U hell (c • F) bd = c • secFun U hell F bd := by
  by_cases h : IsCornerTop ell bd.1 bd.2
  · rw [secFun_corner hell _ h, secFun_corner hell _ h]
    show ((ell : ℝ) ^ 3) • RMap _ (c • F _) = _
    rw [map_smul, smul_comm]
  · rw [secFun_zero hell _ h, secFun_zero hell _ h, smul_zero]

/-- The section on the `L²` carriers, as a `LinearMap`. -/
def secLM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (hell : 0 < ell) : CoarseFnL2 L ell →ₗ[ℝ] BondFnL2 L where
  toFun F := WithLp.toLp 2 (secFun U hell (WithLp.ofLp F))
  map_add' F G := by
    refine (WithLp.linearEquiv 2 ℝ (Bond L → SuTwo)).injective ?_
    funext bd
    simpa using secFun_add U hell (WithLp.ofLp F) (WithLp.ofLp G) bd
  map_smul' c F := by
    refine (WithLp.linearEquiv 2 ℝ (Bond L → SuTwo)).injective ?_
    funext bd
    simpa using secFun_smul U hell c (WithLp.ofLp F) bd

/-- **`R_U` — the right inverse this module delivers.** -/
def rInv (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (hell : 0 < ell) : CoarseFnL2 L ell →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap (secLM U hell)

theorem rInv_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (F : CoarseFnL2 L ell) (bd : Bond L) :
    WithLp.ofLp (rInv U hell F) bd = secFun U hell (WithLp.ofLp F) bd := rfl

/-! ## §3 — THE CORNER LINE AS A `Finset`, AND ITS CARDINALITY -/

/-- The `ell` sites of the block's corner line in direction `μ`. -/
def cornerLine (ell : ℕ) (y : PeriodicLatticeSite L) (μ : Fin 3) :
    Finset (PeriodicLatticeSite L) := (Finset.range ell).image (fun s => pathSite y μ s)

theorem cornerLine_subset {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) :
    cornerLine ell y μ ⊆ blockOf y ell := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
  exact cornerSite_mem_block hell hdvd hy μ (Finset.mem_range.mp hs)

theorem cornerLine_card {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) :
    (cornerLine ell y μ).card = ell := by
  rw [cornerLine, Finset.card_image_of_injOn, Finset.card_range]
  intro s hs t ht hst
  have hs' : s < ell := Finset.mem_range.mp hs
  have ht' : t < ell := Finset.mem_range.mp ht
  have hst' : pathSite y μ s = pathSite y μ t := hst
  have h1 : ((pathSite y μ s) μ).val = (y μ).val + s := cornerSite_val hdvd hy μ hs'
  have h2 : ((pathSite y μ t) μ).val = (y μ).val + t := cornerSite_val hdvd hy μ ht'
  rw [hst', h2] at h1
  omega

/-- **THE CORNER LINE IS EXACTLY THE TRANSVERSE-ALIGNED PART OF THE BLOCK.**  This is the
characterisation the sum-splitting uses: off the corner line, the section's support is not seen at
all. -/
theorem mem_cornerLine_iff {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (μ : Fin 3)
    {x : PeriodicLatticeSite L} (hx : x ∈ blockOf y ell) :
    x ∈ cornerLine ell y μ ↔ ∀ ν : Fin 3, ν ≠ μ → (x ν).val % ell = 0 := by
  constructor
  · intro hxc ν hν
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hxc
    rw [pathSite_apply_ne y μ ν _ hν]
    exact mem_CoarseLattice.mp hy ν
  · intro halign
    have hco : coarseOf ell x = y := coarseOf_eq_of_mem_blockOf hy hx
    have hxb := mem_blockOf.mp hx
    have hxbmu := hxb μ
    have hfit : (y μ).val + ell ≤ L μ + 1 := coarseLattice_mem_fits hdvd hy μ
    refine Finset.mem_image.mpr ⟨(x μ).val - (y μ).val, Finset.mem_range.mpr (by omega), ?_⟩
    funext ν
    apply Fin.ext
    by_cases hν : ν = μ
    · subst hν
      rw [pathSite_apply_self_val, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [pathSite_apply_ne y μ ν _ hν]
      have hcv : ((coarseOf ell x) ν).val = (y ν).val := by rw [hco]
      rw [coarseOf_val, halign ν hν] at hcv
      omega

/-! ## §4 — THE BLOCK SUM, TERM BY TERM -/

/-- **OFF THE CORNER LINE THE SECTION IS INVISIBLE.**  Every site `pathSite x μ i` inherits `x`'s
transverse offsets, so if one of them is nonzero no term of `rZeroA` is corner-top. -/
theorem rZeroA_secFun_off {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    {ell : ℕ} (hell : 0 < ell) (F : CoarseBond L ell → SuTwo) {y x : PeriodicLatticeSite L}
    {μ : Fin 3} (hoff : ¬ ∀ ν : Fin 3, ν ≠ μ → (x ν).val % ell = 0) :
    rZeroA U y x (secFun U hell F) μ ell = 0 := by
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hnc : ¬ IsCornerTop ell ((pathSite x μ i, μ) : Bond L).1 ((pathSite x μ i, μ) : Bond L).2 := by
    intro hc
    refine hoff (fun ν hν => ?_)
    have h2 : ((pathSite x μ i) ν).val % ell = 0 := hc.2 ν hν
    rwa [pathSite_apply_ne x μ ν i hν] at h2
  rw [secFun_zero hell F hnc, map_zero]

/-- **ON THE CORNER LINE THE WHOLE `i`-SUM COLLAPSES TO `ell³ · F(b)`.**  Three REUSED facts do the
work: `isTop_pathSite_iff` kills every `i ≠ iTop`; `topSite_cornerSite` identifies the surviving
site as the block's corner-top site; `transportPath_corner_line` says its transport is the SAME
group element `g` for every `s`, which the section has already inverted. -/
theorem rZeroA_secFun_corner (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (F : CoarseBond L ell → SuTwo) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    (μ : Fin 3) {s : ℕ} (hs : s < ell) :
    rZeroA U y (pathSite y μ s) (secFun U hell F) μ ell
      = ((ell : ℝ) ^ 3) • F (⟨y, hy⟩, μ) := by
  have hfit : ell ≤ L μ + 1 := Nat.le_of_dvd (by omega) (hdvd μ)
  set x : PeriodicLatticeSite L := pathSite y μ s with hxdef
  have hiT : iTop ell x μ = ell - 1 - s := iTop_cornerSite hell hdvd hy μ hs
  have hiTlt : iTop ell x μ < ell := iTop_lt hell x μ
  have hcollapse : rZeroA U y x (secFun U hell F) μ ell
      = RMap (periodicPathHolonomy U y (transportPath y x μ (iTop ell x μ)))
          (secFun U hell F (topSite ell x μ, μ)) := by
    refine Finset.sum_eq_single (iTop ell x μ) ?_ ?_
    · intro i hi hne
      have hlt : i < ell := Finset.mem_range.mp hi
      have hnc : ¬ IsCornerTop ell ((pathSite x μ i, μ) : Bond L).1
          ((pathSite x μ i, μ) : Bond L).2 := by
        intro hc
        exact hne ((isTop_pathSite_iff hell hdvd x μ hlt).mp (isCornerTop_isTop hc))
      rw [secFun_zero hell F hnc, map_zero]
    · intro hnm
      exact absurd (Finset.mem_range.mpr hiTlt) hnm
  rw [hcollapse]
  -- identify the surviving site and its transport
  have htop : topSite ell x μ = cornerTopSite ell y μ := by
    rw [topSite_cornerSite hell hdvd hy μ hs, cornerTopSite]
  have hpath : transportPath y x μ (iTop ell x μ) = List.replicate (ell - 1) (μ, true) := by
    rw [hiT, hxdef]
    exact transportPath_corner_line hs hfit
  rw [hpath, htop]
  -- evaluate the section at the corner-top bond
  have hct : IsCornerTop ell ((cornerTopSite ell y μ, μ) : Bond L).1
      ((cornerTopSite ell y μ, μ) : Bond L).2 := isCornerTop_cornerTopSite hell hdvd hy μ
  rw [secFun_corner hell F hct]
  have hco : coarseOf ell ((cornerTopSite ell y μ, μ) : Bond L).1 = y :=
    coarseOf_cornerTopSite hell hdvd hy μ
  have hcb : coarseBond hell ((cornerTopSite ell y μ, μ) : Bond L).1
      ((cornerTopSite ell y μ, μ) : Bond L).2 = ((⟨y, hy⟩, μ) : CoarseBond L ell) :=
    Prod.ext (Subtype.ext hco) rfl
  rw [hcb]
  show RMap (cornerHol U ell y μ)
      (((ell : ℝ) ^ 3) • RMap (cornerHol U ell (coarseOf ell (cornerTopSite ell y μ)) μ)⁻¹
        (F (⟨y, hy⟩, μ))) = _
  rw [hco, map_smul, RMap_mul_apply, mul_inv_cancel, RMap_one, LinearMap.id_apply]

/-! ## §5 — THE SECTION EQUATION, AT **EVERY** BACKGROUND -/

/-- **`Q_ell(U) ∘ R_U = id`, UNCONDITIONALLY IN `U`.**  The only hypotheses are the two structural
guards `0 < ell` and `∀ μ, ell ∣ L μ + 1`, exactly those of
`QSurjGeneral.qCLM_surjective_general`. -/
theorem qCLM_rInv_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (F : CoarseFnL2 L ell) :
    qCLM U ell (rInv U hell F) = F := by
  refine (WithLp.linearEquiv 2 ℝ (CoarseBond L ell → SuTwo)).injective ?_
  funext b
  show lineCoarseRestrictCov U ell (secFun U hell (WithLp.ofLp F)) b = WithLp.ofLp F b
  obtain ⟨⟨y, hy⟩, μ⟩ := b
  set G : CoarseBond L ell → SuTwo := WithLp.ofLp F with hG
  have hzero : ∀ x ∈ blockOf y ell, x ∉ cornerLine ell y μ →
      rZeroA U y x (secFun U hell G) μ ell = 0 := by
    intro x hx hnc
    refine rZeroA_secFun_off hell G (fun halign => hnc ?_)
    exact (mem_cornerLine_iff hell hdvd hy μ hx).mpr halign
  have hconst : ∀ x ∈ cornerLine ell y μ,
      rZeroA U y x (secFun U hell G) μ ell = ((ell : ℝ) ^ 3) • G (⟨y, hy⟩, μ) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact rZeroA_secFun_corner U hell hdvd G hy μ (Finset.mem_range.mp hs)
  show (1 / (ell : ℝ) ^ 4) • ∑ x ∈ blockOf y ell, rZeroA U y x (secFun U hell G) μ ell
      = G (⟨y, hy⟩, μ)
  rw [← Finset.sum_subset (cornerLine_subset hell hdvd hy μ) hzero,
    Finset.sum_congr rfl hconst, Finset.sum_const, cornerLine_card hell hdvd hy μ,
    ← cast_nsmul, smul_smul, smul_smul]
  have hne : ((ell : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    exact ne_of_gt this
  rw [show (1 / (ell : ℝ) ^ 4) * (ell : ℝ) * (ell : ℝ) ^ 3 = 1 by field_simp, one_smul]

theorem qCLM_comp_rInv (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    (qCLM U ell).comp (rInv U hell) = ContinuousLinearMap.id ℝ (CoarseFnL2 L ell) :=
  ContinuousLinearMap.ext (fun F => qCLM_rInv_apply U hell hdvd F)

/-! ## §6 — THE NORM: `ell³` EXACTLY, AND THE SAME NUMBER AT EVERY BACKGROUND

This is the transport-uniformity.  It is NOT that the section is background-free — it is not — but
that the background enters through `RMap g⁻¹` alone, and `RMap` is a fibre ISOMETRY. -/

/-- The pointwise norm of the section: the background has already cancelled. -/
theorem norm_secFun_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (F : CoarseBond L ell → SuTwo) (bd : Bond L) :
    ‖secFun U hell F bd‖
      = if IsCornerTop ell bd.1 bd.2 then ((ell : ℝ) ^ 3) * ‖F (coarseBond hell bd.1 bd.2)‖
        else 0 := by
  by_cases h : IsCornerTop ell bd.1 bd.2
  · rw [secFun_corner hell F h, if_pos h, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (ell : ℝ) ^ 3), norm_RMap]
  · rw [secFun_zero hell F h, if_neg h, norm_zero]

/-- `cornerBondOf` is injective — one corner-top bond per coarse bond, no collisions. -/
theorem cornerBondOf_injective {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    Function.Injective (cornerBondOf : CoarseBond L ell → Bond L) := by
  intro b c hbc
  have := coarseBond_cornerBondOf hell hdvd b
  rw [hbc, coarseBond_cornerBondOf hell hdvd c] at this
  exact this.symm

/-- **`‖R_U F‖ = ell³·‖F‖` — a SCALED ISOMETRY, at every background.** -/
theorem norm_rInv_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (F : CoarseFnL2 L ell) :
    ‖rInv U hell F‖ = ((ell : ℝ) ^ 3) * ‖F‖ := by
  have hsupp : ∀ bd ∈ (Finset.univ : Finset (Bond L)),
      bd ∉ (Finset.univ : Finset (CoarseBond L ell)).image cornerBondOf →
      ‖WithLp.ofLp (rInv U hell F) bd‖ ^ 2 = 0 := by
    intro bd _ hnot
    have hnc : ¬ IsCornerTop ell bd.1 bd.2 := by
      intro hc
      refine hnot (Finset.mem_image.mpr ⟨coarseBond hell bd.1 bd.2, Finset.mem_univ _, ?_⟩)
      refine Prod.ext ?_ rfl
      exact cornerTopSite_coarseOf hell hdvd hc
    rw [rInv_apply, secFun_zero hell _ hnc, norm_zero]
    ring
  have hinj : ∀ x ∈ (Finset.univ : Finset (CoarseBond L ell)),
      ∀ y ∈ (Finset.univ : Finset (CoarseBond L ell)),
      cornerBondOf x = cornerBondOf y → x = y :=
    fun x _ y _ hxy => cornerBondOf_injective hell hdvd hxy
  have hterm : ∀ b : CoarseBond L ell,
      ‖WithLp.ofLp (rInv U hell F) (cornerBondOf b)‖ ^ 2
        = ((ell : ℝ) ^ 3) ^ 2 * ‖WithLp.ofLp F b‖ ^ 2 := by
    intro b
    have hct : IsCornerTop ell (cornerBondOf b).1 (cornerBondOf b).2 := by
      obtain ⟨⟨y, hy⟩, μ⟩ := b
      exact isCornerTop_cornerTopSite hell hdvd hy μ
    rw [rInv_apply, norm_secFun_apply, if_pos hct, coarseBond_cornerBondOf hell hdvd b]
    ring
  have hsq : ‖rInv U hell F‖ ^ 2 = (((ell : ℝ) ^ 3) * ‖F‖) ^ 2 := by
    rw [norm_sq_pilp (rInv U hell F)]
    rw [← Finset.sum_subset (Finset.subset_univ
      ((Finset.univ : Finset (CoarseBond L ell)).image cornerBondOf)) hsupp,
      Finset.sum_image hinj]
    rw [Finset.sum_congr rfl (fun b _ => hterm b), ← Finset.mul_sum, ← norm_sq_pilp F]
    ring
  have h1 : (0:ℝ) ≤ ‖rInv U hell F‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ((ell : ℝ) ^ 3) * ‖F‖ := by positivity
  nlinarith [hsq, h1, h2]

theorem opNorm_rInv_le (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ‖rInv U hell‖ ≤ (ell : ℝ) ^ 3 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (fun F => le_of_eq (norm_rInv_apply U hell hdvd F))

/-- **`ell³ ≤ ‖R_U‖`** — the constant is ATTAINED, so it is not a lossy over-estimate. -/
theorem le_opNorm_rInv (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    (ell : ℝ) ^ 3 ≤ ‖rInv U hell‖ := by
  set F : CoarseFnL2 L ell := WithLp.toLp 2 (fun _ => suTwoWitness) with hF
  have hFne : F ≠ 0 := by
    intro hcon
    have h := congrFun (congrArg (fun u : CoarseFnL2 L ell => WithLp.ofLp u) hcon)
      (Classical.arbitrary (CoarseBond L ell))
    simp only [hF, WithLp.ofLp_toLp] at h
    exact suTwoWitness_ne_zero (by simpa using h)
  have hFpos : (0:ℝ) < ‖F‖ := norm_pos_iff.mpr hFne
  have heq := norm_rInv_apply U hell hdvd F
  have hle : ‖rInv U hell F‖ ≤ ‖rInv U hell‖ * ‖F‖ := (rInv U hell).le_opNorm F
  rw [heq] at hle
  exact le_of_mul_le_mul_right (by linarith [hle]) hFpos

/-- **`‖R_U‖ = ell³`, EXACTLY — the right-hand side does not mention `U`.** -/
theorem opNorm_rInv (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ‖rInv U hell‖ = (ell : ℝ) ^ 3 :=
  le_antisymm (opNorm_rInv_le U hell hdvd) (le_opNorm_rInv U hell hdvd)

/-- **TRANSPORT-UNIFORMITY, STATED AS A COMPARISON OF TWO ARBITRARY BACKGROUNDS.**  Not "the
operator is background-free" (it is not) — "the NORM is". -/
theorem opNorm_rInv_transport_uniform
    (U V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ‖rInv U hell‖ = ‖rInv V hell‖ := by
  rw [opNorm_rInv U hell hdvd, opNorm_rInv V hell hdvd]

/-- **THE NORM IS A FUNCTION OF `ell` ALONE**, exhibited as such: one real number serving every
background simultaneously. -/
theorem exists_transport_uniform_bound {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L,
        (∀ F : CoarseFnL2 L ell, qCLM U ell (rInv U hell F) = F) ∧ ‖rInv U hell‖ = c := by
  refine ⟨(ell : ℝ) ^ 3, ?_, fun U => ⟨fun F => qCLM_rInv_apply U hell hdvd F,
    opNorm_rInv U hell hdvd⟩⟩
  have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  positivity

end QSurjRInverse
