/-
`compute/gauge_patching/stage/JLocality.lean`

**GAUGE PATCHING, RESOLVED WITHOUT PATCHING.**

`compute/source_wired/SCOPE.md` §7 residual 2 reduced "the printed regularity class of CMP99b
p.396 implies our gauge-invariant deviation class" to exactly one unproved step: the per-cube
gauges of (3.35) have to be assembled into ONE global gauge.  This file proves that the assembly
is NOT NEEDED for the consumer at hand, and that the resulting bound carries the SAME constant.

The two ingredients are the ones Bałaban himself uses on printed p.408 (image-read at 300 dpi,
`probe/img/p-20.png`; `corpus/pages/CMP99b_p408.md`, `adjudicated`):

> "This follows from Corollary 3.5 applied to the configuration `U' = U^u`, and we have to recall
> only that all the results of these theorems are gauge invariant."
> "We will prove Theorems 3.1-3.3 in full generality localizing them by generalized random walk
> expansions to small domains contained in cubes `□`, and then using the results of this corollary."

i.e. LOCALIZE + GAUGE-INVARIANCE OF THE CONCLUSION.  Here:

* gauge invariance of the conclusion is `SourceWiredGauge.norm_JsuTwo_bond_gaugeT` (already in the
  tree, per BOND: `‖J(U^g)(b)‖ = ‖J(U)(b)‖` for every `g`);
* localization is what this file supplies: `Jstencil b`, the set of bonds `J(·)(b)` reads, ENUMERATED
  FROM THE DEFINING TERMS of `SourceJ.Jfield` / `SourceJ.DstarDir` / `SourceJ.FnuMu` /
  `ClayStatement.periodicPlaquetteHolonomy` (S83: against the definition, not the construction).

§1  `plaqBonds`, `FBonds`, `Jstencil` — the stencil, read off the defining products.
§2  the congruence lemmas: agreement on the stencil forces equality of `J` at that bond.
§3  the cut-off configuration and the LOCAL entrywise bound `EB (495*δ) (Jsource U b)`.
§4  `LocGaugeDev` — the per-cube-gauge class, and THE THEOREM: it gives the same `‖J‖` bound.
§5  the printed shape: a family of cubes + a covering condition ⟹ `LocGaugeDev`.
§6  the locality RADIUS: `Jstencil b` lives in the ℓ∞-ball of radius 1 around `b.1`.

**No `sorry`.  No new axiom.  Nothing outside this lane is written.**
-/
import SourceWiredGauge

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace AdalyFormal.Balaban.GaugePatching

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 conjByAmbient)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem holonomyElemInv imHolonomy)
open AdalyFormal.Balaban.SourceJ (piProj FnuMu DstarDir Jfield Jsource)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.SourceWiredJ (EB JsuTwo JsuTwo_apply EB_Jsource)
open AdalyFormal.Balaban.SourceWired (LinkDev)
open AdalyFormal.Balaban.SourceWiredGauge (gaugeT norm_JsuTwo_bond_gaugeT GaugeEquivLinkDev)

variable {L : PeriodicLatticeExtent}

/-- Abbreviation for the group this whole chain runs on. -/
local notation "SU2" => Matrix.specialUnitaryGroup (Fin 2) ℂ

/-! ## §1 — THE STENCIL, ENUMERATED FROM THE DEFINING PRODUCTS

`ClayStatement.periodicPlaquetteHolonomy U p` is, by its own definition,

    U (x, μ) * U (shift x μ, ν) * (U (shift x ν, μ))⁻¹ * (U (x, ν))⁻¹,   x = p.1, μ = p.2.1.1, ν = p.2.1.2

so exactly four bonds occur in it.  `plaqBonds` is that list of four, and nothing else. -/

/-- The four bonds occurring in `periodicPlaquetteHolonomy`'s own defining product. -/
def plaqBonds (p : PeriodicLatticePlaquette L) : Set (Bond L) :=
  {(p.1, p.2.1.1), (periodicLatticeShift p.1 p.2.1.1, p.2.1.2),
   (periodicLatticeShift p.1 p.2.1.2, p.2.1.1), (p.1, p.2.1.2)}

/-- Cross-check against the tree's OWN four-edge object (LAW-19): `plaqBonds` is exactly the
coercion of `ClayStatement.periodicPlaquetteBoundaryEdges`.  This is a tie to an independently
written enumeration, so a mis-enumeration here would have to be duplicated there. -/
theorem plaqBonds_eq_boundaryEdges (p : PeriodicLatticePlaquette L) :
    plaqBonds p = (periodicPlaquetteBoundaryEdges p : Set (Bond L)) := by
  classical
  unfold plaqBonds periodicPlaquetteBoundaryEdges
  ext e
  simp [Set.mem_insert_iff, Finset.coe_insert]

/-- The bonds `FnuMu U ν μ y` reads — read off `FnuMu`'s own three branches. -/
def FBonds (ν μ : Fin 3) (y : PeriodicLatticeSite L) : Set (Bond L) :=
  if h : ν < μ then plaqBonds (y, ⟨(ν, μ), h⟩)
  else if h' : μ < ν then plaqBonds (y, ⟨(μ, ν), h'⟩)
  else ∅

/-- **`Jstencil b`** — the bonds `Jsource U b` reads.

Read off `Jfield U x μ = ∑_ν (if ν = μ then 0 else DstarDir U ν (FnuMu U ν μ ·) x)` and
`DstarDir U ν G x = conjByAmbient (U (shiftBack x ν, ν))⁻¹ (G (shiftBack x ν)) - G x`:
for each `ν ≠ μ` the transport bond `(shiftBack x ν, ν)`, plus the `F`-bonds at the two sites
`x` and `shiftBack x ν`. -/
def Jstencil (b : Bond L) : Set (Bond L) :=
  {e | ∃ ν : Fin 3, ν ≠ b.2 ∧
        (e = (periodicLatticeShiftBack b.1 ν, ν)
          ∨ e ∈ FBonds ν b.2 b.1
          ∨ e ∈ FBonds ν b.2 (periodicLatticeShiftBack b.1 ν))}

/-! ## §2 — LOCALITY: agreement on the stencil forces equality of `J` at that bond -/

theorem plaquetteHolonomy_congr {U V : PeriodicLinkConfiguration SU2 L}
    (p : PeriodicLatticePlaquette L) (h : ∀ e ∈ plaqBonds p, U e = V e) :
    periodicPlaquetteHolonomy U p = periodicPlaquetteHolonomy V p := by
  unfold periodicPlaquetteHolonomy
  have h1 : U (p.1, p.2.1.1) = V (p.1, p.2.1.1) := h _ (by simp [plaqBonds])
  have h2 : U (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
      = V (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) := h _ (by simp [plaqBonds])
  have h3 : U (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)
      = V (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) := h _ (by simp [plaqBonds])
  have h4 : U (p.1, p.2.1.2) = V (p.1, p.2.1.2) := h _ (by simp [plaqBonds])
  simp only [h1, h2, h3, h4]

theorem holonomyElem_congr {U V : PeriodicLinkConfiguration SU2 L}
    (p : PeriodicLatticePlaquette L) (h : ∀ e ∈ plaqBonds p, U e = V e) :
    holonomyElem U p = holonomyElem V p := by
  unfold holonomyElem
  exact plaquetteHolonomy_congr p h

theorem imHolonomy_congr {U V : PeriodicLinkConfiguration SU2 L}
    (p : PeriodicLatticePlaquette L) (h : ∀ e ∈ plaqBonds p, U e = V e) :
    imHolonomy U p = imHolonomy V p := by
  unfold imHolonomy holonomyElemInv
  rw [holonomyElem_congr p h]

theorem FnuMu_congr {U V : PeriodicLinkConfiguration SU2 L} (ν μ : Fin 3)
    (y : PeriodicLatticeSite L) (h : ∀ e ∈ FBonds ν μ y, U e = V e) :
    FnuMu U ν μ y = FnuMu V ν μ y := by
  unfold FnuMu
  unfold FBonds at h
  split_ifs at h ⊢ with hlt hgt
  · rw [imHolonomy_congr _ h]
  · rw [imHolonomy_congr _ h]
  · rfl

theorem Jfield_congr {U V : PeriodicLinkConfiguration SU2 L} (b : Bond L)
    (h : ∀ e ∈ Jstencil b, U e = V e) : Jfield U b.1 b.2 = Jfield V b.1 b.2 := by
  unfold Jfield
  refine Finset.sum_congr rfl ?_
  intro ν _
  by_cases hν : ν = b.2
  · simp [hν]
  · simp only [hν, if_false]
    have hstF : ∀ (y : PeriodicLatticeSite L), (y = b.1 ∨ y = periodicLatticeShiftBack b.1 ν) →
        ∀ e ∈ FBonds ν b.2 y, U e = V e := by
      rintro y (rfl | rfl) e he
      · exact h e ⟨ν, hν, Or.inr (Or.inl he)⟩
      · exact h e ⟨ν, hν, Or.inr (Or.inr he)⟩
    have hF1 : FnuMu U ν b.2 b.1 = FnuMu V ν b.2 b.1 :=
      FnuMu_congr ν b.2 b.1 (hstF b.1 (Or.inl rfl))
    have hF2 : FnuMu U ν b.2 (periodicLatticeShiftBack b.1 ν)
        = FnuMu V ν b.2 (periodicLatticeShiftBack b.1 ν) :=
      FnuMu_congr ν b.2 _ (hstF _ (Or.inr rfl))
    have hlink : U (periodicLatticeShiftBack b.1 ν, ν) = V (periodicLatticeShiftBack b.1 ν, ν) :=
      h _ ⟨ν, hν, Or.inl rfl⟩
    simp only [DstarDir, hlink, hF1, hF2]

/-- **THE LOCALITY THEOREM.**  `Jsource · b` reads only `Jstencil b`. -/
theorem Jsource_congr {U V : PeriodicLinkConfiguration SU2 L} (b : Bond L)
    (h : ∀ e ∈ Jstencil b, U e = V e) : Jsource U b = Jsource V b :=
  Jfield_congr b h

/-- Non-vacuity of §2 in the direction that matters: the stencil is NOT empty, so `Jsource_congr`
is not the trivial statement "`J` reads nothing".  The transport bond of any `ν ≠ b.2` is in it,
and such a `ν` exists because `Fin 3` has three elements. -/
theorem Jstencil_nonempty (b : Bond L) : (Jstencil b).Nonempty := by
  classical
  obtain ⟨ν, hν⟩ : ∃ ν : Fin 3, ν ≠ b.2 := exists_ne b.2
  exact ⟨(periodicLatticeShiftBack b.1 ν, ν), ⟨ν, hν, Or.inl rfl⟩⟩

/-! ## §3 — CUT-OFF, AND THE LOCAL ENTRYWISE BOUND -/

open Classical in
/-- The configuration that agrees with `U` on `Jstencil b` and is `1` elsewhere. -/
noncomputable def cutoff (U : PeriodicLinkConfiguration SU2 L) (b : Bond L) :
    PeriodicLinkConfiguration SU2 L :=
  fun e => if e ∈ Jstencil b then U e else 1

theorem cutoff_on_stencil (U : PeriodicLinkConfiguration SU2 L) (b : Bond L)
    {e : Bond L} (he : e ∈ Jstencil b) : cutoff U b e = U e := by
  classical
  simp [cutoff, he]

theorem Jsource_cutoff (U : PeriodicLinkConfiguration SU2 L) (b : Bond L) :
    Jsource (cutoff U b) b = Jsource U b :=
  Jsource_congr b (fun e he => cutoff_on_stencil U b he)

theorem linkDev_cutoff {δ : ℝ} (hδ : 0 ≤ δ) (U : PeriodicLinkConfiguration SU2 L) (b : Bond L)
    (h : ∀ e ∈ Jstencil b, EB δ ((U e : Matrix (Fin 2) (Fin 2) ℂ) - 1)) :
    ∀ e : Bond L, EB δ (((cutoff U b) e : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  classical
  intro e
  by_cases he : e ∈ Jstencil b
  · rw [cutoff_on_stencil U b he]; exact h e he
  · have : cutoff U b e = 1 := by simp [cutoff, he]
    rw [this]
    intro i j
    simp only [Submonoid.coe_one, sub_self, Matrix.zero_apply, norm_zero]
    exact hδ

/-- **THE LOCAL ENTRYWISE BOUND.**  The `495·δ` bound on `J(U)(b)` needs the link deviation only on
`Jstencil b`.  The constant is IDENTICAL to `SourceWiredJ.EB_Jsource`'s — it is that theorem,
applied to the cut-off configuration; nothing is re-derived and nothing is lost. -/
theorem EB_Jsource_local {δ : ℝ} (hδ : 0 ≤ δ) (U : PeriodicLinkConfiguration SU2 L) (b : Bond L)
    (h : ∀ e ∈ Jstencil b, EB δ ((U e : Matrix (Fin 2) (Fin 2) ℂ) - 1)) :
    EB (495 * δ) (Jsource U b) := by
  have := EB_Jsource (cutoff U b) (linkDev_cutoff hδ U b h) b
  rwa [Jsource_cutoff U b] at this

/-! ## §4 — THE PER-CUBE-GAUGE CLASS AND THE THEOREM -/

/-- **`LocGaugeDev δ U`** — the LOCALIZED deviation class: for every bond, SOME gauge (its own,
with no relation to any other bond's) brings the configuration within `δ` of the identity on that
bond's stencil.

This is the faithful shape of CMP99b p.396's `∀□ ∃u`: the gauge is existentially quantified INSIDE
the `∀`, exactly as printed, and nothing ties the gauges of two different bonds together. -/
def LocGaugeDev (δ : ℝ) (U : PeriodicLinkConfiguration SU2 L) : Prop :=
  ∀ b : Bond L, ∃ g : PeriodicLatticeSite L → SU2,
    ∀ e ∈ Jstencil b, EB δ (((gaugeT g U) e : Matrix (Fin 2) (Fin 2) ℂ) - 1)

/-- The GLOBAL class implies the local one, trivially (restrict the one gauge). -/
theorem locGaugeDev_of_gaugeEquivLinkDev {δ : ℝ} (U : PeriodicLinkConfiguration SU2 L)
    (h : GaugeEquivLinkDev δ U) : LocGaugeDev δ U := by
  obtain ⟨g, hg⟩ := h
  exact fun b => ⟨g, fun e _ => hg e⟩

/-- `norm_sq_JsuTwo_bond_le`'s content, refactored to take the entrywise bound at ONE bond instead
of the global link-deviation hypothesis.  (Same proof; the hypothesis is what changes.) -/
theorem norm_sq_bond_of_EB {C : ℝ} (hC : 0 ≤ C) (U : PeriodicLinkConfiguration SU2 L) (b : Bond L)
    (hEB : EB C (Jsource U b)) :
    ‖(WithLp.ofLp (JsuTwo U) b : SuTwo)‖ ^ 2 ≤ 2 * C ^ 2 := by
  have hEBI : EB C (Complex.I • Jsource U b) := by
    have hs := hEB.smul Complex.I
    rw [Complex.norm_I] at hs
    refine hs.mono (le_of_eq ?_)
    ring
  have hnorm : ‖(WithLp.ofLp (JsuTwo U) b : SuTwo)‖ ^ 2
      = AdalyFormal.Balaban.SuTwoInner.hsInner (WithLp.ofLp (JsuTwo U) b)
          (WithLp.ofLp (JsuTwo U) b) := by
    rw [← real_inner_self_eq_norm_sq]
    rfl
  rw [hnorm, AdalyFormal.Balaban.SuTwoInner.hsInner_self_eq_sumNormSq]
  have e : ∀ i j, ((WithLp.ofLp (JsuTwo U) b : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) i j
      = (Complex.I • Jsource U b) i j := by
    intro i j; rw [JsuTwo_apply]
  have hb : ∀ i j, Complex.normSq (((WithLp.ofLp (JsuTwo U) b : SuTwo) :
      Matrix (Fin 2) (Fin 2) ℂ) i j) ≤ C ^ 2 := by
    intro i j
    rw [e i j, Complex.normSq_eq_norm_sq]
    have := hEBI i j
    nlinarith [this, norm_nonneg ((Complex.I • Jsource U b) i j)]
  have h00 := hb 0 0
  have h01 := hb 0 1
  have h10 := hb 1 0
  have h11 := hb 1 1
  linarith

/-- **THE PER-BOND BOUND FROM THE PER-CUBE CLASS.**  Gauge invariance is used bond by bond, so the
two cubes of two different bonds never have to be compared. -/
theorem norm_sq_bond_le_of_locGaugeDev {δ : ℝ} (hδ : 0 ≤ δ)
    (U : PeriodicLinkConfiguration SU2 L) (h : LocGaugeDev δ U) (b : Bond L) :
    ‖(WithLp.ofLp (JsuTwo U) b : SuTwo)‖ ^ 2 ≤ 2 * (495 * δ) ^ 2 := by
  obtain ⟨g, hg⟩ := h b
  have hgauged : ‖(WithLp.ofLp (JsuTwo (gaugeT g U)) b : SuTwo)‖ ^ 2 ≤ 2 * (495 * δ) ^ 2 :=
    norm_sq_bond_of_EB (by linarith) _ b (EB_Jsource_local hδ (gaugeT g U) b hg)
  rwa [norm_JsuTwo_bond_gaugeT g U b] at hgauged

/-- **THE THEOREM.**  The printed, per-cube regularity data yields the SAME `‖J(U)‖` bound as the
global-gauge hypothesis it was standing in for: `‖J(U)‖ ≤ √(2·|Bond L|)·495·δ`.

*No patching, and no degradation of the constant.*  `SourceWiredJ.norm_JsuTwo_le` is the special
case `LinkDev δ U`; `SourceWiredGauge.norm_JsuTwo_le_of_gaugeEquivLinkDev` is the special case
`GaugeEquivLinkDev δ U` (see `norm_JsuTwo_le_of_gaugeEquivLinkDev'` below) — and this statement
covers configurations that satisfy NEITHER (see `stage/PerCubeSeparation.lean`). -/
theorem norm_JsuTwo_le_of_locGaugeDev {δ : ℝ} (hδ : 0 ≤ δ)
    (U : PeriodicLinkConfiguration SU2 L) (h : LocGaugeDev δ U) :
    ‖JsuTwo U‖ ≤ Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ) := by
  have hC : (0 : ℝ) ≤ 495 * δ := by linarith
  rw [PiLp.norm_eq_of_L2]
  have hsum : ∑ b : Bond L, ‖(WithLp.ofLp (JsuTwo U) b : SuTwo)‖ ^ 2
      ≤ (Fintype.card (Bond L)) * (2 * (495 * δ) ^ 2) := by
    calc ∑ b : Bond L, ‖(WithLp.ofLp (JsuTwo U) b : SuTwo)‖ ^ 2
        ≤ ∑ _b : Bond L, (2 * (495 * δ) ^ 2) :=
          Finset.sum_le_sum fun b _ => norm_sq_bond_le_of_locGaugeDev hδ U h b
      _ = (Fintype.card (Bond L)) * (2 * (495 * δ) ^ 2) := by
          simp [Finset.sum_const, Finset.card_univ]
  have hfin : Real.sqrt ((Fintype.card (Bond L)) * (2 * (495 * δ) ^ 2))
      = Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ) := by
    rw [show ((Fintype.card (Bond L) : ℝ)) * (2 * (495 * δ) ^ 2)
        = (2 * (Fintype.card (Bond L) : ℝ)) * (495 * δ) ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hC]
  calc Real.sqrt (∑ b : Bond L, ‖(WithLp.ofLp (JsuTwo U) b : SuTwo)‖ ^ 2)
      ≤ Real.sqrt ((Fintype.card (Bond L)) * (2 * (495 * δ) ^ 2)) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ) := hfin

/-- The global-gauge statement is recovered as a special case — so nothing is lost by moving to the
weaker hypothesis. -/
theorem norm_JsuTwo_le_of_gaugeEquivLinkDev' {δ : ℝ} (hδ : 0 ≤ δ)
    (U : PeriodicLinkConfiguration SU2 L) (h : GaugeEquivLinkDev δ U) :
    ‖JsuTwo U‖ ≤ Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ) :=
  norm_JsuTwo_le_of_locGaugeDev hδ U (locGaugeDev_of_gaugeEquivLinkDev U h)

/-- And so is the ungauged one. -/
theorem norm_JsuTwo_le_of_linkDev' {δ : ℝ} (hδ : 0 ≤ δ)
    (U : PeriodicLinkConfiguration SU2 L) (h : LinkDev δ U) :
    ‖JsuTwo U‖ ≤ Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ) :=
  norm_JsuTwo_le_of_locGaugeDev hδ U
    (locGaugeDev_of_gaugeEquivLinkDev U ⟨fun _ => (1 : SU2), by
      intro e
      have hone : gaugeT (fun _ => (1 : SU2)) U e = U e := by
        simp [gaugeT]
      rw [hone]; exact h e⟩)

/-! ## §5 — THE PRINTED SHAPE: A FAMILY OF CUBES PLUS A COVERING CONDITION -/

/-- **`CubeGaugeData δ U 𝒞`** — CMP99b (3.35) as a hypothesis about a family `𝒞` of cubes (each
cube presented as its set of bonds): for EACH cube, SOME gauge makes the configuration `δ`-close to
the identity ON THAT CUBE.  Nothing relates the gauges of two cubes. -/
def CubeGaugeData (δ : ℝ) (U : PeriodicLinkConfiguration SU2 L) (𝒞 : Set (Set (Bond L))) : Prop :=
  ∀ C ∈ 𝒞, ∃ g : PeriodicLatticeSite L → SU2,
    ∀ e ∈ C, EB δ (((gaugeT g U) e : Matrix (Fin 2) (Fin 2) ℂ) - 1)

/-- **`StencilCovered 𝒞`** — the ONLY geometric input the implication needs: every bond's stencil
sits inside a single cube of the family.  This is the exact residual left by this file, and it is a
statement about the CUBE GEOMETRY alone (no gauge, no configuration). -/
def StencilCovered (𝒞 : Set (Set (Bond L))) : Prop :=
  ∀ b : Bond L, ∃ C ∈ 𝒞, Jstencil b ⊆ C

/-- **THE PRINTED-CLASS IMPLICATION.**  `∀□ ∃u` (as printed) + "every stencil is inside some cube"
⟹ the `‖J‖` bound, with the same constant.  No compatibility condition between the cubes' gauges
appears anywhere in the hypotheses — because none is used. -/
theorem norm_JsuTwo_le_of_cubes {δ : ℝ} (hδ : 0 ≤ δ) (U : PeriodicLinkConfiguration SU2 L)
    (𝒞 : Set (Set (Bond L))) (hcov : StencilCovered 𝒞) (hdata : CubeGaugeData δ U 𝒞) :
    ‖JsuTwo U‖ ≤ Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ) := by
  refine norm_JsuTwo_le_of_locGaugeDev hδ U ?_
  intro b
  obtain ⟨C, hC, hsub⟩ := hcov b
  obtain ⟨g, hg⟩ := hdata C hC
  exact ⟨g, fun e he => hg e (hsub he)⟩

/-! ## §6 — THE LOCALITY RADIUS: `Jstencil b` lies in the ℓ∞-ball of radius 1 around `b.1`

This is what makes `StencilCovered` cheap for a genuine cube family: p.396's cubes have size
`O(1)ML^jη` with `O(1) ≥ 10` (and `= 12` on p.409), while the stencil has radius ONE lattice
spacing. -/

/-- The ℓ∞-ball of radius one: every coordinate is within one step of `x`'s. -/
def BallOne (x : PeriodicLatticeSite L) : Set (PeriodicLatticeSite L) :=
  {y | ∀ μ : Fin 3, y μ = x μ - 1 ∨ y μ = x μ ∨ y μ = x μ + 1}

theorem shift_mem_ballOne (x : PeriodicLatticeSite L) (μ : Fin 3) :
    periodicLatticeShift x μ ∈ BallOne x := by
  intro ν
  by_cases h : ν = μ
  · subst h; right; right; simp [periodicLatticeShift]
  · right; left; simp [periodicLatticeShift, h]

theorem shiftBack_mem_ballOne (x : PeriodicLatticeSite L) (μ : Fin 3) :
    periodicLatticeShiftBack x μ ∈ BallOne x := by
  intro ν
  by_cases h : ν = μ
  · subst h; left; simp [periodicLatticeShiftBack]
  · right; left; simp [periodicLatticeShiftBack, h]

/-- One step out of a ball-of-one point, in a direction, stays inside the ball provided the step
undoes or is orthogonal to the original one.  Stated in the only form used: shifting `shiftBack x ν`
by a direction `a` lands in `BallOne x`. -/
theorem shift_shiftBack_mem_ballOne (x : PeriodicLatticeSite L) (ν a : Fin 3) :
    periodicLatticeShift (periodicLatticeShiftBack x ν) a ∈ BallOne x := by
  intro μ
  by_cases ha : μ = a
  · subst ha
    by_cases hν : μ = ν
    · subst hν
      right; left
      simp [periodicLatticeShift, periodicLatticeShiftBack]
    · right; right
      simp [periodicLatticeShift, periodicLatticeShiftBack, hν]
  · by_cases hν : μ = ν
    · subst hν
      left
      simp [periodicLatticeShift, periodicLatticeShiftBack, Function.update_apply, ha]
    · right; left
      simp [periodicLatticeShift, periodicLatticeShiftBack, ha, hν]

theorem plaqBonds_base_mem {x : PeriodicLatticeSite L} {p : PeriodicLatticePlaquette L}
    (hp : p.1 ∈ BallOne x)
    (hshift : ∀ a : Fin 3, periodicLatticeShift p.1 a ∈ BallOne x)
    {e : Bond L} (he : e ∈ plaqBonds p) : e.1 ∈ BallOne x := by
  rcases he with h | h | h | h <;> (rw [h]) <;> simp only []
  · exact hp
  · exact hshift _
  · exact hshift _
  · exact hp

/-- **THE RADIUS THEOREM.**  Every bond of `Jstencil b` has its base site within one lattice step
of `b.1` in every coordinate. -/
theorem Jstencil_subset_ballOne (b : Bond L) :
    ∀ e ∈ Jstencil b, e.1 ∈ BallOne b.1 := by
  rintro e ⟨ν, _, hcase⟩
  have hx : b.1 ∈ BallOne b.1 := by intro μ; right; left; rfl
  rcases hcase with h | h | h
  · rw [h]; exact shiftBack_mem_ballOne b.1 ν
  · -- `F`-bonds at the site `b.1`
    unfold FBonds at h
    split_ifs at h with h1 h2
    · exact plaqBonds_base_mem hx (fun a => shift_mem_ballOne b.1 a) h
    · exact plaqBonds_base_mem hx (fun a => shift_mem_ballOne b.1 a) h
    · exact h.elim
  · -- `F`-bonds at the site `shiftBack b.1 ν`
    unfold FBonds at h
    split_ifs at h with h1 h2
    · exact plaqBonds_base_mem (shiftBack_mem_ballOne b.1 ν)
        (fun a => shift_shiftBack_mem_ballOne b.1 ν a) h
    · exact plaqBonds_base_mem (shiftBack_mem_ballOne b.1 ν)
        (fun a => shift_shiftBack_mem_ballOne b.1 ν a) h
    · exact h.elim

/-- **The covering criterion, in usable form.**  A family of cubes that contains, for every bond,
some cube carrying every bond based in the ℓ∞-ball of radius one around that bond's site, is
stencil-covering.  (This is the geometric fact a genuine p.396 cube family supplies with room to
spare: cube size `≥ 10ML^jη`, stencil radius `1`.) -/
theorem stencilCovered_of_ballOne (𝒞 : Set (Set (Bond L)))
    (h : ∀ b : Bond L, ∃ C ∈ 𝒞, ∀ e : Bond L, e.1 ∈ BallOne b.1 → e ∈ C) :
    StencilCovered 𝒞 := by
  intro b
  obtain ⟨C, hC, hCball⟩ := h b
  exact ⟨C, hC, fun e he => hCball e (Jstencil_subset_ballOne b e he)⟩

#print axioms plaqBonds_eq_boundaryEdges
#print axioms Jsource_congr
#print axioms Jstencil_nonempty
#print axioms EB_Jsource_local
#print axioms locGaugeDev_of_gaugeEquivLinkDev
#print axioms norm_sq_bond_le_of_locGaugeDev
#print axioms norm_JsuTwo_le_of_locGaugeDev
#print axioms norm_JsuTwo_le_of_gaugeEquivLinkDev'
#print axioms norm_JsuTwo_le_of_linkDev'
#print axioms norm_JsuTwo_le_of_cubes
#print axioms Jstencil_subset_ballOne
#print axioms stencilCovered_of_ballOne

end AdalyFormal.Balaban.GaugePatching
