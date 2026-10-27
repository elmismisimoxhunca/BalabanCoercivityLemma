/-
`compute/gauge_patching/stage/PerCubeSeparation.lean`

**THE PRINTED PER-CUBE CLASS IS STRICTLY WEAKER THAN THE GLOBAL-GAUGE CLASS — PROVED, BY NAME.**

`JLocality.lean` proves that CMP99b p.396's per-cube data suffices for the `‖J‖` bound with the
same constant.  This file proves the other half of the honest answer: the per-cube data does NOT
imply the global hypothesis the tree had been using (`SourceWiredGauge.GaugeEquivLinkDev`), so the
restatement is mandatory, not cosmetic.

The witness is a FLAT configuration with a nontrivial Polyakov loop, on a `4×4×4` periodic lattice:

    U₀(x,μ) = z   if μ = 0 and x₀ = 3,        z = -1 ∈ SU(2)
    U₀(x,μ) = 1   otherwise.

* **Locally exactly gaugeable** (`U0_locGaugeDev_zero`): for EVERY bond, a gauge `u_k` moves the
  defect layer to `x₀ = k` and the configuration is EXACTLY `1` on that bond's whole `J`-stencil.
  So `U₀ ∈ LocGaugeDev 0` — the per-cube class at its STRONGEST parameter, `δ = 0`.
* **Globally not gaugeable at any `δ < 1`** — indeed not at `δ = 0`
  (`U0_not_gaugeEquivLinkDev_zero`): a global gauge with `U₀^g ≡ 1` would force the direction-`0`
  Polyakov loop `z` to equal `1`.

Nothing here is existential over free data: `L4`, `zEl`, `U0`, `uk`, `site` are all given by name
(S91).  The one `∃` that is CONCLUDED (`U0_locGaugeDev_zero`) supplies its witness explicitly as
`uk (b.1 0 + 2)`.
-/
import JLocality

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace AdalyFormal.Balaban.GaugePatching.Sep

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SourceWiredJ (EB JsuTwo)
open AdalyFormal.Balaban.SourceWiredGauge (gaugeT GaugeEquivLinkDev holonomyElem_gaugeT)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem)
open AdalyFormal.Balaban.GaugePatching

local notation "SU2" => Matrix.specialUnitaryGroup (Fin 2) ℂ

/-! ## §1 — THE OBJECTS, ALL BY NAME -/

/-- The `4×4×4` periodic lattice (`L μ = 3` means side `L μ + 1 = 4`). -/
def L4 : PeriodicLatticeExtent := fun _ => 3

/-- `-1 ∈ SU(2)`: unitary because `(-1)*(-1) = 1`, unimodular because `det(-1) = (-1)² = 1`. -/
theorem negOne_mem : (-1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  constructor
  · show (-1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ
    rw [Matrix.mem_unitaryGroup_iff]
    simp
  · show Matrix.detMonoidHom (-1 : Matrix (Fin 2) (Fin 2) ℂ) = 1
    show Matrix.det (-1 : Matrix (Fin 2) (Fin 2) ℂ) = 1
    rw [show (-1 : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) by
      simp, Matrix.det_smul]
    simp

/-- `z := -1`, the nontrivial central element of `SU(2)`. -/
def zEl : SU2 := ⟨-1, negOne_mem⟩

theorem zEl_ne_one : zEl ≠ (1 : SU2) := by
  intro h
  have h' : ((zEl : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by rw [h]; rfl
  have h0 : ((zEl : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
    rw [h']
  simp [zEl] at h0
  exact absurd h0 (by norm_num)

/-- The witness configuration: `1` everywhere except on the direction-`0` links of the layer
`x₀ = 3`, which carry `z`.  Every plaquette holonomy is `1` (the two direction-`0` links of a
`(0,ν)` plaquette sit in the SAME layer and cancel), so this is a FLAT configuration. -/
def U0 : PeriodicLinkConfiguration SU2 L4 :=
  fun e => if e.2 = 0 ∧ e.1 0 = 3 then zEl else 1

/-- The gauge that moves the defect layer to `x₀ = k`. -/
def uk (k : Fin 4) : PeriodicLatticeSite L4 → SU2 := fun x => if x 0 ≤ k then zEl else 1

/-- The `0`-coordinate of a site, at the type `Fin 4` (`L4 0 + 1` reduces to `4`). -/
def coord0 (x : PeriodicLatticeSite L4) : Fin 4 := x 0

/-- The sites of the direction-`0` axis through the origin. -/
def site (n : Fin 4) : PeriodicLatticeSite L4 := fun μ => if μ = 0 then n else 0

theorem site_coord0 (n : Fin 4) : site n 0 = n := by simp [site]

theorem shift_site (n : Fin 4) : periodicLatticeShift (site n) 0 = site (n + 1) := by
  funext μ
  by_cases h : μ = 0
  · subst h; simp [periodicLatticeShift, site]; try rfl
  · simp [periodicLatticeShift, site, h]

theorem coord0_def_check (x : PeriodicLatticeSite L4) : coord0 x = x 0 := rfl

/-! ## §2 — NO GLOBAL GAUGE FLATTENS `U₀` -/

theorem U0_axis_ne (n : Fin 4) (h : n ≠ 3) : U0 (site n, (0 : Fin 3)) = 1 := by
  show (if ((0 : Fin 3) = 0 ∧ site n 0 = 3) then zEl else 1) = 1
  have hnp : ¬ ((0 : Fin 3) = 0 ∧ site n 0 = 3) := by
    rintro ⟨-, h2⟩
    rw [site_coord0] at h2
    exact h h2
  rw [if_neg hnp]

theorem U0_axis_three : U0 (site 3, (0 : Fin 3)) = zEl := by
  show (if ((0 : Fin 3) = 0 ∧ site 3 0 = 3) then zEl else 1) = zEl
  rw [site_coord0]
  simp

/-- **The Polyakov obstruction.**  If a single global gauge `g` flattens `U₀` on every bond, the
four direction-`0` links through the origin telescope and force `z = 1`. -/
theorem U0_no_global_flat :
    ¬ ∃ g : PeriodicLatticeSite L4 → SU2, ∀ e : Bond L4, gaugeT g U0 e = 1 := by
  rintro ⟨g, hg⟩
  have step : ∀ n : Fin 4, g (site n) * U0 (site n, (0 : Fin 3)) = g (site (n + 1)) := by
    intro n
    have h := hg (site n, (0 : Fin 3))
    rw [AdalyFormal.Balaban.SourceWiredGauge.gaugeT_apply] at h
    have h' : g (site n) * U0 (site n, (0 : Fin 3))
        * (g (periodicLatticeShift (site n) (0 : Fin 3)))⁻¹
          * g (periodicLatticeShift (site n) (0 : Fin 3))
        = 1 * g (periodicLatticeShift (site n) (0 : Fin 3)) := by rw [h]
    rw [inv_mul_cancel_right, one_mul, shift_site] at h'
    exact h'
  have s0 := step 0
  have s1 := step 1
  have s2 := step 2
  have s3 := step 3
  rw [U0_axis_ne 0 (by decide), mul_one, show (0 : Fin 4) + 1 = 1 from by decide] at s0
  rw [U0_axis_ne 1 (by decide), mul_one, show (1 : Fin 4) + 1 = 2 from by decide] at s1
  rw [U0_axis_ne 2 (by decide), mul_one, show (2 : Fin 4) + 1 = 3 from by decide] at s2
  rw [U0_axis_three, show (3 : Fin 4) + 1 = 0 from by decide] at s3
  rw [← s2, ← s1, ← s0] at s3
  refine zEl_ne_one (mul_left_cancel (a := g (site 0)) ?_)
  rw [s3, mul_one]

/-! ## §3 — EVERY STENCIL IS EXACTLY FLATTENED BY SOME GAUGE -/

/-- The layer algebra, enumerated over `Fin 4 × Fin 4`: away from the layer `c = k` the two
`u_k`-factors cancel, and on the wrap-around layer `c = 3` they cancel the defect. -/
theorem layer_algebra (c k : Fin 4) (h : c ≠ k) :
    (if c ≤ k then zEl else 1) * (if c = 3 then zEl else 1)
      * ((if c + 1 ≤ k then zEl else 1))⁻¹ = 1 := by
  fin_cases c <;> fin_cases k <;> simp_all

theorem gaugeT_uk_eq_one (k : Fin 4) (e : Bond L4) (h : e.1 0 ≠ k) :
    gaugeT (uk k) U0 e = 1 := by
  rw [AdalyFormal.Balaban.SourceWiredGauge.gaugeT_apply]
  by_cases hd : e.2 = 0
  · have hshift : (periodicLatticeShift e.1 e.2) 0 = e.1 0 + 1 := by
      rw [hd]; simp [periodicLatticeShift]
    have hU : U0 e = if e.1 0 = 3 then zEl else 1 := by
      by_cases h3 : e.1 0 = 3
      · simp [U0, hd, h3]
      · simp [U0, hd, h3]
    rw [hU]
    show (if e.1 0 ≤ k then zEl else 1) * (if e.1 0 = 3 then zEl else 1)
        * ((uk k) (periodicLatticeShift e.1 e.2))⁻¹ = 1
    rw [show (uk k) (periodicLatticeShift e.1 e.2)
        = if (periodicLatticeShift e.1 e.2) 0 ≤ k then zEl else 1 from rfl, hshift]
    exact layer_algebra (e.1 0) k h
  · have hshift : (periodicLatticeShift e.1 e.2) 0 = e.1 0 := by
      simp [periodicLatticeShift, Ne.symm hd]
    have hU : U0 e = 1 := by simp [U0, hd]
    rw [hU]
    show (uk k) e.1 * 1 * ((uk k) (periodicLatticeShift e.1 e.2))⁻¹ = 1
    rw [show (uk k) (periodicLatticeShift e.1 e.2)
        = if (periodicLatticeShift e.1 e.2) 0 ≤ k then zEl else 1 from rfl, hshift,
      show (uk k) e.1 = if e.1 0 ≤ k then zEl else 1 from rfl, mul_one]
    exact mul_inv_cancel _

/-- The three ball-of-one offsets all miss `c + 2` in `Fin 4`. -/
theorem fin4_avoid : ∀ c : Fin 4, c - 1 ≠ c + 2 ∧ c ≠ c + 2 ∧ c + 1 ≠ c + 2 := by decide

/-- **`U₀` is in the per-cube class at `δ = 0`** — the STRONGEST possible printed data: for every
bond, an explicit gauge makes the configuration exactly the identity on that bond's whole stencil.
The witness is `uk (b.1 0 + 2)`, produced by name, not by choice. -/
theorem U0_stencil_flat (b : Bond L4) :
    ∀ e ∈ Jstencil b, gaugeT (uk (coord0 b.1 + 2)) U0 e = 1 := by
  intro e he
  have hball := Jstencil_subset_ballOne b e he
  have h0 : coord0 e.1 = coord0 b.1 - 1 ∨ coord0 e.1 = coord0 b.1
      ∨ coord0 e.1 = coord0 b.1 + 1 := hball 0
  obtain ⟨ha, hb, hc⟩ := fin4_avoid (coord0 b.1)
  have hne : coord0 e.1 ≠ coord0 b.1 + 2 := by
    rcases h0 with h | h | h <;> rw [h]
    · exact ha
    · exact hb
    · exact hc
  exact gaugeT_uk_eq_one _ e hne

theorem U0_locGaugeDev_zero : LocGaugeDev 0 U0 := by
  intro b
  refine ⟨uk (coord0 b.1 + 2), ?_⟩
  intro e he
  rw [U0_stencil_flat b e he]
  intro i j
  simp

/-! ## §4 — THE SEPARATION, AND WHAT IT BUYS -/

/-- `EB 0` forces the matrix to vanish. -/
theorem eq_one_of_EB_zero {G : SU2} (h : EB 0 ((G : Matrix (Fin 2) (Fin 2) ℂ) - 1)) :
    G = 1 := by
  have hm : (G : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    funext i j
    have := h i j
    have hz : ((G : Matrix (Fin 2) (Fin 2) ℂ) - 1) i j = 0 :=
      norm_le_zero_iff.mp this
    rw [Matrix.sub_apply] at hz
    linear_combination (norm := module) hz
  exact Subtype.ext hm

/-- **THE SEPARATION.**  `U₀` is in the per-cube class at `δ = 0` and in the global class at NO
`δ = 0` — the global hypothesis the tree used is strictly stronger than the printed data. -/
theorem U0_not_gaugeEquivLinkDev_zero : ¬ GaugeEquivLinkDev 0 U0 := by
  rintro ⟨g, hg⟩
  exact U0_no_global_flat ⟨g, fun e => eq_one_of_EB_zero (hg e)⟩

/-- **NON-VACUITY OF `JLocality`'s THEOREM.**  The main theorem applies to `U₀`, which satisfies
NEITHER `LinkDev 0` nor `GaugeEquivLinkDev 0`, and returns `J(U₀) = 0`.  So the per-cube hypothesis
is not merely weaker on paper: it decides a configuration the global hypothesis cannot reach. -/
theorem JsuTwo_U0_eq_zero : JsuTwo U0 = 0 := by
  have h := norm_JsuTwo_le_of_locGaugeDev (le_refl (0 : ℝ)) U0 U0_locGaugeDev_zero
  have h0 : Real.sqrt (2 * (Fintype.card (Bond L4))) * (495 * (0 : ℝ)) = 0 := by ring
  rw [h0] at h
  exact norm_le_zero_iff.mp h

/-- The same, stated as the strictness of the inclusion of classes. -/
theorem locGaugeDev_strictly_weaker :
    (∀ (U : PeriodicLinkConfiguration SU2 L4), GaugeEquivLinkDev 0 U → LocGaugeDev 0 U)
      ∧ ¬ (∀ (U : PeriodicLinkConfiguration SU2 L4), LocGaugeDev 0 U → GaugeEquivLinkDev 0 U) := by
  refine ⟨fun U h => locGaugeDev_of_gaugeEquivLinkDev U h, ?_⟩
  intro hall
  exact U0_not_gaugeEquivLinkDev_zero (hall U0 U0_locGaugeDev_zero)


/-! ## §5 — THE CLASS IS NOT CHEAP: A CONFIGURATION **OUTSIDE** `LocGaugeDev 0`

`compute/cube_geometry/CUBE_SPEC.md` §3 item 7 set the negative control: any per-cube gauge
condition must be checked against `formal/AdalyFormal/IS_REGULAR.md`'s `exists_gauge_bond_vanishes`,
which proves that
an UNCORRELATED PER-BOND existential is satisfied by EVERY configuration and therefore certifies
nothing.  `LocGaugeDev` is not of that kind, and here is the proof: a configuration with ONE
non-flat plaquette fails it, because a stencil contains a whole plaquette and plaquette holonomy is
gauge invariant. -/

/-- One non-flat plaquette: `z` on a single link, `1` elsewhere. -/
def U1 : PeriodicLinkConfiguration SU2 L4 :=
  fun e => if e = (site 0, (0 : Fin 3)) then zEl else 1

/-- The plaquette that link sits on. -/
def pBad : PeriodicLatticePlaquette L4 := (site 0, ⟨(0, 1), by decide⟩)

theorem U1_off {e : Bond L4} (h : e ≠ (site 0, (0 : Fin 3))) : U1 e = 1 := by
  simp [U1, h]

theorem shift_site_one_ne : periodicLatticeShift (site (0 : Fin 4)) 1 ≠ site 0 := by
  intro h
  have h1 := congrFun h 1
  simp [periodicLatticeShift, site, L4] at h1

theorem hol_U1_pBad : holonomyElem U1 pBad = zEl := by
  show U1 (site 0, (0 : Fin 3)) * U1 (periodicLatticeShift (site 0) (0 : Fin 3), (1 : Fin 3))
      * (U1 (periodicLatticeShift (site 0) (1 : Fin 3), (0 : Fin 3)))⁻¹
      * (U1 (site 0, (1 : Fin 3)))⁻¹ = zEl
  have e0 : U1 (site (0 : Fin 4), (0 : Fin 3)) = zEl := by simp [U1]
  have e1 : U1 (periodicLatticeShift (site (0 : Fin 4)) (0 : Fin 3), (1 : Fin 3)) = 1 := by
    refine U1_off ?_
    intro hcon
    have := congrArg Prod.snd hcon
    simp at this
  have e2 : U1 (periodicLatticeShift (site (0 : Fin 4)) (1 : Fin 3), (0 : Fin 3)) = 1 := by
    refine U1_off ?_
    intro hcon
    exact shift_site_one_ne (congrArg Prod.fst hcon)
  have e3 : U1 (site (0 : Fin 4), (1 : Fin 3)) = 1 := by
    refine U1_off ?_
    intro hcon
    have := congrArg Prod.snd hcon
    simp at this
  rw [e0, e1, e2, e3]
  group

theorem FBonds01 : FBonds (0 : Fin 3) 1 (site (0 : Fin 4)) = plaqBonds pBad := by
  unfold FBonds
  rw [dif_pos (by decide : (0 : Fin 3) < 1)]
  rfl

theorem plaqBonds_pBad_sub_stencil :
    ∀ e ∈ plaqBonds pBad, e ∈ Jstencil ((site (0 : Fin 4)), (1 : Fin 3)) := by
  intro e he
  refine ⟨0, by decide, Or.inr (Or.inl ?_)⟩
  rw [FBonds01]
  exact he

theorem holonomyElem_one : holonomyElem (fun _ : Bond L4 => (1 : SU2)) pBad = 1 := by
  show (1 : SU2) * 1 * (1 : SU2)⁻¹ * (1 : SU2)⁻¹ = 1
  group

/-- **THE NEGATIVE CONTROL.**  `LocGaugeDev 0` is NOT satisfied by every configuration: `U₁` has a
plaquette with holonomy `z ≠ 1`, and a stencil containing that plaquette cannot be gauged flat. -/
theorem U1_not_locGaugeDev_zero : ¬ LocGaugeDev 0 U1 := by
  intro h
  obtain ⟨g, hg⟩ := h ((site (0 : Fin 4)), (1 : Fin 3))
  have hflat : ∀ e ∈ plaqBonds pBad, gaugeT g U1 e = (fun _ : Bond L4 => (1 : SU2)) e :=
    fun e he => eq_one_of_EB_zero (hg e (plaqBonds_pBad_sub_stencil e he))
  have h1 : holonomyElem (gaugeT g U1) pBad = holonomyElem (fun _ : Bond L4 => (1 : SU2)) pBad :=
    holonomyElem_congr pBad hflat
  rw [holonomyElem_gaugeT, hol_U1_pBad, holonomyElem_one] at h1
  refine zEl_ne_one (mul_left_cancel (a := g pBad.1) ?_)
  calc g pBad.1 * zEl = g pBad.1 * zEl * (g pBad.1)⁻¹ * g pBad.1 := by group
    _ = 1 * g pBad.1 := by rw [h1]
    _ = g pBad.1 * 1 := by rw [one_mul, mul_one]

/-- Stated as the dichotomy the negative control establishes: the per-cube class separates
configurations — `U₀` is in it, `U₁` is not. -/
theorem locGaugeDev_zero_separates :
    LocGaugeDev 0 U0 ∧ ¬ LocGaugeDev 0 U1 :=
  ⟨U0_locGaugeDev_zero, U1_not_locGaugeDev_zero⟩

#print axioms negOne_mem
#print axioms zEl_ne_one
#print axioms shift_site
#print axioms coord0_def_check
#print axioms U0_axis_ne
#print axioms U0_axis_three
#print axioms U0_no_global_flat
#print axioms layer_algebra
#print axioms gaugeT_uk_eq_one
#print axioms fin4_avoid
#print axioms U0_stencil_flat
#print axioms U0_locGaugeDev_zero
#print axioms eq_one_of_EB_zero
#print axioms U0_not_gaugeEquivLinkDev_zero
#print axioms JsuTwo_U0_eq_zero
#print axioms locGaugeDev_strictly_weaker
#print axioms U1_off
#print axioms shift_site_one_ne
#print axioms hol_U1_pBad
#print axioms FBonds01
#print axioms plaqBonds_pBad_sub_stencil
#print axioms holonomyElem_one
#print axioms U1_not_locGaugeDev_zero
#print axioms locGaugeDev_zero_separates

end AdalyFormal.Balaban.GaugePatching.Sep
