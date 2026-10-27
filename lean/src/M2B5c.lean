import M2B5b

/-!
# M2B5c -- the concrete box cutoff `chi z (cutFam s w L)` and the abstract `CutSpec` consumed by the matrix algebra (m2_bridge_20261014, Layer B1)

`cutF s w = prof (2w+4) (s-6) w` : `ProfSpec` with `τ1 = 1/w`, `τ2 = 2/w²`, `lo = 6`, `hi = s - 7`; equals `1` on `[2w+4, s-2w-5]`.
`cutFam s w L σ` : the factor used in coordinate `σ`: `cutF s w` if the cube fits (`s ≤ L σ + 1`, NARROW coordinate) and the constant `1` if it wraps (`L σ + 1 < s`, WIDE).
`CutSpec sites χ τ1 τ2` : the properties of a site function `χ` used by the Leibniz computation of `M2B6`
(range in `[0,1]`, forward/backward first differences `≤ τ1`, centred second difference `≤ τ2`, mixed second difference `≤ τ1²`,
and support margin 6: `χ x ≠ 0 → every y with pdist x y ≤ 6 lies in sites`).
`cutoff_spec` : `CutSpec (siteBox z s) (chi z (cutFam s w L)) (1/w) (2/w²)` for ANY torus (`L σ ≥ 1`), `7 ≤ s`, `1 ≤ w` -- no condition relating the cube side to the torus.
`cutoff_core` : `χ = 1` where every NARROW coordinate has its offset in `[2w+4, s-2w-5]`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Bridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

variable {L : PeriodicLatticeExtent}

noncomputable def cutF (s w : ℕ) : ℕ → ℝ := prof (2 * w + 4) (s - 6) w

theorem cutF_spec {s w : ℕ} (hw : 1 ≤ w) (hs : 7 ≤ s) :
    ProfSpec (cutF s w) (1 / (w : ℝ)) (2 / (w : ℝ) ^ 2) 6 (s - 7) where
  nonneg := fun o => prof_nonneg _ _ _ o
  le_one := fun o => prof_le_one hw o
  first := fun o => prof_first hw o
  second := fun o => prof_second hw o
  supp := fun o ho => by
    obtain ⟨h1, h2⟩ := prof_support ho
    constructor <;> omega
  lo2 := by norm_num

theorem cutF_one {s w o : ℕ} (hw : 1 ≤ w) (h1 : 2 * w + 4 ≤ o) (h2 : o + 2 * w + 5 ≤ s) : cutF s w o = 1 :=
  prof_one hw h1 (by omega)

/-- the factor used in each coordinate: the profile where the cube fits, the constant `1` where it wraps. -/
noncomputable def cutFam (s w : ℕ) (L : PeriodicLatticeExtent) : Fin 3 → ℕ → ℝ :=
  fun σ => if s ≤ L σ + 1 then cutF s w else fun _ => 1

theorem cutFam_coord {s w : ℕ} (hw : 1 ≤ w) (hs : 7 ≤ s) (σ : Fin 3) :
    CoordSpec (L σ) (cutFam s w L σ) (1 / (w : ℝ)) (2 / (w : ℝ) ^ 2) := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  unfold cutFam
  by_cases h : s ≤ L σ + 1
  · rw [if_pos h]
    exact coordSpec_prof (cutF_spec hw hs) (by omega)
  · rw [if_neg h]
    exact coordSpec_one (by positivity) (by positivity)

theorem cutFam_reach (z : PeriodicLatticeSite L) {s w : ℕ} (hw : 1 ≤ w) (hs : 7 ≤ s) (σ : Fin 3) :
    Reach z σ s (cutFam s w L σ) := by
  unfold cutFam
  by_cases h : s ≤ L σ + 1
  · rw [if_pos h]
    exact reach_prof z σ (cutF_spec hw hs) (by norm_num) (by omega) h
  · rw [if_neg h]
    exact reach_one z σ (by omega)

/-- the properties of a cutoff used by the Leibniz computation. -/
structure CutSpec (sites : Set (PeriodicLatticeSite L)) (χ : PeriodicLatticeSite L → ℝ) (τ1 τ2 : ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ χ x
  le_one : ∀ x, χ x ≤ 1
  fwd : ∀ x μ, |χ (periodicLatticeShift x μ) - χ x| ≤ τ1
  bwd : ∀ x μ, |χ (periodicLatticeShiftBack x μ) - χ x| ≤ τ1
  sec : ∀ x ν, |χ (periodicLatticeShift x ν) + χ (periodicLatticeShiftBack x ν) - 2 * χ x| ≤ τ2
  mixed : ∀ x μ ν, ν ≠ μ →
    |(χ (periodicLatticeShift x μ) - χ x)
      - (χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) - χ (periodicLatticeShiftBack x ν))| ≤ τ1 ^ 2
  supp : ∀ x, χ x ≠ 0 → ∀ y, pdist x y ≤ 6 → y ∈ sites

theorem cutoff_spec (z : PeriodicLatticeSite L) {s w : ℕ} (hw : 1 ≤ w) (hs : 7 ≤ s) (hL : ∀ σ, 1 ≤ L σ) :
    CutSpec (siteBox z s) (chi z (cutFam s w L)) (1 / (w : ℝ)) (2 / (w : ℝ) ^ 2) := by
  have hF := fun σ => cutFam_coord (L := L) (s := s) hw hs σ
  exact
  { nonneg := chi_nonneg hF hL z
    le_one := chi_le_one hF hL z
    fwd := chi_first_fwd hF hL z
    bwd := chi_first_bwd hF hL z
    sec := chi_second hF hL z
    mixed := fun x μ ν h => chi_mixed hF hL z x h
    supp := fun x hx y hy => chi_support_box hF hL z (fun σ => cutFam_reach z hw hs σ) x hx y hy }

theorem cutoff_core (z : PeriodicLatticeSite L) {s w : ℕ} (hw : 1 ≤ w) (hs : 7 ≤ s) (hL : ∀ σ, 1 ≤ L σ)
    (x : PeriodicLatticeSite L)
    (hx : ∀ σ, s ≤ L σ + 1 → 2 * w + 4 ≤ offc z x σ ∧ offc z x σ + 2 * w + 5 ≤ s) : chi z (cutFam s w L) x = 1 := by
  have hF := fun σ => cutFam_coord (L := L) (s := s) hw hs σ
  refine chi_one hF hL z x (fun σ => ?_)
  unfold cutFam
  by_cases h : s ≤ L σ + 1
  · rw [if_pos h]; exact cutF_one hw (hx σ h).1 (hx σ h).2
  · rw [if_neg h]

end AdalyFormal.M2Bridge

#print axioms AdalyFormal.M2Bridge.cutoff_spec
#print axioms AdalyFormal.M2Bridge.cutoff_core
