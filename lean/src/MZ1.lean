import CovF
import CovH
import DS3

/-!
# MZ1 -- uncovered `ddA` stencils lie on a codimension-2 set (m2_dlayer, 2026-10-15)

Printed class (r8): class cubes are grid-aligned boxes `siteBox z (12 · M ℓ^i)`, `z` on the `M ℓ^i` grid.
`NP g t` : the coordinate `t` is next to a plane of the grid `g` (`t ≡ 0` or `t ≡ −1 mod g`).

* `box1_succ`, `box1_pred` : one coordinate.  A grid-aligned interval that contains `t` also contains `t + 1` unless
  `t ≡ −1`, and `t − 1` unless `t ≡ 0` (mod any `g ≥ 2` dividing the grid).
* `near1_in_box` : a box containing `x` contains the whole one-step neighbourhood of `x` once the at most two
  "crossing" neighbours are supplied.
* **`stencil_cov`** : under `Admissible`, `CoversOm0p ℓ M 12 k S`, `strat x ≥ 2`: if `x` is next to a plane of the grid
  `g = M ℓ^{strat x − 1}` on at most ONE axis, then ONE class cube contains every `CurlReads` of the `ddA` stencils at `x`
  (clause 3 of `PerCubeRegular2` applies at `x`, in every direction).
* **`unc_two_near`** : contrapositive.  A site of stratum `≥ 2` whose `ddA` stencil lies in no class cube is next to grid
  planes on TWO distinct axes.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2DLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.M2Coverage (Near1 near1_self near1_shift near1_back near1_shift_shift near1_shift_back
  near1_back_shift_shift back_apply val_succ cube_index_ge)
open AdalyFormal.M1 (strat strat_le strat_eq_iff)

variable {L : PeriodicLatticeExtent}

/-- the coordinate `t` is next to a plane of the grid `g` -/
def NP (g t : ℕ) : Prop := t % g = 0 ∨ t % g = g - 1

/-! ## 1. one coordinate -/

theorem dform {N z t : ℕ} (hz : z < N) (ht : t < N) :
    (t + N - z) % N = if z ≤ t then t - z else t + N - z := by
  split_ifs with h
  · rw [show t + N - z = (t - z) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

theorem sform {N t : ℕ} (ht : t < N) : (t + 1) % N = if t + 1 < N then t + 1 else 0 := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [show t + 1 = N by omega, Nat.mod_self]

theorem dsucc {N z t : ℕ} (hz : z < N) (ht : t < N) :
    ((t + 1) % N + N - z) % N = ((t + N - z) % N + 1) % N := by
  have hv : (t + N - z) % N < N := Nat.mod_lt _ (by omega)
  rw [sform hv, dform hz ht, sform ht]
  by_cases h1 : t + 1 < N
  · rw [if_pos h1, dform hz h1]
    split_ifs <;> omega
  · rw [if_neg h1, dform hz (show 0 < N by omega)]
    split_ifs <;> omega

theorem d_mod_g {N z t g : ℕ} (hz : z ≤ N) (hgN : g ∣ N) (hgz : g ∣ z) : (t + N - z) % N % g = t % g := by
  rw [Nat.mod_mod_of_dvd _ hgN]
  obtain ⟨c, hc⟩ := Nat.dvd_sub hgN hgz
  rw [show t + N - z = t + (N - z) by omega, hc, Nat.add_mul_mod_self_left]

theorem succ_lt {d T g : ℕ} (hd : d < T) (hgT : g ∣ T) (hg : 2 ≤ g) (hr : d % g ≠ g - 1) : d + 1 < T := by
  by_contra h
  have hT : T = d + 1 := by omega
  have h0 : (d + 1) % g = 0 := by rw [← hT]; exact Nat.mod_eq_zero_of_dvd hgT
  have hlt := Nat.mod_lt d (by omega : 0 < g)
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < g by omega)] at h0
  by_cases h' : d % g + 1 < g
  · rw [Nat.mod_eq_of_lt h'] at h0; omega
  · omega

theorem box1_succ {N z t g T : ℕ} (hz : z < N) (ht : t < N) (hgN : g ∣ N) (hgz : g ∣ z) (hgT : g ∣ T)
    (hg : 2 ≤ g) (hin : (t + N - z) % N < T) (hr : t % g ≠ g - 1) : ((t + 1) % N + N - z) % N < T := by
  rw [dsucc hz ht]
  by_cases hTN : N ≤ T
  · exact lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hTN
  have hr' : (t + N - z) % N % g ≠ g - 1 := by rw [d_mod_g hz.le hgN hgz]; exact hr
  have h := succ_lt hin hgT hg hr'
  rw [Nat.mod_eq_of_lt (by omega)]; exact h

theorem box1_pred {N z s t g T : ℕ} (hz : z < N) (hs : s < N) (hst : (s + 1) % N = t) (hgN : g ∣ N) (hgz : g ∣ z)
    (hin : (t + N - z) % N < T) (hr : t % g ≠ 0) : (s + N - z) % N < T := by
  by_cases hTN : N ≤ T
  · exact lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hTN
  have e := dsucc hz hs
  rw [hst] at e
  have hne : (t + N - z) % N ≠ 0 := by
    intro h0; apply hr; rw [← d_mod_g hz.le hgN hgz (t := t), h0, Nat.zero_mod]
  have hv : (s + N - z) % N < N := Nat.mod_lt _ (by omega)
  rw [sform hv] at e
  split_ifs at e with hlt <;> omega

/-! ## 2. the one-step neighbourhood in a box -/

theorem near1_in_box {g T : ℕ} {z x : PeriodicLatticeSite L} (hgN : ∀ σ, g ∣ L σ + 1) (hgz : ∀ σ, g ∣ (z σ).val)
    (hgT : g ∣ T) (hg : 2 ≤ g) (hx : x ∈ siteBox z T)
    (hsu : ∀ σ, (x σ).val % g = g - 1 → periodicLatticeShift x σ ∈ siteBox z T)
    (hpr : ∀ σ, (x σ).val % g = 0 → periodicLatticeShiftBack x σ ∈ siteBox z T) :
    ∀ w, Near1 x w → w ∈ siteBox z T := by
  intro w hw σ
  show ((w σ).val + (L σ + 1) - (z σ).val) % (L σ + 1) < T
  have hxσ : ((x σ).val + (L σ + 1) - (z σ).val) % (L σ + 1) < T := hx σ
  rcases hw σ with h | h | h
  · rw [h]; exact hxσ
  · rw [h, val_succ]
    by_cases hr : (x σ).val % g = g - 1
    · have h2 : ((periodicLatticeShift x σ σ).val + (L σ + 1) - (z σ).val) % (L σ + 1) < T := hsu σ hr σ
      rw [AdalyFormal.M2Coverage.shift_apply, if_pos rfl, val_succ] at h2
      exact h2
    · exact box1_succ (z σ).isLt (x σ).isLt (hgN σ) (hgz σ) hgT hg hxσ hr
  · rw [h]
    have hst : ((x σ - 1).val + 1) % (L σ + 1) = (x σ).val := by rw [← val_succ, sub_add_cancel]
    by_cases hr : (x σ).val % g = 0
    · have h2 : ((periodicLatticeShiftBack x σ σ).val + (L σ + 1) - (z σ).val) % (L σ + 1) < T := hpr σ hr σ
      rw [back_apply, if_pos rfl] at h2
      exact h2
    · exact box1_pred (z σ).isLt (x σ - 1).isLt hst (hgN σ) (hgz σ) hxσ hr

/-- the `CurlReads` of the `ddA` stencils at `x`, from the one-step neighbourhood (as in CovF `near_clause3`). -/
theorem curlreads_of_near1 (sites : Set (PeriodicLatticeSite L)) (x : PeriodicLatticeSite L)
    (m : ∀ w, Near1 x w → w ∈ sites) :
    ∀ μ ν : Fin 3, ν ≠ μ → CurlReads sites (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads sites x ν μ := by
  intro μ ν hνμ
  have hμν : μ ≠ ν := fun h => hνμ h.symm
  have e1 : periodicLatticeShift (periodicLatticeShiftBack x ν) ν = x := periodicLatticeShift_shiftBack x ν
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  · show periodicLatticeShift (periodicLatticeShiftBack x ν) ν ∈ _; rw [e1]; exact m _ (near1_self x)
  · show periodicLatticeShift (periodicLatticeShift (periodicLatticeShiftBack x ν) ν) μ ∈ _
    rw [e1]; exact m _ (near1_shift x μ)
  · exact m _ (near1_back x ν)
  · exact m _ (near1_shift_back x hμν)
  · exact m _ (near1_shift_back x hμν)
  · exact m _ (near1_back_shift_shift x hμν)
  · exact m _ (near1_back x ν)
  · show periodicLatticeShift (periodicLatticeShiftBack x ν) ν ∈ _; rw [e1]; exact m _ (near1_self x)
  · exact m _ (near1_shift x ν)
  · exact m _ (near1_shift_shift x hμν)
  · exact m _ (near1_self x)
  · exact m _ (near1_shift x μ)
  · exact m _ (near1_shift x μ)
  · exact m _ (near1_shift_shift x (fun h => hμν h.symm))
  · exact m _ (near1_self x)
  · exact m _ (near1_shift x ν)

/-! ## 3. plaquettes and cubes -/

theorem plaq_of (y : PeriodicLatticeSite L) (a b : Fin 3) (hab : a ≠ b) :
    ∃ p : PeriodicLatticePlaquette L, ((y, a) : Bond L) ∈ periodicPlaquetteBoundaryEdges p ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, e = (y, a) ∨ e = (periodicLatticeShift y a, b) ∨
        e = (periodicLatticeShift y b, a) ∨ e = (y, b) := by
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨(y, (⟨(a, b), h⟩ : PeriodicPlaquetteDirections)), ?_, fun e he => ?_⟩
    · simp [periodicPlaquetteBoundaryEdges]
    · simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr h1))
  · refine ⟨(y, (⟨(b, a), h⟩ : PeriodicPlaquetteDirections)), ?_, fun e he => ?_⟩
    · simp [periodicPlaquetteBoundaryEdges]
    · simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with h1 | h1 | h1 | h1
      · exact Or.inr (Or.inr (Or.inr h1))
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inl h1)
      · exact Or.inl h1

/-- the sites within distance 3 of a stratum-`≥ 2` site lie in `Ω₀` -/
theorem near_om0 {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 1 ≤ ell) (hRM : 3 ≤ R * M)
    {x : PeriodicLatticeSite L} (hs : 2 ≤ strat S k x) {w : PeriodicLatticeSite L} (hw : pdist x w ≤ 3) :
    w ∈ S.Om 0 :=
  AdalyFormal.M1DStrat.mem_om0_of_strat hS
    (by have := AdalyFormal.M1DStrat.strat_le_near hS hell (hw.trans hRM); omega)

/-- a class cube containing a stratum-`s` site is a grid box whose grid is a multiple of `M ℓ^{s-1}` -/
theorem cube_box {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hq : IsClassCube ell M 12 k S sites i)
    {x : PeriodicLatticeSite L} (hx : x ∈ sites) (hx0 : x ∈ S.Om 0) :
    ∃ z : PeriodicLatticeSite L, sites = siteBox z (12 * bigSide M ell i) ∧
      (∀ σ, bigSide M ell (strat S k x - 1) ∣ (z σ).val) ∧
      bigSide M ell (strat S k x - 1) ∣ 12 * bigSide M ell i := by
  obtain ⟨-, ⟨z, hgrid, hzs⟩, -, -⟩ := hq.1
  have hj : x ∈ towerBj S (strat S k x) := (strat_eq_iff hS (strat_le S k x) x).2 ⟨hx0, rfl⟩
  have hle : strat S k x ≤ i + 1 := cube_index_ge hS hq hx hj
  have hdv : bigSide M ell (strat S k x - 1) ∣ bigSide M ell i := by
    unfold bigSide; exact Nat.mul_dvd_mul_left M (Nat.pow_dvd_pow ell (by omega))
  refine ⟨z, hzs, fun σ => hdv.trans (Nat.dvd_of_mod_eq_zero (hgrid σ)), hdv.trans (Dvd.intro_left _ rfl)⟩

/-! ## 4. the stencil lies in one class cube unless two coordinates are next to grid planes -/

theorem pd_bs {x : PeriodicLatticeSite L} (ν ρ : Fin 3) :
    pdist x (periodicLatticeShift (periodicLatticeShiftBack x ν) ρ) ≤ 2 :=
  AdalyFormal.M1DStrat.pd_sh (AdalyFormal.M1DStrat.pd_bk (AdalyFormal.M1DStrat.pd0 x) ν) ρ

theorem stencil_box {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 1 ≤ M)
    (hRM : 3 ≤ R * M) (hcov : CoversOm0p ell M 12 k S) (x : PeriodicLatticeSite L) (hs : 2 ≤ strat S k x)
    (ν₀ : Fin 3) (hfar : ∀ σ, σ ≠ ν₀ → ¬ NP (bigSide M ell (strat S k x - 1)) (x σ).val) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M 12 k S sites i ∧
      ∀ w, Near1 x w → w ∈ sites := by
  set g := bigSide M ell (strat S k x - 1) with hgdef
  have hell1 : 1 ≤ ell := by omega
  have hg2 : 2 ≤ g := by
    rw [hgdef]; unfold bigSide
    have h1 : ell ^ 1 ≤ ell ^ (strat S k x - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_one] at h1
    nlinarith
  have hgN : ∀ σ, g ∣ L σ + 1 := fun σ => hS.2.2.1 _ (by have := strat_le S k x; omega) σ
  have hx0 : x ∈ S.Om 0 := AdalyFormal.M1DStrat.mem_om0_of_strat hS (by omega)
  have nom : ∀ w, pdist x w ≤ 3 → w ∈ S.Om 0 := fun w hw => near_om0 hS hell1 hRM hs hw
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin 3, ν₀ ≠ ρ := ⟨ν₀ + 1, by fin_cases ν₀ <;> decide⟩
  have p0 := AdalyFormal.M1DStrat.pd0 x
  -- the generic finish
  have fin : ∀ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M 12 k S sites i → x ∈ sites →
      (∀ σ, (x σ).val % g = g - 1 → periodicLatticeShift x σ ∈ sites) →
      (∀ σ, (x σ).val % g = 0 → periodicLatticeShiftBack x σ ∈ sites) →
      ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M 12 k S sites i ∧
        ∀ w, Near1 x w → w ∈ sites := by
    intro sites i hq hxs hsu hpr
    obtain ⟨z, hzs, hgz, hgT⟩ := cube_box hS hq hxs hx0
    subst hzs
    exact ⟨_, i, hq, near1_in_box hgN hgz hgT hg2 hxs hsu hpr⟩
  by_cases h0 : (x ν₀).val % g = 0
  · obtain ⟨p, hmem, hed⟩ := plaq_of (periodicLatticeShiftBack x ν₀) ν₀ ρ hρ
    have hpin : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e := by
      intro e he
      have b1 := AdalyFormal.M1DStrat.pd_bk p0 ν₀
      rcases hed e he with rfl | rfl | rfl | rfl
      · exact ⟨nom _ (b1.trans (by norm_num)), nom _ ((AdalyFormal.M1DStrat.pd_sh b1 ν₀).trans (by norm_num))⟩
      · exact ⟨nom _ ((AdalyFormal.M1DStrat.pd_sh b1 ν₀).trans (by norm_num)),
          nom _ ((AdalyFormal.M1DStrat.pd_sh (AdalyFormal.M1DStrat.pd_sh b1 ν₀) ρ).trans (by norm_num))⟩
      · exact ⟨nom _ ((AdalyFormal.M1DStrat.pd_sh b1 ρ).trans (by norm_num)),
          nom _ ((AdalyFormal.M1DStrat.pd_sh (AdalyFormal.M1DStrat.pd_sh b1 ρ) ν₀).trans (by norm_num))⟩
      · exact ⟨nom _ (b1.trans (by norm_num)), nom _ ((AdalyFormal.M1DStrat.pd_sh b1 ρ).trans (by norm_num))⟩
    obtain ⟨sites, i, hq, hcb⟩ := hcov.2 p hpin
    have hb := hcb _ hmem
    have hxs : x ∈ sites := by have := hb.2; rwa [periodicLatticeShift_shiftBack] at this
    refine fin sites i hq hxs (fun σ hσ => ?_) (fun σ hσ => ?_)
    · by_cases hσ0 : σ = ν₀
      · subst hσ0; omega
      · exact absurd (Or.inr hσ) (hfar σ hσ0)
    · by_cases hσ0 : σ = ν₀
      · subst hσ0; exact hb.1
      · exact absurd (Or.inl hσ) (hfar σ hσ0)
  by_cases h1 : (x ν₀).val % g = g - 1
  · obtain ⟨p, hmem, hed⟩ := plaq_of x ν₀ ρ hρ
    have hpin : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e := by
      intro e he
      rcases hed e he with rfl | rfl | rfl | rfl
      · exact ⟨nom _ (p0.trans (by norm_num)), nom _ ((AdalyFormal.M1DStrat.pd_sh p0 ν₀).trans (by norm_num))⟩
      · exact ⟨nom _ ((AdalyFormal.M1DStrat.pd_sh p0 ν₀).trans (by norm_num)),
          nom _ ((AdalyFormal.M1DStrat.pd_sh (AdalyFormal.M1DStrat.pd_sh p0 ν₀) ρ).trans (by norm_num))⟩
      · exact ⟨nom _ ((AdalyFormal.M1DStrat.pd_sh p0 ρ).trans (by norm_num)),
          nom _ ((AdalyFormal.M1DStrat.pd_sh (AdalyFormal.M1DStrat.pd_sh p0 ρ) ν₀).trans (by norm_num))⟩
      · exact ⟨nom _ (p0.trans (by norm_num)), nom _ ((AdalyFormal.M1DStrat.pd_sh p0 ρ).trans (by norm_num))⟩
    obtain ⟨sites, i, hq, hcb⟩ := hcov.2 p hpin
    have hb := hcb _ hmem
    refine fin sites i hq hb.1 (fun σ hσ => ?_) (fun σ hσ => ?_)
    · by_cases hσ0 : σ = ν₀
      · subst hσ0; exact hb.2
      · exact absurd (Or.inr hσ) (hfar σ hσ0)
    · by_cases hσ0 : σ = ν₀
      · subst hσ0; exact absurd hσ h0
      · exact absurd (Or.inl hσ) (hfar σ hσ0)
  · obtain ⟨sites, i, hq, hxs⟩ := hcov.1 x hx0
    refine fin sites i hq hxs (fun σ hσ => ?_) (fun σ hσ => ?_)
    · by_cases hσ0 : σ = ν₀
      · subst hσ0; exact absurd hσ h1
      · exact absurd (Or.inr hσ) (hfar σ hσ0)
    · by_cases hσ0 : σ = ν₀
      · subst hσ0; exact absurd hσ h0
      · exact absurd (Or.inl hσ) (hfar σ hσ0)

/-- the `ddA` stencils at `x` (every direction) lie in one class cube -/
def StencilCovered {L : PeriodicLatticeExtent} (ell M k : ℕ) (S : Tower L) (x : PeriodicLatticeSite L) : Prop :=
  ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M 12 k S sites i ∧
    ∀ μ ν : Fin 3, ν ≠ μ → CurlReads sites (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads sites x ν μ

theorem stencil_cov {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 1 ≤ M)
    (hRM : 3 ≤ R * M) (hcov : CoversOm0p ell M 12 k S) (x : PeriodicLatticeSite L) (hs : 2 ≤ strat S k x)
    (ν₀ : Fin 3) (hfar : ∀ σ, σ ≠ ν₀ → ¬ NP (bigSide M ell (strat S k x - 1)) (x σ).val) :
    StencilCovered ell M k S x := by
  obtain ⟨sites, i, hq, hm⟩ := stencil_box hS hell hM hRM hcov x hs ν₀ hfar
  exact ⟨sites, i, hq, curlreads_of_near1 sites x hm⟩

/-- **uncovered stencils sit next to grid planes on two axes** -/
theorem unc_two_near {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hM : 1 ≤ M)
    (hRM : 3 ≤ R * M) (hcov : CoversOm0p ell M 12 k S) (x : PeriodicLatticeSite L) (hs : 2 ≤ strat S k x)
    (hunc : ¬ StencilCovered ell M k S x) :
    ∃ a b : Fin 3, a ≠ b ∧ NP (bigSide M ell (strat S k x - 1)) (x a).val ∧
      NP (bigSide M ell (strat S k x - 1)) (x b).val := by
  by_contra hcon
  push Not at hcon
  apply hunc
  by_cases hex : ∃ a : Fin 3, NP (bigSide M ell (strat S k x - 1)) (x a).val
  · obtain ⟨a, ha⟩ := hex
    exact stencil_cov hS hell hM hRM hcov x hs a (fun σ hσ hn => hcon a σ (fun h => hσ h.symm) ha hn)
  · push Not at hex
    exact stencil_cov hS hell hM hRM hcov x hs 0 (fun σ _ => hex σ)

#print axioms NP
#print axioms dform
#print axioms sform
#print axioms dsucc
#print axioms d_mod_g
#print axioms succ_lt
#print axioms box1_succ
#print axioms box1_pred
#print axioms near1_in_box
#print axioms curlreads_of_near1
#print axioms plaq_of
#print axioms near_om0
#print axioms cube_box
#print axioms pd_bs
#print axioms stencil_box
#print axioms StencilCovered
#print axioms stencil_cov
#print axioms unc_two_near

end AdalyFormal.M2DLayer
