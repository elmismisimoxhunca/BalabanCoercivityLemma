import MR5

/-!
# MR6 -- a corner where no class cube reaches: `CoversOm0p 12` does not give single-cube neighbourhoods
(m2_route, 2026-10-14)

Tower `VT` on a torus of side 52 (`ell = 2`, `M = 2`, `k = 1`, `R = 18`; `Lu + 1 = 26`): `Ω₀` = everything,
`Ω₁` = everything except six level-1 big blocks ("clumps", side 4), at big-block coordinates
`(6,0,0), (7,0,0), (0,6,0), (0,7,0), (0,0,6), (0,0,7)`; `Ω₂ = ∅`.
* `vt_admissible`, `vt_torusOK` : `Admissible 2 2 18 1 VT`, `TorusOK 2 2 Lu`.
* `vt_plaq_cover` / `vt_coversp` : every plaquette (hence every site) lies in one class cube: `CoversOm0p 2 2 12 1 VT`
  (sites AND plaquettes, the headline's coverage hypothesis).
* **`vt_star_no_cube`** : the site `x₀ = (1,1,1)` and its three forward neighbours `x₀ + e_σ` lie in NO common class cube.
* `vt_stencil_no_cube` : hence at `x₀`, for every direction `μ`, the premise of clause 3 of `PerCubeRegular2`
  (all `CurlReads` of the `ddA` stencil inside one cube) fails for every class cube: the printed class, as frozen in
  r8, imposes no `ddA` bound at `x₀`.
Consequences (facts about what the class supplies, for the consumers listed in NOTES): no class cube contains the ℓ¹ ball
`Ball x₀ 1`; class cubes therefore cannot be IMS patches with a margin, and any per-cube consumer that needs a 3D
neighbourhood of a site inside ONE cube (D-layer stencils, 4ℓ-balls, block cones, patch balls) is not served at `x₀`.
No sorry / axiom / native_decide.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2Route

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M2Bridge (cube_isClass)

/-! ## the tower -/

def clumpQ (a b c : ℕ) : Prop :=
  ((a = 6 ∨ a = 7) ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ (b = 6 ∨ b = 7) ∧ c = 0) ∨ (a = 0 ∧ b = 0 ∧ (c = 6 ∨ c = 7))

def VClump {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) : Prop :=
  clumpQ ((x 0).val / 4) ((x 1).val / 4) ((x 2).val / 4)

def VT (L : PeriodicLatticeExtent) : Tower L :=
  ⟨fun j => if j = 0 then Set.univ else if j = 1 then {x | ¬ VClump x} else ∅⟩

theorem vt_om0 {L : PeriodicLatticeExtent} : (VT L).Om 0 = Set.univ := by simp [VT]
theorem vt_om1 {L : PeriodicLatticeExtent} : (VT L).Om 1 = {x | ¬ VClump x} := by simp [VT]
theorem vt_omj {L : PeriodicLatticeExtent} {j : ℕ} (hj : 2 ≤ j) : (VT L).Om j = ∅ := by
  simp only [VT]; rw [if_neg (by omega), if_neg (by omega)]

section
variable {L : PeriodicLatticeExtent} (hL : ∀ μ, L μ + 1 = 52)
include hL

/-- the site with coordinates `f`. -/
def mkS (f : Fin 3 → ℕ) (hf : ∀ σ, f σ < 52) : PeriodicLatticeSite L :=
  fun σ => ⟨f σ, by have := hL σ; have := hf σ; omega⟩

theorem mkS_val (f : Fin 3 → ℕ) (hf : ∀ σ, f σ < 52) (σ : Fin 3) : ((mkS hL f hf) σ).val = f σ := rfl

theorem vt_admissible : Admissible 2 2 18 1 (VT L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this; rw [vt_om0]; trivial
    · rw [vt_omj (by omega)] at hx; exact hx.elim
  · intro j hj; exact vt_omj (by omega)
  · intro j hj μ
    rw [hL μ]
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this; unfold bigSide; norm_num
    · have : j = 1 := by omega
      subst this; unfold bigSide; norm_num
  · intro j hj
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this; rw [vt_om0]; intro x _ y _; trivial
    · have : j = 1 := by omega
      subst this; rw [vt_om1]
      intro x hx y hy
      have e : bigSide 2 2 1 = 4 := by unfold bigSide; norm_num
      rw [e] at hy
      simp only [Set.mem_setOf_eq, VClump] at hx ⊢
      rw [hy 0, hy 1, hy 2]; exact hx
  · intro j hj x hx y hy
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this; rw [vt_om0] at hx; exact (hx trivial).elim
    · rw [vt_omj (by omega)] at hy; exact hy.elim
  · intro x
    rw [vt_om0]
    simp only [Set.mem_univ, true_iff]
    have h20 : (20 : ℕ) < L 0 + 1 := by rw [hL 0]; norm_num
    refine ⟨Function.update x 0 ⟨20, h20⟩, ?_, x, fun _ => rfl, ?_⟩
    · rw [vt_om1]
      simp only [Set.mem_setOf_eq, VClump, clumpQ, Function.update_self]
      omega
    · unfold pdist
      rw [Fin.sum_univ_three]
      simp only [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
        Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
      have h1 : pcd (L 1 + 1) (x 1).val (x 1).val = 0 := by unfold pcd; simp
      have h2 : pcd (L 2 + 1) (x 2).val (x 2).val = 0 := by unfold pcd; simp
      have h0 : pcd (L 0 + 1) (x 0).val 20 ≤ 26 := by
        have hx := (x 0).isLt; have hL0 := hL 0; unfold pcd; split_ifs <;> omega
      omega

/-! ## boxes on the 52-torus -/

/-- `v` lies in the cyclic window `[z, z + s)` of `ℤ/52`. -/
def inI (z s v : ℕ) : Prop := (v + 52 - z) % 52 < s

theorem mem_box_iff (z : PeriodicLatticeSite L) (s : ℕ) (x : PeriodicLatticeSite L) :
    x ∈ siteBox z s ↔ ∀ σ, inI (z σ).val s (x σ).val := by
  simp only [siteBox, Set.mem_setOf_eq, inI, hL]

theorem shift_val (x : PeriodicLatticeSite L) (μ σ : Fin 3) :
    (periodicLatticeShift x μ σ).val = if σ = μ then ((x σ).val + 1) % 52 else (x σ).val := by
  unfold periodicLatticeShift
  by_cases h : σ = μ
  · subst h
    rw [Function.update_self, if_pos rfl, Fin.val_add_one]
    have hl := (x σ).isLt
    have hL' := hL σ
    split_ifs with h1
    · rw [h1, Fin.val_last]; omega
    · have : (x σ).val ≠ L σ := fun h2 => h1 (Fin.ext (by rw [h2, Fin.val_last]))
      omega
  · rw [Function.update_of_ne h, if_neg h]

/-- the four corners of the plaquette `(x; μ, ν)` lie in a box when each axis window contains the coordinates. -/
theorem corners_in_box (z : PeriodicLatticeSite L) (s : ℕ) (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hμν : μ ≠ ν)
    (h : ∀ σ, inI (z σ).val s (x σ).val ∧ ((σ = μ ∨ σ = ν) → inI (z σ).val s (((x σ).val + 1) % 52))) :
    x ∈ siteBox z s ∧ periodicLatticeShift x μ ∈ siteBox z s ∧ periodicLatticeShift x ν ∈ siteBox z s ∧
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ siteBox z s := by
  simp only [mem_box_iff hL, shift_val hL]
  refine ⟨fun σ => (h σ).1, fun σ => ?_, fun σ => ?_, fun σ => ?_⟩
  · split_ifs with h1
    · exact (h σ).2 (Or.inl h1)
    · exact (h σ).1
  · split_ifs with h1
    · exact (h σ).2 (Or.inr h1)
    · exact (h σ).1
  · by_cases h1 : σ = ν
    · have h2 : σ ≠ μ := fun h2 => hμν (h2.symm.trans h1)
      rw [if_pos h1, if_neg h2]; exact (h σ).2 (Or.inr h1)
    · rw [if_neg h1]
      split_ifs with h2
      · exact (h σ).2 (Or.inl h2)
      · exact (h σ).1

end

/-! ## arithmetic on the 52-circle -/

theorem in48 (W v : ℕ) (hW : W < 13) (hv : v < 52) : inI (4 * ((W + 1) % 13)) 48 v ↔ v / 4 ≠ W := by
  unfold inI; omega

theorem in48' (z v : ℕ) (hz : z < 52) (hz4 : z % 4 = 0) (hv : v < 52) : inI z 48 v ↔ v / 4 ≠ (z / 4 + 12) % 13 := by
  unfold inI; omega

/-- the `γ`-window of an index-0 box and the clump coordinate it reaches. -/
def zsel (t : ℕ) : ℕ :=
  if t ≤ 1 then 30 else if t ≤ 3 then 2 else if t ≤ 26 then 4 else if t = 27 then 6 else if t ≤ 50 then 28 else 30

def cv (t : ℕ) : ℕ := if 2 ≤ t ∧ t ≤ 27 then 24 else 30

theorem zsel_table (t : ℕ) (ht : t < 52) :
    inI (zsel t) 24 t ∧ inI (zsel t) 24 (cv t) ∧ (t ≠ 1 → inI (zsel t) 24 ((t + 1) % 52)) := by
  unfold inI zsel cv; split_ifs <;> omega

theorem zsel_lt (t : ℕ) : zsel t < 52 ∧ zsel t % 2 = 0 := by unfold zsel; split_ifs <;> omega

theorem cv_col (t : ℕ) : cv t < 52 ∧ (cv t / 4 = 6 ∨ cv t / 4 = 7) := by unfold cv; split_ifs <;> omega

def inR (v : ℕ) : Prop := 48 ≤ v ∨ v ≤ 19

theorem in24_48 (v : ℕ) (hv : v < 52) (h : inR v) : inI 48 24 v := by unfold inI; unfold inR at h; omega

theorem two_nonzero (q : Fin 3 → ℕ) (α β : Fin 3) (hab : α ≠ β) (hα : q α ≠ 0) (hβ : q β ≠ 0) :
    ¬ clumpQ (q 0) (q 1) (q 2) := by
  intro hc
  unfold clumpQ at hc
  fin_cases α <;> fin_cases β <;> simp at hab hα hβ <;> omega

/-- the third axis. -/
theorem third_axis (μ ν : Fin 3) : ∃ l : Fin 3, l ≠ μ ∧ l ≠ ν := by
  revert μ ν; decide

theorem axes_cover {μ ν l σ : Fin 3} (hμν : μ ≠ ν) (hl1 : l ≠ μ) (hl2 : l ≠ ν) (hσ : σ ≠ l) : σ = μ ∨ σ = ν := by
  revert μ ν l σ; decide

section cover
variable {L : PeriodicLatticeExtent} (hL : ∀ μ, L μ + 1 = 52)
include hL

theorem side0 : 12 * bigSide 2 2 0 = 24 := by norm_num [bigSide]
theorem side1 : 12 * bigSide 2 2 1 = 48 := by norm_num [bigSide]

theorem vt_tb0 {c : PeriodicLatticeSite L} (hc : VClump c) : c ∈ towerBj (VT L) 0 := by
  refine ⟨by rw [vt_om0]; trivial, ?_⟩
  rw [vt_om1]; exact fun h => h hc

theorem vt_tb1 {y : PeriodicLatticeSite L} (hy : y ∈ (VT L).Om 1) : y ∈ towerBj (VT L) 1 :=
  ⟨hy, by rw [vt_omj (by norm_num)]; exact fun h => h⟩

/-- an index-1 class cube from excluded columns `W` (two of them `0`). -/
theorem idx1_cover (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hμν : μ ≠ ν) (W : Fin 3 → ℕ) (hW : ∀ σ, W σ < 13)
    (h2 : ∃ α β : Fin 3, α ≠ β ∧ W α = 0 ∧ W β = 0)
    (hav : ∀ σ, (x σ).val / 4 ≠ W σ ∧ ((σ = μ ∨ σ = ν) → (((x σ).val + 1) % 52) / 4 ≠ W σ)) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube 2 2 12 1 (VT L) sites j ∧
      x ∈ sites ∧ periodicLatticeShift x μ ∈ sites ∧ periodicLatticeShift x ν ∈ sites ∧
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ sites := by
  have hz : ∀ σ, 4 * ((W σ + 1) % 13) < 52 := fun σ => by have := hW σ; omega
  set z : PeriodicLatticeSite L := mkS hL (fun σ => 4 * ((W σ + 1) % 13)) hz with hzdef
  have hbox : ∀ y : PeriodicLatticeSite L, y ∈ siteBox z 48 ↔ ∀ σ, (y σ).val / 4 ≠ W σ := by
    intro y
    rw [mem_box_iff hL]
    refine forall_congr' (fun σ => ?_)
    rw [mkS_val]
    exact in48 _ _ (hW σ) (by have := (y σ).isLt; have := hL σ; omega)
  have hsub : siteBox z (12 * bigSide 2 2 1) ⊆ (VT L).Om 1 := by
    rw [side1 hL]
    intro y hy
    rw [vt_om1]
    obtain ⟨α, β, hab, ha, hb⟩ := h2
    have hy' := (hbox y).1 hy
    have hA := hy' α
    have hB := hy' β
    rw [ha] at hA; rw [hb] at hB
    exact two_nonzero (fun σ => (y σ).val / 4) α β hab hA hB
  have hc := corners_in_box hL z 48 x hμν (fun σ => by
    rw [mkS_val]
    have hx := (x σ).isLt
    have hL' := hL σ
    refine ⟨(in48 _ _ (hW σ) (by omega)).2 (hav σ).1, fun h => (in48 _ _ (hW σ) (by omega)).2 ((hav σ).2 h)⟩)
  rw [← side1 hL] at hc
  have hgrid : GridCorner (bigSide 2 2 1) z := by
    intro σ
    show (4 * ((W σ + 1) % 13)) % bigSide 2 2 1 = 0
    norm_num [bigSide]
  refine ⟨siteBox z (12 * bigSide 2 2 1), 1, ?_, hc⟩
  exact cube_isClass (vt_admissible hL) (le_refl 1) hgrid hsub hc.1 (vt_tb1 hL (hsub hc.1)) (by norm_num)

/-- an index-0 class cube with a clump along axis `γ`. -/
theorem idx0_cover (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hμν : μ ≠ ν) (γ : Fin 3)
    (hγ : (γ = μ ∨ γ = ν) → (x γ).val ≠ 1)
    (hR : ∀ σ, σ ≠ γ → inR (x σ).val ∧ ((σ = μ ∨ σ = ν) → inR (((x σ).val + 1) % 52))) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube 2 2 12 1 (VT L) sites j ∧
      x ∈ sites ∧ periodicLatticeShift x μ ∈ sites ∧ periodicLatticeShift x ν ∈ sites ∧
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ sites := by
  classical
  set t : ℕ := (x γ).val with ht
  have htl : t < 52 := by have := (x γ).isLt; have := hL γ; omega
  have hz : ∀ σ, (if σ = γ then zsel t else 48) < 52 := fun σ => by
    split_ifs
    · exact (zsel_lt t).1
    · norm_num
  have hcv : ∀ σ, (if σ = γ then cv t else 0) < 52 := fun σ => by
    split_ifs
    · exact (cv_col t).1
    · norm_num
  set z : PeriodicLatticeSite L := mkS hL (fun σ => if σ = γ then zsel t else 48) hz with hzdef
  set c : PeriodicLatticeSite L := mkS hL (fun σ => if σ = γ then cv t else 0) hcv with hcdef
  have hc := corners_in_box hL z 24 x hμν (fun σ => by
    rw [mkS_val]
    have hx := (x σ).isLt
    have hL' := hL σ
    by_cases hσ : σ = γ
    · subst hσ
      rw [if_pos rfl]
      obtain ⟨t1, -, t3⟩ := zsel_table t htl
      exact ⟨t1, fun h => t3 (hγ h)⟩
    · rw [if_neg hσ]
      obtain ⟨r1, r2⟩ := hR σ hσ
      exact ⟨in24_48 _ (by omega) r1, fun h => in24_48 _ (by omega) (r2 h)⟩)
  rw [← side0 hL] at hc
  have hcbox : c ∈ siteBox z (12 * bigSide 2 2 0) := by
    rw [side0 hL, mem_box_iff hL]
    intro σ
    rw [mkS_val, mkS_val]
    by_cases hσ : σ = γ
    · rw [if_pos hσ, if_pos hσ]; exact (zsel_table t htl).2.1
    · rw [if_neg hσ, if_neg hσ]; unfold inI; norm_num
  have hcl : VClump c := by
    show clumpQ ((c 0).val / 4) ((c 1).val / 4) ((c 2).val / 4)
    rw [hcdef, mkS_val, mkS_val, mkS_val]
    have h := (cv_col t).2
    unfold clumpQ
    fin_cases γ <;> simp <;> omega
  have hgrid : GridCorner (bigSide 2 2 0) z := by
    intro σ
    show (if σ = γ then zsel t else 48) % bigSide 2 2 0 = 0
    have e : bigSide 2 2 0 = 2 := by norm_num [bigSide]
    rw [e]
    split_ifs
    · exact (zsel_lt t).2
    · norm_num
  have hsub : siteBox z (12 * bigSide 2 2 0) ⊆ (VT L).Om 0 := by rw [vt_om0]; exact Set.subset_univ _
  refine ⟨siteBox z (12 * bigSide 2 2 0), 0, ?_, hc⟩
  exact cube_isClass (vt_admissible hL) (Nat.zero_le 1) hgrid hsub hcbox (vt_tb0 hL hcl) (by norm_num)

/-- **every plaquette lies in one class cube** of `VT`. -/
theorem vt_plaq_cover (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hμν : μ ≠ ν) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube 2 2 12 1 (VT L) sites j ∧
      x ∈ sites ∧ periodicLatticeShift x μ ∈ sites ∧ periodicLatticeShift x ν ∈ sites ∧
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ sites := by
  classical
  set Z : Fin 3 → Prop := fun σ => (x σ).val / 4 = 0 ∨ ((σ = μ ∨ σ = ν) ∧ (((x σ).val + 1) % 52) / 4 = 0) with hZ
  have hxl : ∀ σ, (x σ).val < 52 := fun σ => by have := (x σ).isLt; have := hL σ; omega
  have hZR : ∀ σ, Z σ → inR (x σ).val ∧ inR (((x σ).val + 1) % 52) := by
    intro σ hσ
    have := hxl σ
    rcases hσ with h | ⟨-, h⟩ <;> unfold inR <;> omega
  by_cases hA : ∃ α β : Fin 3, α ≠ β ∧ ¬ Z α ∧ ¬ Z β
  · refine idx1_cover hL x hμν (fun σ => if Z σ then ((x σ).val / 4 + 6) % 13 else 0)
      (fun σ => by split_ifs <;> omega) ?_ (fun σ => ?_)
    · obtain ⟨α, β, hab, ha, hb⟩ := hA
      exact ⟨α, β, hab, by rw [if_neg ha], by rw [if_neg hb]⟩
    · have := hxl σ
      by_cases hσ : Z σ
      · rw [if_pos hσ]
        exact ⟨by omega, fun _ => by omega⟩
      · rw [if_neg hσ]
        simp only [hZ, not_or, not_and] at hσ
        exact ⟨hσ.1, fun h => hσ.2 h⟩
  · push_neg at hA
    obtain ⟨l, hl1, hl2⟩ := third_axis μ ν
    by_cases hRR : (inR (x μ).val ∧ inR (((x μ).val + 1) % 52)) ∧ (inR (x ν).val ∧ inR (((x ν).val + 1) % 52))
    · refine idx0_cover hL x hμν l (fun h => (h.elim (fun h' => absurd h' hl1) (fun h' => absurd h' hl2))) ?_
      intro σ hσ
      rcases axes_cover hμν hl1 hl2 hσ with h | h <;> subst h
      · exact ⟨hRR.1.1, fun _ => hRR.1.2⟩
      · exact ⟨hRR.2.1, fun _ => hRR.2.2⟩
    · -- an axis σ₀ ∈ {μ, ν} leaves the window: it does not touch column 0, the other two do
      have hex : ∃ σ₀ : Fin 3, (σ₀ = μ ∨ σ₀ = ν) ∧ ¬ (inR (x σ₀).val ∧ inR (((x σ₀).val + 1) % 52)) := by
        by_cases h1 : inR (x μ).val ∧ inR (((x μ).val + 1) % 52)
        · exact ⟨ν, Or.inr rfl, fun h2 => hRR ⟨h1, h2⟩⟩
        · exact ⟨μ, Or.inl rfl, h1⟩
      obtain ⟨σ₀, hσ₀, hout⟩ := hex
      have hnZ : ¬ Z σ₀ := fun h => hout (hZR σ₀ h)
      refine idx0_cover hL x hμν σ₀ (fun _ => ?_) (fun σ hσ => ?_)
      · intro h1
        apply hnZ
        left; omega
      · have hZσ : Z σ := by
          by_contra hn
          exact hA σ₀ σ (Ne.symm hσ) hnZ |> fun h => hn h
        exact ⟨(hZR σ hZσ).1, fun _ => (hZR σ hZσ).2⟩

/-- **`CoversOm0p 2 2 12 1 VT`** (sites and plaquettes). -/
theorem vt_coversp : CoversOm0p 2 2 12 1 (VT L) := by
  refine ⟨fun x _ => ?_, fun p _ => ?_⟩
  · obtain ⟨sites, j, hq, hx, -⟩ := vt_plaq_cover hL x (μ := 0) (ν := 1) (by decide)
    exact ⟨sites, j, hq, hx⟩
  · obtain ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩ := p
    obtain ⟨sites, j, hq, h1, h2, h3, h4⟩ := vt_plaq_cover hL x (μ := μ) (ν := ν) (ne_of_lt hμν)
    refine ⟨sites, j, hq, fun e he => ?_⟩
    simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨h1, h2⟩
    · exact ⟨h2, h4⟩
    · exact ⟨h3, by rw [shift_comm]; exact h4⟩
    · exact ⟨h1, h3⟩

theorem vt_torusOK {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 26) : TorusOK 2 2 Lu := by
  refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩ <;> rw [hLu μ] <;> norm_num

/-! ## the corner `x₀ = (1,1,1)` -/

/-- no class cube contains, for every axis `σ`, a site of coordinate `≤ 1` and a site of coordinate in `[2,3]` along `σ`,
all inside the big block `[0,3]³`. -/
theorem vt_no_cube_of (sites : Set (PeriodicLatticeSite L)) (i : ℕ) (hq : IsClassCube 2 2 12 1 (VT L) sites i)
    (P Q : Fin 3 → PeriodicLatticeSite L)
    (hP : ∀ σ, P σ ∈ sites ∧ ((P σ) σ).val ≤ 1) (hQ : ∀ σ, Q σ ∈ sites ∧ 2 ≤ ((Q σ) σ).val ∧ ((Q σ) σ).val ≤ 3) :
    False := by
  obtain ⟨⟨hik, ⟨z, hgrid, hz⟩, hsub, ⟨c, hcs, hcB⟩⟩, -⟩ := hq
  have hzl : ∀ σ, (z σ).val < 52 := fun σ => by have := (z σ).isLt; have := hL σ; omega
  have hmem : ∀ y, y ∈ sites → ∀ σ, inI (z σ).val (12 * bigSide 2 2 i) (y σ).val := by
    intro y hy
    rw [hz] at hy
    exact (mem_box_iff hL _ _ _).1 hy
  rcases Nat.lt_or_ge i 1 with h0 | h1
  · have hi : i = 0 := by omega
    subst hi
    rw [side0 hL] at hmem
    have hcl : VClump c := by
      have h := hcB.2
      exact Classical.byContradiction (fun hn => h (by rw [show (0 : ℕ) + 1 = 1 from rfl, vt_om1]; exact hn))
    have hg : ∀ σ, (z σ).val % 2 = 0 := fun σ => by
      have := hgrid σ; simpa [bigSide] using this
    have key : ∀ σ, (c σ).val / 4 = 6 ∨ (c σ).val / 4 = 7 → False := by
      intro σ hσ
      have a1 := hmem _ (hP σ).1 σ
      have a2 := hmem _ (hQ σ).1 σ
      have a3 := hmem _ hcs σ
      have p1 := (hP σ).2
      have q1 := (hQ σ).2
      have zl := hzl σ
      have zg := hg σ
      unfold inI at a1 a2 a3
      omega
    unfold VClump clumpQ at hcl
    rcases hcl with ⟨h, -, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩
    · exact key 0 h
    · exact key 1 h
    · exact key 2 h
  · have hi : i = 1 := by omega
    subst hi
    rw [side1 hL] at hmem
    have hg : ∀ σ, (z σ).val % 4 = 0 := fun σ => by
      have := hgrid σ; simpa [bigSide] using this
    have hW : ∀ σ, ((z σ).val / 4 + 12) % 13 ≠ 0 := by
      intro σ
      have a1 := (in48' _ _ (hzl σ) (hg σ) (by have := ((P σ) σ).isLt; have := hL σ; omega)).1 (hmem _ (hP σ).1 σ)
      have := (hP σ).2
      omega
    have hsub1 : ∀ y, y ∈ sites → ¬ VClump y := by
      intro y hy
      rcases hsub hy with h | h
      · have h1 := h.1; rw [vt_om1] at h1; exact h1
      · have h1 := h.1; rw [vt_omj (by norm_num)] at h1; exact h1.elim
    have hin : ∀ v : ℕ, (hv : v < 52) → v / 4 ≠ ((z 0).val / 4 + 12) % 13 →
        mkS hL (fun σ => if σ = 0 then v else 0) (fun σ => by split_ifs <;> omega) ∈ sites := by
      intro v hv hvW
      rw [hz, side1 hL, mem_box_iff hL]
      intro σ
      rw [mkS_val]
      rw [in48' _ _ (hzl σ) (hg σ) (by split_ifs <;> omega)]
      by_cases h : σ = 0
      · subst h; simpa using hvW
      · rw [if_neg h]; simpa using (hW σ).symm
    have hcl : ∀ v : ℕ, (hv : v < 52) → (v / 4 = 6 ∨ v / 4 = 7) →
        VClump (mkS hL (fun σ => if σ = 0 then v else 0) (fun σ => by split_ifs <;> omega)) := by
      intro v hv h
      unfold VClump clumpQ
      simp only [mkS_val]
      simp
      omega
    by_cases h6 : ((z 0).val / 4 + 12) % 13 = 6
    · exact hsub1 _ (hin 28 (by norm_num) (by omega)) (hcl 28 (by norm_num) (by norm_num))
    · exact hsub1 _ (hin 24 (by norm_num) (by omega)) (hcl 24 (by norm_num) (by norm_num))

/-- the corner `x₀ = (1,1,1)`. -/
def x0 : PeriodicLatticeSite L := mkS hL (fun _ => 1) (fun _ => by norm_num)

/-- **the unit star at `x₀` lies in no class cube.** -/
theorem vt_star_no_cube :
    ¬ ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube 2 2 12 1 (VT L) sites i ∧
      x0 hL ∈ sites ∧ ∀ σ, periodicLatticeShift (x0 hL) σ ∈ sites := by
  rintro ⟨sites, i, hq, hx, hs⟩
  refine vt_no_cube_of hL sites i hq (fun _ => x0 hL) (fun σ => periodicLatticeShift (x0 hL) σ)
    (fun σ => ⟨hx, by show (mkS hL (fun _ => 1) _ σ).val ≤ 1; rw [mkS_val]⟩) (fun σ => ⟨hs σ, ?_⟩)
  rw [shift_val hL, if_pos rfl]
  show 2 ≤ ((mkS hL (fun _ => 1) _ σ).val + 1) % 52 ∧ ((mkS hL (fun _ => 1) _ σ).val + 1) % 52 ≤ 3
  rw [mkS_val]; norm_num

/-- **clause 3 of `PerCubeRegular2` is never triggered at `x₀`**: for every direction `μ`, no class cube contains all the
`CurlReads` of the `ddA` stencil at `x₀`. -/
theorem vt_stencil_no_cube (μ : Fin 3) :
    ¬ ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube 2 2 12 1 (VT L) sites i ∧
      ∀ ν : Fin 3, ν ≠ μ → CurlReads sites (AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack (x0 hL) ν) ν μ ∧
        CurlReads sites (x0 hL) ν μ := by
  rintro ⟨sites, i, hq, hst⟩
  obtain ⟨ν0, hν0, -⟩ := third_axis μ μ
  have hb : ∀ ν, ν ≠ μ → CubeBond sites ((x0 hL, μ) : Bond L) ∧ CubeBond sites ((x0 hL, ν) : Bond L) :=
    fun ν hν => ⟨(hst ν hν).2.2.1, (hst ν hν).2.2.2.2⟩
  refine vt_star_no_cube hL ⟨sites, i, hq, (hb ν0 hν0).1.1, fun σ => ?_⟩
  by_cases h : σ = μ
  · subst h; exact (hb ν0 hν0).1.2
  · exact (hb σ h).2.2

end cover

end AdalyFormal.M2Route

#print axioms AdalyFormal.M2Route.vt_om0
#print axioms AdalyFormal.M2Route.vt_om1
#print axioms AdalyFormal.M2Route.vt_omj
#print axioms AdalyFormal.M2Route.mkS_val
#print axioms AdalyFormal.M2Route.vt_admissible
#print axioms AdalyFormal.M2Route.mem_box_iff
#print axioms AdalyFormal.M2Route.shift_val
#print axioms AdalyFormal.M2Route.corners_in_box
#print axioms AdalyFormal.M2Route.in48
#print axioms AdalyFormal.M2Route.in48'
#print axioms AdalyFormal.M2Route.zsel_table
#print axioms AdalyFormal.M2Route.zsel_lt
#print axioms AdalyFormal.M2Route.cv_col
#print axioms AdalyFormal.M2Route.in24_48
#print axioms AdalyFormal.M2Route.two_nonzero
#print axioms AdalyFormal.M2Route.side0
#print axioms AdalyFormal.M2Route.side1
#print axioms AdalyFormal.M2Route.vt_tb0
#print axioms AdalyFormal.M2Route.vt_tb1
#print axioms AdalyFormal.M2Route.idx1_cover
#print axioms AdalyFormal.M2Route.idx0_cover
#print axioms AdalyFormal.M2Route.third_axis
#print axioms AdalyFormal.M2Route.axes_cover
#print axioms AdalyFormal.M2Route.vt_plaq_cover
#print axioms AdalyFormal.M2Route.vt_coversp
#print axioms AdalyFormal.M2Route.vt_torusOK
#print axioms AdalyFormal.M2Route.vt_no_cube_of
#print axioms AdalyFormal.M2Route.vt_star_no_cube
#print axioms AdalyFormal.M2Route.vt_stencil_no_cube
