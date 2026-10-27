import CovA

/-!
# CovB -- every plaquette of `GT` lies in one class cube (`CoversOm0p 2 M 12 1 (GT L n M)`, every `n ≥ 25`)
(m2_coverage, 2026-10-14)

Block coordinates `a σ = x_σ / M` on `ℤ/(2n)`.  Case analysis on the plaquette's block cluster:
* two axes whose cluster avoids column `0`: an index-1 cube (24 blocks, even corner) avoiding column `0` on those axes;
* one such axis with its cluster in the middle band `[14, 2n-14]`: an index-1 cube whose window on that axis avoids
  columns `0, 6, n-6`;
* otherwise: an index-0 cube (12 blocks) meeting a hole along the free axis (or the third axis).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2Coverage

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M2Bridge (cube_isClass)
open AdalyFormal.M2Route (third_axis axes_cover)

section cover
variable {L : PeriodicLatticeExtent} {n M : ℕ} (hM : 0 < M) (hn : 25 ≤ n) (hL : ∀ μ, L μ + 1 = 2 * n * M)
include hM hn hL

def mkG (f : Fin 3 → ℕ) (hf : ∀ σ, f σ < 2 * n * M) : PeriodicLatticeSite L :=
  fun σ => ⟨f σ, by have := hL σ; have := hf σ; omega⟩

omit hM hn in
theorem mkG_val (f : Fin 3 → ℕ) (hf : ∀ σ, f σ < 2 * n * M) (σ : Fin 3) : ((mkG hL f hf) σ).val = f σ := rfl

omit hM hn in
theorem mul_lt2n (b : ℕ) (hb : b < 2 * n) : M * b < 2 * n * M ↔ 0 < M := by
  constructor
  · intro h; rcases Nat.eq_zero_or_pos M with h0 | h0
    · subst h0; simp at h
    · exact h0
  · intro h0
    have := Nat.mul_lt_mul_of_pos_left hb h0
    rw [mul_comm M (2 * n)] at this; exact this

theorem mulb_lt (b : ℕ) (hb : b < 2 * n) : M * b < 2 * n * M := (mul_lt2n hL b hb).2 hM

omit hM hn in
theorem mem_boxG (z : PeriodicLatticeSite L) (s : ℕ) (x : PeriodicLatticeSite L) :
    x ∈ siteBox z s ↔ ∀ σ, ((x σ).val + 2 * n * M - (z σ).val) % (2 * n * M) < s := by
  simp only [siteBox, Set.mem_setOf_eq, hL]

theorem mem_boxBG (b : Fin 3 → ℕ) (hb : ∀ σ, b σ < 2 * n) (c : ℕ) (x : PeriodicLatticeSite L) :
    x ∈ siteBox (mkG hL (fun σ => M * b σ) (fun σ => mulb_lt hM hn hL (b σ) (hb σ))) (c * M) ↔
      ∀ σ, inB (2 * n) (b σ) c ((x σ).val / M) := by
  rw [mem_boxG hL]
  refine forall_congr' (fun σ => ?_)
  rw [mkG_val]
  exact modK M (2 * n) _ _ c hM (xlt hM hn hL x σ) (hb σ)

omit hM hn in
theorem shiftG_val (x : PeriodicLatticeSite L) (μ σ : Fin 3) :
    (periodicLatticeShift x μ σ).val = if σ = μ then ((x σ).val + 1) % (2 * n * M) else (x σ).val := by
  unfold periodicLatticeShift
  by_cases h : σ = μ
  · subst h
    rw [Function.update_self, if_pos rfl, Fin.val_add_one]
    have hl := (x σ).isLt
    have hL' := hL σ
    split_ifs with h1
    · rw [h1, Fin.val_last, hL']; exact (Nat.mod_self _).symm
    · have : (x σ).val ≠ L σ := fun h2 => h1 (Fin.ext (by rw [h2, Fin.val_last]))
      rw [← hL']
      exact (Nat.mod_eq_of_lt (by omega)).symm
  · rw [Function.update_of_ne h, if_neg h]

/-- corners of the plaquette `(x; μ, ν)` in a block-cornered box. -/
theorem cornersG (b : Fin 3 → ℕ) (hb : ∀ σ, b σ < 2 * n) (c : ℕ) (x : PeriodicLatticeSite L) {μ ν : Fin 3}
    (hμν : μ ≠ ν)
    (h : ∀ σ, inB (2 * n) (b σ) c ((x σ).val / M) ∧
      ((σ = μ ∨ σ = ν) → inB (2 * n) (b σ) c ((((x σ).val + 1) % (2 * n * M)) / M))) :
    let z := mkG hL (fun σ => M * b σ) (fun σ => mulb_lt hM hn hL (b σ) (hb σ))
    x ∈ siteBox z (c * M) ∧ periodicLatticeShift x μ ∈ siteBox z (c * M) ∧
      periodicLatticeShift x ν ∈ siteBox z (c * M) ∧
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ siteBox z (c * M) := by
  intro z
  simp only [z, mem_boxBG hM hn hL b hb c, shiftG_val hL]
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

omit hM hn hL in
theorem gt_tb0 {c : PeriodicLatticeSite L} (hc : GH n M c) : c ∈ towerBj (GT L n M) 0 := by
  refine ⟨by rw [gt_om0]; trivial, ?_⟩
  rw [show (0 : ℕ) + 1 = 1 from rfl, gt_om1]; exact fun h => h hc

omit hM hn hL in
theorem gt_tb1 {y : PeriodicLatticeSite L} (hy : y ∈ (GT L n M).Om 1) : y ∈ towerBj (GT L n M) 1 :=
  ⟨hy, by rw [gt_omj (by norm_num)]; exact fun h => h⟩

omit hM hn hL in
theorem col_eq (v : ℕ) : v / (M * 2) = v / M / 2 := by rw [Nat.div_div_eq_div_mul]

/-- index-1 cube from a block window `b` (even corners, 24 blocks) whose box contains no hole. -/
theorem idx1G (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hμν : μ ≠ ν) {R : ℕ} (hR : 18 ≤ R)
    (b : Fin 3 → ℕ) (hb : ∀ σ, b σ < 2 * n) (hbe : ∀ σ, b σ % 2 = 0)
    (hfree : ∀ q : Fin 3 → ℕ, (∀ σ, q σ < 2 * n) → (∀ σ, inB (2 * n) (b σ) 24 (q σ)) →
      ¬ holeQ n (q 0 / 2) (q 1 / 2) (q 2 / 2))
    (hin : ∀ σ, inB (2 * n) (b σ) 24 ((x σ).val / M) ∧
      ((σ = μ ∨ σ = ν) → inB (2 * n) (b σ) 24 ((((x σ).val + 1) % (2 * n * M)) / M))) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube 2 M 12 1 (GT L n M) sites j ∧
      x ∈ sites ∧ periodicLatticeShift x μ ∈ sites ∧ periodicLatticeShift x ν ∈ sites ∧
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ sites := by
  set z := mkG hL (fun σ => M * b σ) (fun σ => mulb_lt hM hn hL (b σ) (hb σ)) with hz
  have hside : 12 * bigSide M 2 1 = 24 * M := by rw [bs1]; ring
  have hsub : siteBox z (12 * bigSide M 2 1) ⊆ (GT L n M).Om 1 := by
    rw [hside]
    intro y hy
    rw [hz, mem_boxBG hM hn hL b hb] at hy
    rw [gt_om1]
    show ¬ holeQ n ((y 0).val / (M * 2)) ((y 1).val / (M * 2)) ((y 2).val / (M * 2))
    rw [col_eq, col_eq, col_eq]
    exact hfree (fun σ => (y σ).val / M) (fun σ => blk_lt M _ _ hM (xlt hM hn hL y σ)) hy
  have hc := cornersG hM hn hL b hb 24 x hμν hin
  simp only at hc
  rw [← hside] at hc
  have hgrid : GridCorner (bigSide M 2 1) z := by
    intro σ
    rw [bs1]
    show (M * b σ) % (M * 2) = 0
    have : M * b σ = (M * 2) * (b σ / 2) := by
      have := Nat.div_add_mod (b σ) 2
      rw [hbe σ] at this
      calc M * b σ = M * (2 * (b σ / 2) + 0) := by rw [this]
        _ = (M * 2) * (b σ / 2) := by ring
    rw [this]; exact Nat.mul_mod_right _ _
  refine ⟨siteBox z (12 * bigSide M 2 1), 1, ?_, hc⟩
  exact cube_isClass (gt_admissible hM hn hL (R := R) (by omega)) (le_refl 1) hgrid hsub hc.1 (gt_tb1 (hsub hc.1)) (by omega)

/-- index-0 cube (12 blocks) from a block window `b` containing a hole block `cb`. -/
theorem idx0G (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hμν : μ ≠ ν) {R : ℕ} (hR : 18 ≤ R)
    (b : Fin 3 → ℕ) (hb : ∀ σ, b σ < 2 * n) (cb : Fin 3 → ℕ) (hcb : ∀ σ, cb σ < 2 * n)
    (hcin : ∀ σ, inB (2 * n) (b σ) 12 (cb σ)) (hhole : holeQ n (cb 0 / 2) (cb 1 / 2) (cb 2 / 2))
    (hin : ∀ σ, inB (2 * n) (b σ) 12 ((x σ).val / M) ∧
      ((σ = μ ∨ σ = ν) → inB (2 * n) (b σ) 12 ((((x σ).val + 1) % (2 * n * M)) / M))) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube 2 M 12 1 (GT L n M) sites j ∧
      x ∈ sites ∧ periodicLatticeShift x μ ∈ sites ∧ periodicLatticeShift x ν ∈ sites ∧
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ sites := by
  set z := mkG hL (fun σ => M * b σ) (fun σ => mulb_lt hM hn hL (b σ) (hb σ)) with hz
  set c := mkG hL (fun σ => M * cb σ) (fun σ => mulb_lt hM hn hL (cb σ) (hcb σ)) with hc
  have hside : 12 * bigSide M 2 0 = 12 * M := by rw [bs0]
  have hcor := cornersG hM hn hL b hb 12 x hμν hin
  simp only at hcor
  rw [← hside] at hcor
  have hcbox : c ∈ siteBox z (12 * bigSide M 2 0) := by
    rw [hside, hz, mem_boxBG hM hn hL b hb]
    intro σ
    rw [hc, mkG_val, Nat.mul_div_cancel_left _ hM]
    exact hcin σ
  have hcl : GH n M c := by
    show holeQ n ((c 0).val / (M * 2)) ((c 1).val / (M * 2)) ((c 2).val / (M * 2))
    rw [col_eq, col_eq, col_eq, hc, mkG_val, mkG_val, mkG_val,
      Nat.mul_div_cancel_left _ hM, Nat.mul_div_cancel_left _ hM, Nat.mul_div_cancel_left _ hM]
    exact hhole
  have hgrid : GridCorner (bigSide M 2 0) z := by
    intro σ
    rw [bs0]
    show (M * b σ) % M = 0
    exact Nat.mul_mod_right _ _
  have hsub : siteBox z (12 * bigSide M 2 0) ⊆ (GT L n M).Om 0 := by rw [gt_om0]; exact Set.subset_univ _
  refine ⟨siteBox z (12 * bigSide M 2 0), 0, ?_, hcor⟩
  exact cube_isClass (gt_admissible hM hn hL (R := R) (by omega)) (Nat.zero_le 1) hgrid hsub hcbox (gt_tb0 hcl) (by omega)

omit hM hn hL in
/-- `holeQ` read off three explicit columns. -/
theorem holeQ_axis (n : ℕ) (γ : Fin 3) (q : Fin 3 → ℕ) (hγ : q γ = 6 ∨ q γ = n - 6) (h0 : ∀ σ, σ ≠ γ → q σ = 0) :
    holeQ n (q 0) (q 1) (q 2) := by
  unfold holeQ
  fin_cases γ
  · have h1 := h0 1 (by decide); have h2 := h0 2 (by decide); simp at hγ; omega
  · have h1 := h0 0 (by decide); have h2 := h0 2 (by decide); simp at hγ; omega
  · have h1 := h0 0 (by decide); have h2 := h0 1 (by decide); simp at hγ; omega

/-- **every plaquette of `GT` lies in one class cube.** -/
theorem gt_plaq_cover {R : ℕ} (hR : 18 ≤ R) (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hμν : μ ≠ ν) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube 2 M 12 1 (GT L n M) sites j ∧
      x ∈ sites ∧ periodicLatticeShift x μ ∈ sites ∧ periodicLatticeShift x ν ∈ sites ∧
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ sites := by
  classical
  obtain ⟨a, hadef⟩ : ∃ a : Fin 3 → ℕ, a = fun σ => (x σ).val / M := ⟨_, rfl⟩
  obtain ⟨a', ha'def⟩ : ∃ a' : Fin 3 → ℕ, a' = fun σ => (((x σ).val + 1) % (2 * n * M)) / M := ⟨_, rfl⟩
  have hxa : ∀ σ, (x σ).val / M = a σ := fun σ => by rw [hadef]
  have hxa' : ∀ σ, (((x σ).val + 1) % (2 * n * M)) / M = a' σ := fun σ => by rw [ha'def]
  have hal : ∀ σ, a σ < 2 * n := fun σ => by rw [← hxa σ]; exact blk_lt M _ _ hM (xlt hM hn hL x σ)
  have hsh : ∀ σ, a' σ = a σ ∨ (a σ + 1 < 2 * n ∧ a' σ = a σ + 1) ∨ (a σ + 1 = 2 * n ∧ a' σ = 0) := by
    intro σ
    have h1 := hal σ
    rcases shift_blk M (2 * n) _ hM (xlt hM hn hL x σ) with h | h
    · left; rw [← hxa σ, ← hxa' σ]; exact h
    · right
      rw [hxa' σ, hxa σ] at h
      by_cases h2 : a σ + 1 < 2 * n
      · left; refine ⟨h2, ?_⟩; rw [h]; exact Nat.mod_eq_of_lt h2
      · right; refine ⟨by omega, ?_⟩
        rw [h, show a σ + 1 = 2 * n by omega, Nat.mod_self]
  -- the window goals, in terms of `a`, `a'`
  have hwin : ∀ (b : Fin 3 → ℕ) (w : ℕ),
      (∀ σ, inB (2 * n) (b σ) w (a σ) ∧ ((σ = μ ∨ σ = ν) → inB (2 * n) (b σ) w (a' σ))) →
      ∀ σ, inB (2 * n) (b σ) w ((x σ).val / M) ∧
        ((σ = μ ∨ σ = ν) → inB (2 * n) (b σ) w ((((x σ).val + 1) % (2 * n * M)) / M)) := by
    intro b w h σ
    rw [hxa σ, hxa' σ]; exact h σ
  -- the cluster on axis σ touches column 0
  obtain ⟨Z, hZ⟩ : ∃ Z : Fin 3 → Prop, Z = fun σ => a σ / 2 = 0 ∨ ((σ = μ ∨ σ = ν) ∧ a' σ / 2 = 0) := ⟨_, rfl⟩
  have hZa : ∀ σ, Z σ → (a σ = 2 * n - 1 ∨ a σ ≤ 1) ∧ ((σ = μ ∨ σ = ν) → a' σ ≤ 2) := by
    intro σ hσ
    rw [hZ] at hσ
    have := hal σ; have := hsh σ
    rcases hσ with h | ⟨-, h⟩
    · exact ⟨by omega, fun _ => by omega⟩
    · exact ⟨by omega, fun _ => by omega⟩
  have hNZ : ∀ σ, ¬ Z σ → 2 ≤ a σ ∧ ((σ = μ ∨ σ = ν) → 2 ≤ a' σ ∧ a' σ ≤ a σ + 1) := by
    intro σ hσ
    rw [hZ] at hσ
    simp only [not_or, not_and] at hσ
    have := hal σ; have := hsh σ
    refine ⟨by omega, fun h => ?_⟩
    have := hσ.2 h; omega
  have inZ : ∀ σ, Z σ → ∀ w, (w = 12 ∨ w = 24) → inB (2 * n) (2 * n - 2) w (a σ) ∧
      ((σ = μ ∨ σ = ν) → inB (2 * n) (2 * n - 2) w (a' σ)) := by
    intro σ hσ w hw
    have h1 := hZa σ hσ
    have h2 := hal σ
    refine ⟨(inB_iff h2 (by omega)).2 (by omega), fun h => ?_⟩
    have h3 := h1.2 h
    exact (inB_iff (by omega) (by omega)).2 (by omega)
  by_cases hA : ∃ α β : Fin 3, α ≠ β ∧ ¬ Z α ∧ ¬ Z β
  · -- index 1, windows avoiding column 0 on the two free axes
    obtain ⟨α, β, hab, hα, hβ⟩ := hA
    obtain ⟨b, hbdef⟩ : ∃ b : Fin 3 → ℕ, b = fun σ => if Z σ then 2 * n - 2 else min (2 * (a σ / 2)) (2 * n - 24) :=
      ⟨_, rfl⟩
    have hbZ : ∀ σ, Z σ → b σ = 2 * n - 2 := fun σ h => by rw [hbdef]; simp only [if_pos h]
    have hbN : ∀ σ, ¬ Z σ → b σ = min (2 * (a σ / 2)) (2 * n - 24) := fun σ h => by rw [hbdef]; simp only [if_neg h]
    have hb : ∀ σ, b σ < 2 * n := fun σ => by
      have := hal σ
      by_cases h : Z σ
      · rw [hbZ σ h]; omega
      · rw [hbN σ h]; omega
    have hbe : ∀ σ, b σ % 2 = 0 := fun σ => by
      by_cases h : Z σ
      · rw [hbZ σ h]; omega
      · rw [hbN σ h]; omega
    refine idx1G hM hn hL x hμν hR b hb hbe ?_ (hwin b 24 (fun σ => ?_))
    · intro q hq hqin
      refine two_ne_zero_noHole n (fun σ => q σ / 2) α β hab ?_ ?_
      · have h1 := (inB_iff (hq α) (hb α)).1 (hqin α)
        have h2 := hb α
        rw [hbN α hα] at h1 h2
        have h3 := (hNZ α hα).1
        have h4 := hal α
        show q α / 2 ≠ 0
        omega
      · have h1 := (inB_iff (hq β) (hb β)).1 (hqin β)
        have h2 := hb β
        rw [hbN β hβ] at h1 h2
        have h3 := (hNZ β hβ).1
        have h4 := hal β
        show q β / 2 ≠ 0
        omega
    · by_cases hσ : Z σ
      · rw [hbZ σ hσ]; exact inZ σ hσ 24 (Or.inr rfl)
      · rw [hbN σ hσ]
        have h1 := hNZ σ hσ
        have h2 := hal σ
        refine ⟨(inB_iff h2 (by omega)).2 (by omega), fun h => ?_⟩
        have h3 := h1.2 h
        have h4 := hsh σ
        exact (inB_iff (by omega) (by omega)).2 (by omega)
  · push Not at hA
    obtain ⟨l, hl1, hl2⟩ := third_axis μ ν
    by_cases hex : ∃ σ₀ : Fin 3, ¬ Z σ₀
    · obtain ⟨σ₀, hσ₀⟩ := hex
      have hoth : ∀ σ, σ ≠ σ₀ → Z σ := by
        intro σ hσ
        by_contra hn'
        exact hn' (hA σ₀ σ (Ne.symm hσ) hσ₀)
      have hN0 := hNZ σ₀ hσ₀
      have htl := hal σ₀
      by_cases hmid : 14 ≤ a σ₀ ∧ a σ₀ ≤ 2 * n - 14
      · -- index 1 with a middle window on σ₀
        obtain ⟨b, hbdef⟩ : ∃ b : Fin 3 → ℕ,
            b = fun σ => if σ = σ₀ then min (2 * (a σ₀ / 2)) (2 * n - 36) else 2 * n - 2 := ⟨_, rfl⟩
        have hb0 : b σ₀ = min (2 * (a σ₀ / 2)) (2 * n - 36) := by rw [hbdef]; simp
        have hbo : ∀ σ, σ ≠ σ₀ → b σ = 2 * n - 2 := fun σ h => by rw [hbdef]; simp only [if_neg h]
        have hb : ∀ σ, b σ < 2 * n := fun σ => by
          by_cases h : σ = σ₀
          · rw [h, hb0]; omega
          · rw [hbo σ h]; omega
        have hbe : ∀ σ, b σ % 2 = 0 := fun σ => by
          by_cases h : σ = σ₀
          · rw [h, hb0]; omega
          · rw [hbo σ h]; omega
        refine idx1G hM hn hL x hμν hR b hb hbe ?_ (hwin b 24 (fun σ => ?_))
        · intro q hq hqin
          have h1 := (inB_iff (hq σ₀) (hb σ₀)).1 (hqin σ₀)
          have h2 := hb σ₀
          rw [hb0] at h1 h2
          refine one_free_noHole n (fun σ => q σ / 2) σ₀ ?_ ?_ ?_
          · show q σ₀ / 2 ≠ 0; omega
          · show q σ₀ / 2 ≠ 6; omega
          · show q σ₀ / 2 ≠ n - 6; omega
        · by_cases hσ : σ = σ₀
          · rw [hσ, hb0]
            refine ⟨(inB_iff htl (by omega)).2 (by omega), fun h => ?_⟩
            have h3 := hN0.2 h
            have h4 := hsh σ₀
            exact (inB_iff (by omega) (by omega)).2 (by omega)
          · rw [hbo σ hσ]; exact inZ σ (hoth σ hσ) 24 (Or.inr rfl)
      · -- index 0, window on σ₀ meeting a hole of axis σ₀
        obtain ⟨w, hw⟩ : ∃ w : ℕ, w = if a σ₀ ≤ 13 then a σ₀ else if a σ₀ = 2 * n - 13 then 2 * n - 13 else 2 * n - 12 :=
          ⟨_, rfl⟩
        obtain ⟨cv, hcv⟩ : ∃ cv : ℕ, cv = if a σ₀ ≤ 12 then 12 else if a σ₀ = 13 then 13 else 2 * n - 12 := ⟨_, rfl⟩
        have hwl : w < 2 * n := by rw [hw]; split_ifs <;> omega
        have hcvl : cv < 2 * n := by rw [hcv]; split_ifs <;> omega
        have hwin0 : (w ≤ a σ₀ ∧ a σ₀ - w < 12 ∧ (a σ₀ + 1 < 2 * n → a σ₀ + 1 - w < 12)) ∧ (w ≤ cv ∧ cv - w < 12) ∧
            (cv / 2 = 6 ∨ cv / 2 = n - 6) := by
          rw [hw, hcv]; split_ifs <;> omega
        obtain ⟨b, hbdef⟩ : ∃ b : Fin 3 → ℕ, b = fun σ => if σ = σ₀ then w else 2 * n - 2 := ⟨_, rfl⟩
        obtain ⟨cb, hcbdef⟩ : ∃ cb : Fin 3 → ℕ, cb = fun σ => if σ = σ₀ then cv else 0 := ⟨_, rfl⟩
        have hb0 : b σ₀ = w := by rw [hbdef]; simp
        have hbo : ∀ σ, σ ≠ σ₀ → b σ = 2 * n - 2 := fun σ h => by rw [hbdef]; simp only [if_neg h]
        have hc0 : cb σ₀ = cv := by rw [hcbdef]; simp
        have hco : ∀ σ, σ ≠ σ₀ → cb σ = 0 := fun σ h => by rw [hcbdef]; simp only [if_neg h]
        have hb : ∀ σ, b σ < 2 * n := fun σ => by
          by_cases h : σ = σ₀
          · rw [h, hb0]; exact hwl
          · rw [hbo σ h]; omega
        have hcb : ∀ σ, cb σ < 2 * n := fun σ => by
          by_cases h : σ = σ₀
          · rw [h, hc0]; exact hcvl
          · rw [hco σ h]; omega
        refine idx0G hM hn hL x hμν hR b hb cb hcb (fun σ => ?_) ?_ (hwin b 12 (fun σ => ?_))
        · by_cases hσ : σ = σ₀
          · rw [hσ, hb0, hc0]
            exact (inB_iff hcvl hwl).2 (Or.inl ⟨hwin0.2.1.1, hwin0.2.1.2⟩)
          · rw [hbo σ hσ, hco σ hσ]
            exact (inB_iff (by omega) (by omega)).2 (by omega)
        · refine holeQ_axis n σ₀ (fun σ => cb σ / 2) ?_ (fun σ hσ => ?_)
          · show cb σ₀ / 2 = 6 ∨ cb σ₀ / 2 = n - 6
            rw [hc0]; exact hwin0.2.2
          · show cb σ / 2 = 0
            rw [hco σ hσ]
        · by_cases hσ : σ = σ₀
          · rw [hσ, hb0]
            refine ⟨(inB_iff htl hwl).2 (Or.inl ⟨hwin0.1.1, hwin0.1.2.1⟩), fun h => ?_⟩
            have h3 := hN0.2 h
            have h4 := hsh σ₀
            exact (inB_iff (by omega) hwl).2 (by have := hwin0.1; omega)
          · rw [hbo σ hσ]
            exact inZ σ (hoth σ hσ) 12 (Or.inl rfl)
    · -- every axis touches column 0: index 0 along the third axis `l`
      push Not at hex
      have hlnot : ¬ (l = μ ∨ l = ν) := by rintro (h | h) <;> contradiction
      have hal0 : a l ≤ 1 := by
        have h := hex l
        rw [hZ] at h
        rcases h with h | ⟨h, -⟩
        · omega
        · exact absurd h hlnot
      obtain ⟨w, hw⟩ : ∃ w : ℕ, w = if a l = 0 then 2 * n - 11 else 1 := ⟨_, rfl⟩
      obtain ⟨cv, hcv⟩ : ∃ cv : ℕ, cv = if a l = 0 then 2 * n - 11 else 12 := ⟨_, rfl⟩
      have hwl : w < 2 * n := by rw [hw]; split_ifs <;> omega
      have hcvl : cv < 2 * n := by rw [hcv]; split_ifs <;> omega
      have hwin0 : inB (2 * n) w 12 (a l) ∧ inB (2 * n) w 12 cv ∧ (cv / 2 = 6 ∨ cv / 2 = n - 6) := by
        rw [inB_iff (hal l) hwl, inB_iff hcvl hwl, hw, hcv]; split_ifs <;> omega
      obtain ⟨b, hbdef⟩ : ∃ b : Fin 3 → ℕ, b = fun σ => if σ = l then w else 2 * n - 2 := ⟨_, rfl⟩
      obtain ⟨cb, hcbdef⟩ : ∃ cb : Fin 3 → ℕ, cb = fun σ => if σ = l then cv else 0 := ⟨_, rfl⟩
      have hb0 : b l = w := by rw [hbdef]; simp
      have hbo : ∀ σ, σ ≠ l → b σ = 2 * n - 2 := fun σ h => by rw [hbdef]; simp only [if_neg h]
      have hc0 : cb l = cv := by rw [hcbdef]; simp
      have hco : ∀ σ, σ ≠ l → cb σ = 0 := fun σ h => by rw [hcbdef]; simp only [if_neg h]
      have hb : ∀ σ, b σ < 2 * n := fun σ => by
        by_cases h : σ = l
        · rw [h, hb0]; exact hwl
        · rw [hbo σ h]; omega
      have hcb : ∀ σ, cb σ < 2 * n := fun σ => by
        by_cases h : σ = l
        · rw [h, hc0]; exact hcvl
        · rw [hco σ h]; omega
      refine idx0G hM hn hL x hμν hR b hb cb hcb (fun σ => ?_) ?_ (hwin b 12 (fun σ => ?_))
      · by_cases hσ : σ = l
        · rw [hσ, hb0, hc0]; exact hwin0.2.1
        · rw [hbo σ hσ, hco σ hσ]
          exact (inB_iff (by omega) (by omega)).2 (by omega)
      · refine holeQ_axis n l (fun σ => cb σ / 2) ?_ (fun σ hσ => ?_)
        · show cb l / 2 = 6 ∨ cb l / 2 = n - 6
          rw [hc0]; exact hwin0.2.2
        · show cb σ / 2 = 0
          rw [hco σ hσ]
      · by_cases hσ : σ = l
        · rw [hσ, hb0]
          exact ⟨hwin0.1, fun h => absurd h hlnot⟩
        · rw [hbo σ hσ]
          exact inZ σ (hex σ) 12 (Or.inl rfl)

theorem gt_coversp {R : ℕ} (hR : 18 ≤ R) : CoversOm0p 2 M 12 1 (GT L n M) := by
  refine ⟨fun x _ => ?_, fun p _ => ?_⟩
  · obtain ⟨sites, j, hq, hx, -⟩ := gt_plaq_cover hM hn hL hR x (μ := 0) (ν := 1) (by decide)
    exact ⟨sites, j, hq, hx⟩
  · obtain ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩ := p
    obtain ⟨sites, j, hq, h1, h2, h3, h4⟩ := gt_plaq_cover hM hn hL hR x (μ := μ) (ν := ν) (ne_of_lt hμν)
    refine ⟨sites, j, hq, fun e he => ?_⟩
    simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨h1, h2⟩
    · exact ⟨h2, h4⟩
    · exact ⟨h3, by rw [AdalyFormal.M2Route.shift_comm]; exact h4⟩
    · exact ⟨h1, h3⟩

end cover

end AdalyFormal.M2Coverage
