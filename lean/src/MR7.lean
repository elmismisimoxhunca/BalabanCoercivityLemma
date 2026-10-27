import MR6

/-!
# MR7 -- the corner of MR6 for EVERY even `M` and every `R ≥ 18` (m2_route, 2026-10-14)

`VTM L M` : on the fine torus of side `26 M` (`ell = 2`, `k = 1`), `Ω₀` = everything, `Ω₁` = everything except six level-1
big blocks (side `2M`) at big-block coordinates `(6,0,0), (7,0,0), (0,6,0), (0,7,0), (0,0,6), (0,0,7)`, `Ω₂ = ∅`.
All box arithmetic is reduced to level-0 block coordinates `v / M` on `ℤ/26` (`modKR`), where MR6's argument runs verbatim
(MR6 is the case `M = 2`).
* **`vtm_corner`** : for every even `M ≥ 2`, every `R ≥ 18` and `Lu` with `Lu μ + 1 = 13 M`:
  `TorusOK 2 M Lu`, `Admissible 2 M R 1 (VTM _ M)`, `CoversOm0p 2 M 12 1 (VTM _ M)` (sites and plaquettes), and the site
  `x₀ = (M-1, M-1, M-1)` together with its three forward neighbours lies in NO class cube.
* `vtm_stencil_no_cube` : hence clause 3 of `PerCubeRegular2` is never triggered at `x₀`, in any direction.
No sorry / axiom / native_decide.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2Route

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M2Bridge (cube_isClass)

/-! ## block arithmetic on `ℤ/(26 M)` -/

/-- `a` lies in the cyclic block window `[b, b + c)` of `ℤ/26`. -/
def inB (b c a : ℕ) : Prop := (a + 26 - b) % 26 < c

theorem mul_lt26 (M b : ℕ) (hM : 0 < M) (hb : b < 26) : M * b < 26 * M := by
  have := Nat.mul_lt_mul_of_pos_left hb hM
  rw [mul_comm M 26] at this; exact this

theorem modKR (M v b c : ℕ) (hM : 0 < M) (hv : v < 26 * M) (hb : b < 26) :
    (v + 26 * M - M * b) % (26 * M) < c * M ↔ inB b c (v / M) := by
  unfold inB
  have hr : v % M < M := Nat.mod_lt _ hM
  have hv' : M * (v / M) + v % M = v := Nat.div_add_mod v M
  have ha : v / M < 26 := (Nat.div_lt_iff_lt_mul hM).2 hv
  generalize hqa : v / M = a at hv' ha ⊢
  generalize hqr : v % M = r at hv' hr ⊢
  obtain ⟨d, hd⟩ : ∃ d, d = 26 - b := ⟨_, rfl⟩
  have hbd : b + d = 26 := by omega
  have hMd : M * b + M * d = 26 * M := by rw [← Nat.mul_add, hbd, mul_comm]
  have e1 : v + 26 * M - M * b = M * (a + d) + r := by
    have h6 : v + 26 * M - M * b = v + M * d := by rw [← hMd]; omega
    rw [h6, Nat.mul_add]; omega
  have e0 : a + 26 - b = a + d := by omega
  rw [e1, e0]
  obtain ⟨t, ht⟩ : ∃ t, t = a + d := ⟨_, rfl⟩
  rw [← ht]
  have htq : t = 26 * (t / 26) + t % 26 := (Nat.div_add_mod t 26).symm
  have ht26 : t % 26 < 26 := Nat.mod_lt _ (by norm_num)
  have e2 : (M * t + r) % (26 * M) = M * (t % 26) + r := by
    have h3 : M * t + r = (M * (t % 26) + r) + (26 * M) * (t / 26) := by
      conv_lhs => rw [htq]
      ring
    rw [h3, Nat.add_mul_mod_self_left]
    apply Nat.mod_eq_of_lt
    have h4 : M * (t % 26) + M ≤ 26 * M := by
      have := Nat.mul_le_mul_left M (show t % 26 + 1 ≤ 26 by omega)
      rw [Nat.mul_add, mul_one, mul_comm M 26] at this
      exact this
    omega
  rw [e2]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have := Nat.mul_le_mul_left M hc
    rw [mul_comm M c] at this
    omega
  · intro h
    have := Nat.mul_le_mul_left M (show t % 26 + 1 ≤ c by omega)
    rw [Nat.mul_add, mul_one, mul_comm M c] at this
    omega

theorem win24 (B q : ℕ) (hB : B < 26) (hB2 : B % 2 = 0) (hq : q < 26) :
    inB B 24 q ↔ q / 2 ≠ (B / 2 + 12) % 13 := by
  unfold inB; omega

theorem blk_lt (M v : ℕ) (hM : 0 < M) (hv : v < 26 * M) : v / M < 26 := (Nat.div_lt_iff_lt_mul hM).2 hv

/-- the block of `v + 1` is the block of `v` or the next one. -/
theorem shift_blk (M v : ℕ) (hM : 0 < M) (hv : v < 26 * M) :
    ((v + 1) % (26 * M)) / M = v / M ∨ ((v + 1) % (26 * M)) / M = (v / M + 1) % 26 := by
  have hv' : M * (v / M) + v % M = v := Nat.div_add_mod v M
  have hr : v % M < M := Nat.mod_lt _ hM
  have ha := blk_lt M v hM hv
  by_cases h1 : v + 1 < 26 * M
  · rw [Nat.mod_eq_of_lt h1]
    have e : v + 1 = (v % M + 1) + M * (v / M) := by omega
    rw [e, Nat.add_mul_div_left _ _ hM]
    by_cases h2 : v % M + 1 < M
    · left; rw [Nat.div_eq_of_lt h2]; ring
    · right
      have h3 : v % M + 1 = M := by omega
      rw [h3, Nat.div_self hM]
      have h4 : v / M + 1 < 26 := by
        by_contra hc
        have : 26 * M ≤ M * (v / M) + M := by
          have := Nat.mul_le_mul_left M (show 26 ≤ v / M + 1 by omega)
          rw [Nat.mul_add, mul_one, mul_comm M 26] at this; exact this
        omega
      rw [Nat.mod_eq_of_lt h4]; ring
  · have h1' : v + 1 = 26 * M := by omega
    rw [h1', Nat.mod_self, Nat.zero_div]
    right
    have h5 : v / M = 25 := by
      have e : v = (M - 1) + M * 25 := by
        have : 26 * M = M * 25 + M := by ring
        omega
      rw [e, Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt (by omega)]
    rw [h5]

def VCl {L : PeriodicLatticeExtent} (M : ℕ) (x : PeriodicLatticeSite L) : Prop :=
  clumpQ ((x 0).val / (M * 2)) ((x 1).val / (M * 2)) ((x 2).val / (M * 2))

def mkM {L : PeriodicLatticeExtent} {M : ℕ} (hL : ∀ μ, L μ + 1 = 26 * M) (f : Fin 3 → ℕ) (hf : ∀ σ, f σ < 26 * M) :
    PeriodicLatticeSite L :=
  fun σ => ⟨f σ, by have := hL σ; have := hf σ; omega⟩

theorem mkM_val {L : PeriodicLatticeExtent} {M : ℕ} (hL : ∀ μ, L μ + 1 = 26 * M) (f : Fin 3 → ℕ)
    (hf : ∀ σ, f σ < 26 * M) (σ : Fin 3) : ((mkM hL f hf) σ).val = f σ := rfl

/-- the corner `x₀ = (M-1, M-1, M-1)`. -/
def x0M {L : PeriodicLatticeExtent} {M : ℕ} (hM : 0 < M) (hL : ∀ μ, L μ + 1 = 26 * M) : PeriodicLatticeSite L :=
  mkM hL (fun _ => M - 1) (fun _ => by omega)

def VTM (L : PeriodicLatticeExtent) (M : ℕ) : Tower L :=
  ⟨fun j => if j = 0 then Set.univ else if j = 1 then {x | ¬ VCl M x} else ∅⟩

theorem vtm_om0 {L : PeriodicLatticeExtent} {M : ℕ} : (VTM L M).Om 0 = Set.univ := by simp [VTM]
theorem vtm_om1 {L : PeriodicLatticeExtent} {M : ℕ} : (VTM L M).Om 1 = {x | ¬ VCl M x} := by simp [VTM]
theorem vtm_omj {L : PeriodicLatticeExtent} {M j : ℕ} (hj : 2 ≤ j) : (VTM L M).Om j = ∅ := by
  simp only [VTM]; rw [if_neg (by omega), if_neg (by omega)]

theorem bs0 (M : ℕ) : bigSide M 2 0 = M := by simp [bigSide]
theorem bs1 (M : ℕ) : bigSide M 2 1 = M * 2 := by simp [bigSide]

section main
variable {L : PeriodicLatticeExtent} {M : ℕ} (hM : 0 < M) (hL : ∀ μ, L μ + 1 = 26 * M)
include hM hL

theorem xlt (x : PeriodicLatticeSite L) (σ : Fin 3) : (x σ).val < 26 * M := by
  have := (x σ).isLt; have := hL σ; omega

theorem vtm_admissible {R : ℕ} (hR : 18 ≤ R) : Admissible 2 M R 1 (VTM L M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this; rw [vtm_om0]; trivial
    · rw [vtm_omj (by omega)] at hx; exact hx.elim
  · intro j hj; exact vtm_omj (by omega)
  · intro j hj μ
    rw [hL μ]
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this; rw [bs0]; exact Dvd.intro_left 26 rfl
    · have : j = 1 := by omega
      subst this; rw [bs1]; exact ⟨13, by ring⟩
  · intro j hj
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this; rw [vtm_om0]; intro x _ y _; trivial
    · have : j = 1 := by omega
      subst this; rw [vtm_om1, bs1]
      intro x hx y hy
      simp only [Set.mem_setOf_eq, VCl] at hx ⊢
      rw [hy 0, hy 1, hy 2]; exact hx
  · intro j hj x hx y hy
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this; rw [vtm_om0] at hx; exact (hx trivial).elim
    · rw [vtm_omj (by omega)] at hy; exact hy.elim
  · intro x
    rw [vtm_om0]
    simp only [Set.mem_univ, true_iff]
    have h10 : 10 * M < L 0 + 1 := by rw [hL 0]; omega
    refine ⟨Function.update x 0 ⟨10 * M, h10⟩, ?_, x, fun _ => rfl, ?_⟩
    · rw [vtm_om1]
      simp only [Set.mem_setOf_eq, VCl, clumpQ, Function.update_self]
      have e : 10 * M / (M * 2) = 5 := by
        rw [show 10 * M = (M * 2) * 5 by ring, Nat.mul_div_cancel_left _ (by omega)]
      rw [e]; omega
    · unfold pdist
      rw [Fin.sum_univ_three]
      simp only [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
        Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
      have h1 : pcd (L 1 + 1) (x 1).val (x 1).val = 0 := by unfold pcd; simp
      have h2 : pcd (L 2 + 1) (x 2).val (x 2).val = 0 := by unfold pcd; simp
      have h0 : pcd (L 0 + 1) (x 0).val (10 * M) ≤ 13 * M := by
        have hx := (x 0).isLt; have hL0 := hL 0; unfold pcd; split_ifs <;> omega
      have : 13 * M ≤ R * M := Nat.mul_le_mul_right _ (by omega)
      omega

theorem mem_boxM (z : PeriodicLatticeSite L) (s : ℕ) (x : PeriodicLatticeSite L) :
    x ∈ siteBox z s ↔ ∀ σ, ((x σ).val + 26 * M - (z σ).val) % (26 * M) < s := by
  simp only [siteBox, Set.mem_setOf_eq, hL]

/-- a box whose corner is `M · b` (block corner `b`) and side `c · M`: membership is block-window membership. -/
theorem mem_boxB (b : Fin 3 → ℕ) (hb : ∀ σ, b σ < 26) (c : ℕ) (x : PeriodicLatticeSite L) :
    x ∈ siteBox (mkM hL (fun σ => M * b σ) (fun σ => mul_lt26 M (b σ) hM (hb σ))) (c * M) ↔
      ∀ σ, inB (b σ) c ((x σ).val / M) := by
  rw [mem_boxM hM hL]
  refine forall_congr' (fun σ => ?_)
  rw [mkM_val]
  exact modKR M _ _ c hM (xlt hM hL x σ) (hb σ)

theorem shiftM_val (x : PeriodicLatticeSite L) (μ σ : Fin 3) :
    (periodicLatticeShift x μ σ).val = if σ = μ then ((x σ).val + 1) % (26 * M) else (x σ).val := by
  unfold periodicLatticeShift
  by_cases h : σ = μ
  · subst h
    rw [Function.update_self, if_pos rfl, Fin.val_add_one]
    have hl := (x σ).isLt
    have hL' := hL σ
    split_ifs with h1
    · rw [h1, Fin.val_last, hL']; exact (Nat.mod_self _).symm
    · have : (x σ).val ≠ L σ := fun h2 => h1 (Fin.ext (by rw [h2, Fin.val_last]))
      exact (Nat.mod_eq_of_lt (by omega)).symm
  · rw [Function.update_of_ne h, if_neg h]

/-- corners of the plaquette `(x; μ, ν)` in a block-cornered box. -/
theorem cornersB (b : Fin 3 → ℕ) (hb : ∀ σ, b σ < 26) (c : ℕ) (x : PeriodicLatticeSite L) {μ ν : Fin 3}
    (hμν : μ ≠ ν)
    (h : ∀ σ, inB (b σ) c ((x σ).val / M) ∧ ((σ = μ ∨ σ = ν) → inB (b σ) c ((((x σ).val + 1) % (26 * M)) / M))) :
    let z := mkM hL (fun σ => M * b σ) (fun σ => mul_lt26 M (b σ) hM (hb σ))
    x ∈ siteBox z (c * M) ∧ periodicLatticeShift x μ ∈ siteBox z (c * M) ∧
      periodicLatticeShift x ν ∈ siteBox z (c * M) ∧
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ siteBox z (c * M) := by
  intro z
  simp only [z, mem_boxB hM hL b hb c, shiftM_val hM hL]
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

theorem vtm_tb0 {c : PeriodicLatticeSite L} (hc : VCl M c) : c ∈ towerBj (VTM L M) 0 := by
  refine ⟨by rw [vtm_om0]; trivial, ?_⟩
  rw [show (0 : ℕ) + 1 = 1 from rfl, vtm_om1]; exact fun h => h hc

theorem vtm_tb1 {y : PeriodicLatticeSite L} (hy : y ∈ (VTM L M).Om 1) : y ∈ towerBj (VTM L M) 1 :=
  ⟨hy, by rw [vtm_omj (by norm_num)]; exact fun h => h⟩

theorem col_eq (v : ℕ) : v / (M * 2) = v / M / 2 := by rw [Nat.div_div_eq_div_mul]

/-- index-1 cube from excluded columns `W`. -/
theorem idx1M (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hμν : μ ≠ ν) {R : ℕ} (hR : 18 ≤ R)
    (W : Fin 3 → ℕ) (hW : ∀ σ, W σ < 13)
    (h2 : ∃ α β : Fin 3, α ≠ β ∧ W α = 0 ∧ W β = 0)
    (hav : ∀ σ, (x σ).val / M / 2 ≠ W σ ∧ ((σ = μ ∨ σ = ν) → (((x σ).val + 1) % (26 * M)) / M / 2 ≠ W σ)) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube 2 M 12 1 (VTM L M) sites j ∧
      x ∈ sites ∧ periodicLatticeShift x μ ∈ sites ∧ periodicLatticeShift x ν ∈ sites ∧
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ sites := by
  set b : Fin 3 → ℕ := fun σ => 2 * ((W σ + 1) % 13) with hbdef
  have hb : ∀ σ, b σ < 26 := fun σ => by simp only [hbdef]; omega
  set z := mkM hL (fun σ => M * b σ) (fun σ => mul_lt26 M (b σ) hM (hb σ)) with hz
  have hside : 12 * bigSide M 2 1 = 24 * M := by rw [bs1]; ring
  have hwin : ∀ a, a < 26 → ∀ σ, (inB (b σ) 24 a ↔ a / 2 ≠ W σ) := by
    intro a ha σ
    have := hW σ
    simp only [hbdef, inB]; omega
  have hsub : siteBox z (12 * bigSide M 2 1) ⊆ (VTM L M).Om 1 := by
    rw [hside]
    intro y hy
    rw [hz, mem_boxB hM hL b hb] at hy
    rw [vtm_om1]
    obtain ⟨α, β, hab, ha, hbb⟩ := h2
    have hA := (hwin _ (blk_lt M _ hM (xlt hM hL y α)) α).1 (hy α)
    have hB := (hwin _ (blk_lt M _ hM (xlt hM hL y β)) β).1 (hy β)
    rw [ha] at hA; rw [hbb] at hB
    show ¬ clumpQ ((y 0).val / (M * 2)) ((y 1).val / (M * 2)) ((y 2).val / (M * 2))
    rw [col_eq hM hL, col_eq hM hL, col_eq hM hL]
    exact two_nonzero (fun σ => (y σ).val / M / 2) α β hab hA hB
  have hc := cornersB hM hL b hb 24 x hμν (fun σ => by
    have hx := xlt hM hL x σ
    refine ⟨(hwin _ (blk_lt M _ hM hx) σ).2 (hav σ).1, fun h => (hwin _ ?_ σ).2 ((hav σ).2 h)⟩
    exact blk_lt M _ hM (Nat.mod_lt _ (by omega)))
  simp only at hc
  rw [← hside] at hc
  have hgrid : GridCorner (bigSide M 2 1) z := by
    intro σ
    rw [bs1]
    show (M * (2 * ((W σ + 1) % 13))) % (M * 2) = 0
    rw [show M * (2 * ((W σ + 1) % 13)) = (M * 2) * ((W σ + 1) % 13) by ring]
    exact Nat.mul_mod_right _ _
  refine ⟨siteBox z (12 * bigSide M 2 1), 1, ?_, hc⟩
  exact cube_isClass (vtm_admissible hM hL hR) (le_refl 1) hgrid hsub hc.1 (vtm_tb1 hM hL (hsub hc.1)) (by omega)

/-- block tables for index-0 boxes. -/
def zsb (t : ℕ) : ℕ :=
  if t = 0 then 15 else if t ≤ 11 then 1 else if t = 12 then 2 else if t ≤ 23 then 13 else if t = 24 then 14 else 15

def cvb (t : ℕ) : ℕ := if t = 0 then 15 else if t ≤ 12 then 12 else if t ≤ 23 then 13 else if t = 24 then 14 else 15

omit hM hL in
theorem zsb_table (t : ℕ) (ht : t < 26) :
    inB (zsb t) 12 t ∧ inB (zsb t) 12 (cvb t) ∧ (t ≠ 0 → inB (zsb t) 12 ((t + 1) % 26)) ∧ zsb t < 26 ∧
      cvb t < 26 ∧ (cvb t / 2 = 6 ∨ cvb t / 2 = 7) := by
  unfold inB zsb cvb; split_ifs <;> omega

def inRb (a : ℕ) : Prop := inB 24 12 a

/-- index-0 cube with a clump along axis `γ`. -/
theorem idx0M (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hμν : μ ≠ ν) {R : ℕ} (hR : 18 ≤ R) (γ : Fin 3)
    (hγ : (γ = μ ∨ γ = ν) → ((((x γ).val + 1) % (26 * M)) / M = (x γ).val / M ∨ (x γ).val / M ≠ 0))
    (hRR : ∀ σ, σ ≠ γ → inRb ((x σ).val / M) ∧ ((σ = μ ∨ σ = ν) → inRb ((((x σ).val + 1) % (26 * M)) / M))) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube 2 M 12 1 (VTM L M) sites j ∧
      x ∈ sites ∧ periodicLatticeShift x μ ∈ sites ∧ periodicLatticeShift x ν ∈ sites ∧
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ sites := by
  classical
  set t : ℕ := (x γ).val / M with ht
  have htl : t < 26 := blk_lt M _ hM (xlt hM hL x γ)
  obtain ⟨T1, T2, T3, T4, T5, T6⟩ := zsb_table t htl
  set b : Fin 3 → ℕ := fun σ => if σ = γ then zsb t else 24 with hbdef
  have hb : ∀ σ, b σ < 26 := fun σ => by simp only [hbdef]; split_ifs <;> omega
  set cb : Fin 3 → ℕ := fun σ => if σ = γ then cvb t else 0 with hcbdef
  have hcb : ∀ σ, M * cb σ < 26 * M := fun σ => by
    have : cb σ < 26 := by simp only [hcbdef]; split_ifs <;> omega
    nlinarith
  set z := mkM hL (fun σ => M * b σ) (fun σ => mul_lt26 M (b σ) hM (hb σ)) with hz
  set c := mkM hL (fun σ => M * cb σ) hcb with hc
  have hside : 12 * bigSide M 2 0 = 12 * M := by rw [bs0]
  have hcor := cornersB hM hL b hb 12 x hμν (fun σ => by
    by_cases hσ : σ = γ
    · subst hσ
      simp only [hbdef, if_pos rfl]
      refine ⟨T1, fun h => ?_⟩
      have hsh := shift_blk M _ hM (xlt hM hL x σ)
      rcases hγ h with h1 | h1
      · rw [h1]; exact T1
      · rcases hsh with h2 | h2
        · rw [h2]; exact T1
        · rw [h2]; exact T3 h1
    · simp only [hbdef, if_neg hσ]
      exact ⟨(hRR σ hσ).1, fun h => (hRR σ hσ).2 h⟩)
  simp only at hcor
  rw [← hside] at hcor
  have hcbox : c ∈ siteBox z (12 * bigSide M 2 0) := by
    rw [hside, hz, mem_boxB hM hL b hb]
    intro σ
    rw [hc, mkM_val, Nat.mul_div_cancel_left _ hM]
    simp only [hbdef, hcbdef]
    split_ifs
    · exact T2
    · unfold inB; norm_num
  have hcl : VCl M c := by
    show clumpQ ((c 0).val / (M * 2)) ((c 1).val / (M * 2)) ((c 2).val / (M * 2))
    rw [col_eq hM hL, col_eq hM hL, col_eq hM hL, hc, mkM_val, mkM_val, mkM_val,
      Nat.mul_div_cancel_left _ hM, Nat.mul_div_cancel_left _ hM, Nat.mul_div_cancel_left _ hM]
    simp only [hcbdef]
    unfold clumpQ
    fin_cases γ <;> simp <;> omega
  have hgrid : GridCorner (bigSide M 2 0) z := by
    intro σ
    rw [bs0]
    show (M * b σ) % M = 0
    exact Nat.mul_mod_right _ _
  have hsub : siteBox z (12 * bigSide M 2 0) ⊆ (VTM L M).Om 0 := by rw [vtm_om0]; exact Set.subset_univ _
  refine ⟨siteBox z (12 * bigSide M 2 0), 0, ?_, hcor⟩
  exact cube_isClass (vtm_admissible hM hL hR) (Nat.zero_le 1) hgrid hsub hcbox (vtm_tb0 hM hL hcl) (by omega)

/-- **every plaquette of `VTM` lies in one class cube.** -/
theorem vtm_plaq_cover {R : ℕ} (hR : 18 ≤ R) (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hμν : μ ≠ ν) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube 2 M 12 1 (VTM L M) sites j ∧
      x ∈ sites ∧ periodicLatticeShift x μ ∈ sites ∧ periodicLatticeShift x ν ∈ sites ∧
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ sites := by
  classical
  set a : Fin 3 → ℕ := fun σ => (x σ).val / M with hadef
  set a' : Fin 3 → ℕ := fun σ => (((x σ).val + 1) % (26 * M)) / M with ha'def
  have hal : ∀ σ, a σ < 26 := fun σ => blk_lt M _ hM (xlt hM hL x σ)
  have hsh : ∀ σ, a' σ = a σ ∨ a' σ = (a σ + 1) % 26 := fun σ => shift_blk M _ hM (xlt hM hL x σ)
  set Z : Fin 3 → Prop := fun σ => a σ / 2 = 0 ∨ ((σ = μ ∨ σ = ν) ∧ a' σ / 2 = 0) with hZ
  have hZR : ∀ σ, Z σ → inRb (a σ) ∧ inRb (a' σ) := by
    intro σ hσ
    have := hal σ
    have := hsh σ
    unfold inRb inB
    rcases hσ with h | ⟨-, h⟩ <;> omega
  by_cases hA : ∃ α β : Fin 3, α ≠ β ∧ ¬ Z α ∧ ¬ Z β
  · refine idx1M hM hL x hμν hR (fun σ => if Z σ then (a σ / 2 + 6) % 13 else 0)
      (fun σ => by split_ifs <;> omega) ?_ (fun σ => ?_)
    · obtain ⟨α, β, hab, ha, hb⟩ := hA
      exact ⟨α, β, hab, by rw [if_neg ha], by rw [if_neg hb]⟩
    · have := hal σ
      have h3 := hsh σ
      by_cases hσ : Z σ
      · rw [if_pos hσ]
        refine ⟨by simp only [hadef]; omega, fun _ => ?_⟩
        show a' σ / 2 ≠ (a σ / 2 + 6) % 13
        omega
      · rw [if_neg hσ]
        simp only [hZ, not_or, not_and] at hσ
        exact ⟨hσ.1, fun h => hσ.2 h⟩
  · push_neg at hA
    obtain ⟨l, hl1, hl2⟩ := third_axis μ ν
    by_cases hRR : (inRb (a μ) ∧ inRb (a' μ)) ∧ (inRb (a ν) ∧ inRb (a' ν))
    · refine idx0M hM hL x hμν hR l (fun h => (h.elim (fun h' => absurd h' hl1) (fun h' => absurd h' hl2))) ?_
      intro σ hσ
      rcases axes_cover hμν hl1 hl2 hσ with h | h <;> subst h
      · exact ⟨hRR.1.1, fun _ => hRR.1.2⟩
      · exact ⟨hRR.2.1, fun _ => hRR.2.2⟩
    · have hex : ∃ σ₀ : Fin 3, (σ₀ = μ ∨ σ₀ = ν) ∧ ¬ (inRb (a σ₀) ∧ inRb (a' σ₀)) := by
        by_cases h1 : inRb (a μ) ∧ inRb (a' μ)
        · exact ⟨ν, Or.inr rfl, fun h2 => hRR ⟨h1, h2⟩⟩
        · exact ⟨μ, Or.inl rfl, h1⟩
      obtain ⟨σ₀, hσ₀, hout⟩ := hex
      have hnZ : ¬ Z σ₀ := fun h => hout (hZR σ₀ h)
      refine idx0M hM hL x hμν hR σ₀ (fun _ => Or.inr ?_) (fun σ hσ => ?_)
      · intro h1
        apply hnZ
        left
        show (x σ₀).val / M / 2 = 0
        rw [h1]
      · have hZσ : Z σ := by
          by_contra hn
          exact hn (hA σ₀ σ (Ne.symm hσ) hnZ)
        exact ⟨(hZR σ hZσ).1, fun _ => (hZR σ hZσ).2⟩

theorem vtm_coversp {R : ℕ} (hR : 18 ≤ R) : CoversOm0p 2 M 12 1 (VTM L M) := by
  refine ⟨fun x _ => ?_, fun p _ => ?_⟩
  · obtain ⟨sites, j, hq, hx, -⟩ := vtm_plaq_cover hM hL hR x (μ := 0) (ν := 1) (by decide)
    exact ⟨sites, j, hq, hx⟩
  · obtain ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩ := p
    obtain ⟨sites, j, hq, h1, h2, h3, h4⟩ := vtm_plaq_cover hM hL hR x (μ := μ) (ν := ν) (ne_of_lt hμν)
    refine ⟨sites, j, hq, fun e he => ?_⟩
    simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨h1, h2⟩
    · exact ⟨h2, h4⟩
    · exact ⟨h3, by rw [shift_comm]; exact h4⟩
    · exact ⟨h1, h3⟩

/-- no class cube contains, along every axis `σ`, a site in block `0` and a site in block `1`. -/
theorem vtm_no_cube_of (sites : Set (PeriodicLatticeSite L)) (i : ℕ) (hq : IsClassCube 2 M 12 1 (VTM L M) sites i)
    (P Q : Fin 3 → PeriodicLatticeSite L)
    (hP : ∀ σ, P σ ∈ sites ∧ ((P σ) σ).val / M = 0) (hQ : ∀ σ, Q σ ∈ sites ∧ ((Q σ) σ).val / M = 1) : False := by
  obtain ⟨⟨hik, ⟨z, hgrid, hz⟩, hsub, ⟨c, hcs, hcB⟩⟩, -⟩ := hq
  have hzM : ∀ σ, (z σ).val % M = 0 := by
    intro σ
    have h := hgrid σ
    rcases Nat.lt_or_ge i 1 with h0 | h1
    · have hi : i = 0 := by omega
      subst hi; rw [bs0] at h; exact h
    · have hi : i = 1 := by omega
      subst hi; rw [bs1] at h
      exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.trans (Dvd.intro 2 rfl) (Nat.dvd_of_mod_eq_zero h))
  set b : Fin 3 → ℕ := fun σ => (z σ).val / M with hbdef
  have hb : ∀ σ, b σ < 26 := fun σ => blk_lt M _ hM (xlt hM hL z σ)
  have hzb : z = mkM hL (fun σ => M * b σ) (fun σ => mul_lt26 M (b σ) hM (hb σ)) := by
    funext σ
    apply Fin.ext
    rw [mkM_val]
    have := Nat.div_add_mod (z σ).val M
    rw [hzM σ] at this
    simp only [hbdef]; omega
  have hmem : ∀ c', ∀ y, y ∈ siteBox z (c' * M) → ∀ σ, inB (b σ) c' ((y σ).val / M) := by
    intro c' y hy
    rw [hzb, mem_boxB hM hL b hb] at hy
    exact hy
  rcases Nat.lt_or_ge i 1 with h0 | h1
  · have hi : i = 0 := by omega
    subst hi
    rw [bs0] at hz
    have hcl : VCl M c := by
      have h := hcB.2
      exact Classical.byContradiction (fun hn => h (by rw [show (0 : ℕ) + 1 = 1 from rfl, vtm_om1]; exact hn))
    have key : ∀ σ, ((c σ).val / M / 2 = 6 ∨ (c σ).val / M / 2 = 7) → False := by
      intro σ hσ
      have a1 := hmem 12 _ (hz ▸ (hP σ).1) σ
      have a2 := hmem 12 _ (hz ▸ (hQ σ).1) σ
      have a3 := hmem 12 _ (hz ▸ hcs) σ
      have p1 := (hP σ).2
      have q1 := (hQ σ).2
      have bl := hb σ
      rw [p1] at a1; rw [q1] at a2
      unfold inB at a1 a2 a3
      omega
    unfold VCl clumpQ at hcl
    rw [col_eq hM hL, col_eq hM hL, col_eq hM hL] at hcl
    rcases hcl with ⟨h, -, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩
    · exact key 0 h
    · exact key 1 h
    · exact key 2 h
  · have hi : i = 1 := by omega
    subst hi
    rw [bs1, show 12 * (M * 2) = 24 * M by ring] at hz
    have hbe : ∀ σ, b σ % 2 = 0 := by
      intro σ
      have h := hgrid σ
      rw [bs1] at h
      have h2 : M * 2 ∣ (z σ).val := Nat.dvd_of_mod_eq_zero h
      obtain ⟨q, hq⟩ := h2
      simp only [hbdef]; rw [hq, show M * 2 * q = M * (2 * q) by ring, Nat.mul_div_cancel_left _ hM]; omega
    have hW : ∀ σ, (b σ / 2 + 12) % 13 ≠ 0 := by
      intro σ
      have a1 := hmem 24 _ (hz ▸ (hP σ).1) σ
      rw [(hP σ).2] at a1
      have := (win24 _ 0 (hb σ) (hbe σ) (by norm_num)).1 a1
      simpa using this.symm
    have hsub1 : ∀ y, y ∈ sites → ¬ VCl M y := by
      intro y hy
      rcases hsub hy with h | h
      · have h1 := h.1; rw [vtm_om1] at h1; exact h1
      · have h1 := h.1; rw [vtm_omj (by norm_num)] at h1; exact h1.elim
    have hin : ∀ q : ℕ, (hq : q < 26) → q / 2 ≠ (b 0 / 2 + 12) % 13 →
        mkM hL (fun σ => M * (if σ = 0 then q else 0)) (fun σ => by split_ifs <;> nlinarith) ∈ sites := by
      intro q hq hqW
      rw [hz]
      have := mem_boxB hM hL b hb 24 (mkM hL (fun σ => M * (if σ = 0 then q else 0)) (fun σ => by split_ifs <;> nlinarith))
      rw [← hzb] at this
      rw [this]
      intro σ
      rw [mkM_val, Nat.mul_div_cancel_left _ hM]
      by_cases h : σ = 0
      · subst h; simp only [if_pos rfl]; exact (win24 _ _ (hb 0) (hbe 0) hq).2 hqW
      · simp only [if_neg h]
        exact (win24 _ 0 (hb σ) (hbe σ) (by norm_num)).2 (by simpa using (hW σ).symm)
    have hcl : ∀ q : ℕ, (hq : q < 26) → (q / 2 = 6 ∨ q / 2 = 7) →
        VCl M (mkM hL (fun σ => M * (if σ = 0 then q else 0)) (fun σ => by split_ifs <;> nlinarith)) := by
      intro q hq h
      show clumpQ _ _ _
      rw [col_eq hM hL, col_eq hM hL, col_eq hM hL, mkM_val, mkM_val, mkM_val,
        Nat.mul_div_cancel_left _ hM, Nat.mul_div_cancel_left _ hM, Nat.mul_div_cancel_left _ hM]
      unfold clumpQ
      simp
      omega
    by_cases h6 : (b 0 / 2 + 12) % 13 = 6
    · exact hsub1 _ (hin 14 (by norm_num) (by omega)) (hcl 14 (by norm_num) (by norm_num))
    · exact hsub1 _ (hin 12 (by norm_num) (by omega)) (hcl 12 (by norm_num) (by norm_num))

theorem vtm_star_no_cube :
    ¬ ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube 2 M 12 1 (VTM L M) sites i ∧
      x0M hM hL ∈ sites ∧ ∀ σ, periodicLatticeShift (x0M hM hL) σ ∈ sites := by
  rintro ⟨sites, i, hq, hx, hs⟩
  refine vtm_no_cube_of hM hL sites i hq (fun _ => x0M hM hL) (fun σ => periodicLatticeShift (x0M hM hL) σ)
    (fun σ => ⟨hx, ?_⟩) (fun σ => ⟨hs σ, ?_⟩)
  · show (mkM hL (fun _ => M - 1) _ σ).val / M = 0
    rw [mkM_val]; exact Nat.div_eq_of_lt (by omega)
  · rw [shiftM_val hM hL, if_pos rfl]
    show ((mkM hL (fun _ => M - 1) _ σ).val + 1) % (26 * M) / M = 1
    rw [mkM_val, show M - 1 + 1 = M by omega, Nat.mod_eq_of_lt (by omega), Nat.div_self hM]

theorem vtm_stencil_no_cube (μ : Fin 3) :
    ¬ ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube 2 M 12 1 (VTM L M) sites i ∧
      ∀ ν : Fin 3, ν ≠ μ →
        CurlReads sites (AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack (x0M hM hL) ν) ν μ ∧
        CurlReads sites (x0M hM hL) ν μ := by
  rintro ⟨sites, i, hq, hst⟩
  obtain ⟨ν0, hν0, -⟩ := third_axis μ μ
  have hb : ∀ ν, ν ≠ μ → CubeBond sites ((x0M hM hL, μ) : Bond L) ∧ CubeBond sites ((x0M hM hL, ν) : Bond L) :=
    fun ν hν => ⟨(hst ν hν).2.2.1, (hst ν hν).2.2.2.2⟩
  refine vtm_star_no_cube hM hL ⟨sites, i, hq, (hb ν0 hν0).1.1, fun σ => ?_⟩
  by_cases h : σ = μ
  · subst h; exact (hb ν0 hν0).1.2
  · exact (hb σ h).2.2

end main

/-- **the corner, in the headline's geometry**: every even `M ≥ 2`, every `R ≥ 18`, unit torus `13 M`. -/
theorem vtm_corner {M R : ℕ} (hM : 0 < M) (hM2 : 2 ∣ M) (hR : 18 ≤ R) {Lu : PeriodicLatticeExtent}
    (hLu : ∀ μ, Lu μ + 1 = 13 * M) :
    TorusOK 2 M Lu ∧ Admissible 2 M R 1 (VTM (scaleUp 2 1 Lu) M) ∧ CoversOm0p 2 M 12 1 (VTM (scaleUp 2 1 Lu) M) ∧
      ∃ x : PeriodicLatticeSite (scaleUp 2 1 Lu),
        ¬ ∃ (sites : Set (PeriodicLatticeSite (scaleUp 2 1 Lu))) (i : ℕ),
          IsClassCube 2 M 12 1 (VTM (scaleUp 2 1 Lu) M) sites i ∧ x ∈ sites ∧ ∀ σ, periodicLatticeShift x σ ∈ sites := by
  have hL : ∀ μ, scaleUp 2 1 Lu μ + 1 = 26 * M := by
    intro μ; unfold scaleUp; rw [hLu μ]; have : 1 ≤ 13 * M * 2 ^ 1 := by omega
    omega
  refine ⟨⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩, vtm_admissible hM hL hR, vtm_coversp hM hL hR,
    x0M hM hL, vtm_star_no_cube hM hL⟩
  · rw [hLu μ]; exact Dvd.dvd.mul_left hM2 13
  · rw [hLu μ]; omega
  · rw [hLu μ]; exact Dvd.intro_left 13 rfl

end AdalyFormal.M2Route

#print axioms AdalyFormal.M2Route.modKR
#print axioms AdalyFormal.M2Route.win24
#print axioms AdalyFormal.M2Route.mul_lt26
#print axioms AdalyFormal.M2Route.blk_lt
#print axioms AdalyFormal.M2Route.shift_blk
#print axioms AdalyFormal.M2Route.vtm_om0
#print axioms AdalyFormal.M2Route.vtm_om1
#print axioms AdalyFormal.M2Route.vtm_omj
#print axioms AdalyFormal.M2Route.bs0
#print axioms AdalyFormal.M2Route.bs1
#print axioms AdalyFormal.M2Route.mkM_val
#print axioms AdalyFormal.M2Route.x0M
#print axioms AdalyFormal.M2Route.mkM
#print axioms AdalyFormal.M2Route.VCl
#print axioms AdalyFormal.M2Route.VTM
#print axioms AdalyFormal.M2Route.xlt
#print axioms AdalyFormal.M2Route.vtm_admissible
#print axioms AdalyFormal.M2Route.mem_boxM
#print axioms AdalyFormal.M2Route.mem_boxB
#print axioms AdalyFormal.M2Route.shiftM_val
#print axioms AdalyFormal.M2Route.cornersB
#print axioms AdalyFormal.M2Route.vtm_tb0
#print axioms AdalyFormal.M2Route.vtm_tb1
#print axioms AdalyFormal.M2Route.col_eq
#print axioms AdalyFormal.M2Route.idx1M
#print axioms AdalyFormal.M2Route.zsb_table
#print axioms AdalyFormal.M2Route.idx0M
#print axioms AdalyFormal.M2Route.vtm_plaq_cover
#print axioms AdalyFormal.M2Route.vtm_coversp
#print axioms AdalyFormal.M2Route.vtm_no_cube_of
#print axioms AdalyFormal.M2Route.vtm_star_no_cube
#print axioms AdalyFormal.M2Route.vtm_stencil_no_cube
#print axioms AdalyFormal.M2Route.vtm_corner
