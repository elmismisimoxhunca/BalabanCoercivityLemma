import LF3
import LF5a

/-!
# LF5b -- cell corners inside a big block, indexed by the cube `[0,ell)³`

`iota n Y i = Y + n i` (cyclic), `idx n N y = (y - corner N y)/n`.  For `Y` an `N`-corner (`N = ell^{j+1}`, `n = ell^j`):
`iota` is a bijection from the cube onto the `n`-corners of the big block of `Y` (`iota_idx`, `idx_iota`, `iota_inj`),
`shift_iota` (an `n`-step is a cube step), `sum_stepBlock_cube` (the composite average over the big block is the cube
average of the cell values).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.LemIFlat

open AdalyFormal.Target.ClayStatement
open AdalyFormal.M1Patch (corner corner_dvd)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf inBlock)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

/-- the cell corner with cube index `i` in the big block at `Y`. -/
def iota (n : ℕ) (Y : PeriodicLatticeSite L) (i : Fin 3 → ℕ) : PeriodicLatticeSite L :=
  fun μ => ⟨((Y μ).val + n * i μ) % (L μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- the cube index of a corner. -/
def idx (n N : ℕ) (y : PeriodicLatticeSite L) : Fin 3 → ℕ := fun μ => ((y μ).val - (corner N y μ).val) / n

theorem iota_val_mod (n : ℕ) (Y : PeriodicLatticeSite L) (i : Fin 3 → ℕ) (μ : Fin 3) :
    (iota n Y i μ).val = ((Y μ).val + n * i μ) % (L μ + 1) := rfl

/-- an `n`-step from a cube corner is a cube step (no hypothesis: both sides are taken mod `L+1`). -/
theorem shift_iota (n : ℕ) (Y : PeriodicLatticeSite L) (i : Fin 3 → ℕ) (ν : Fin 3) :
    coarseShift (iota n Y i) n ν = iota n Y (Function.update i ν (i ν + 1)) := by
  funext μ
  by_cases h : μ = ν
  · subst h
    apply Fin.ext
    rw [coarseShift_val_eq, iota_val_mod, iota_val_mod, Function.update_self, Nat.mod_add_mod]
    congr 1; ring
  · rw [coarseShift_apply_ne _ _ _ _ h]
    apply Fin.ext
    rw [iota_val_mod, iota_val_mod, Function.update_of_ne h]

section
variable (ell j : ℕ) (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1)
include hell hdvd

theorem fit_big (Y : PeriodicLatticeSite L) (hY : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val) (μ : Fin 3) :
    (Y μ).val + ell ^ (j + 1) ≤ L μ + 1 := by
  obtain ⟨a, ha⟩ := hY μ
  obtain ⟨b, hb⟩ := hdvd μ
  have hlt : ell ^ (j + 1) * a < ell ^ (j + 1) * b := by rw [← ha, ← hb]; exact (Y μ).isLt
  have hab : a + 1 ≤ b := Nat.lt_of_mul_lt_mul_left hlt
  have h2 := Nat.mul_le_mul_left (ell ^ (j + 1)) hab
  rw [Nat.mul_succ] at h2
  rw [ha, hb]; omega

theorem iota_lt (Y : PeriodicLatticeSite L) (hY : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val) (i : Fin 3 → ℕ)
    (hi : i ∈ cube ell) (μ : Fin 3) : (Y μ).val + ell ^ j * i μ < (Y μ).val + ell ^ (j + 1) := by
  have h1 : i μ < ell := (mem_cube ell i).mp hi μ
  have h2 : ell ^ j * i μ < ell ^ j * ell := Nat.mul_lt_mul_of_pos_left h1 (pow_pos hell j)
  rw [← pow_succ] at h2
  omega

theorem iota_val (Y : PeriodicLatticeSite L) (hY : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val) (i : Fin 3 → ℕ)
    (hi : i ∈ cube ell) (μ : Fin 3) : (iota (ell ^ j) Y i μ).val = (Y μ).val + ell ^ j * i μ := by
  rw [iota_val_mod]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (iota_lt ell j hell hdvd Y hY i hi μ) (fit_big ell j hell hdvd Y hY μ))

theorem iota_mem_block (Y : PeriodicLatticeSite L) (hY : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val) (i : Fin 3 → ℕ)
    (hi : i ∈ cube ell) : iota (ell ^ j) Y i ∈ blockOf Y (ell ^ (j + 1)) := by
  rw [mem_blockOf]
  intro μ
  rw [iota_val ell j hell hdvd Y hY i hi μ]
  exact ⟨Nat.le_add_right _ _, iota_lt ell j hell hdvd Y hY i hi μ⟩

theorem iota_onLat (Y : PeriodicLatticeSite L) (hY : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val) (i : Fin 3 → ℕ)
    (hi : i ∈ cube ell) (μ : Fin 3) : ell ^ j ∣ (iota (ell ^ j) Y i μ).val := by
  rw [iota_val ell j hell hdvd Y hY i hi μ]
  exact Nat.dvd_add ((pow_dvd_pow ell (Nat.le_succ j)).trans (hY μ)) (Dvd.intro _ rfl)

theorem corner_iota (Y : PeriodicLatticeSite L) (hY : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val) (i : Fin 3 → ℕ)
    (hi : i ∈ cube ell) : corner (ell ^ (j + 1)) (iota (ell ^ j) Y i) = Y :=
  (mem_blockOf_iff_corner (pow_pos hell (j + 1)) Y _ hY).mp (iota_mem_block ell j hell hdvd Y hY i hi)

theorem idx_mem_cube (y : PeriodicLatticeSite L) (hy : ∀ μ : Fin 3, ell ^ j ∣ (y μ).val) :
    idx (ell ^ j) (ell ^ (j + 1)) y ∈ cube ell := by
  rw [mem_cube]
  intro μ
  unfold idx
  rw [corner_val]
  have hn : 0 < ell ^ j := pow_pos hell j
  have hmod : (y μ).val - (y μ).val / ell ^ (j + 1) * ell ^ (j + 1) = (y μ).val % ell ^ (j + 1) := by
    rw [Nat.mod_eq_sub_mul_div, Nat.mul_comm]
  rw [hmod]
  have hlt : (y μ).val % ell ^ (j + 1) < ell ^ j * ell := by
    rw [← pow_succ]; exact Nat.mod_lt _ (pow_pos hell _)
  exact (Nat.div_lt_iff_lt_mul hn).mpr (by rw [Nat.mul_comm]; exact hlt)

theorem iota_idx (y : PeriodicLatticeSite L) (hy : ∀ μ : Fin 3, ell ^ j ∣ (y μ).val) :
    iota (ell ^ j) (corner (ell ^ (j + 1)) y) (idx (ell ^ j) (ell ^ (j + 1)) y) = y := by
  funext μ
  apply Fin.ext
  rw [iota_val_mod]
  unfold idx
  have hc : (corner (ell ^ (j + 1)) y μ).val ≤ (y μ).val := by rw [corner_val]; exact Nat.div_mul_le_self _ _
  have hdv : ell ^ j ∣ (y μ).val - (corner (ell ^ (j + 1)) y μ).val :=
    Nat.dvd_sub (hy μ) ((pow_dvd_pow ell (Nat.le_succ j)).trans (corner_dvd _ y μ))
  rw [Nat.mul_div_cancel' hdv, Nat.add_sub_cancel' hc, Nat.mod_eq_of_lt (y μ).isLt]

theorem idx_iota (Y : PeriodicLatticeSite L) (hY : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val) (i : Fin 3 → ℕ)
    (hi : i ∈ cube ell) : idx (ell ^ j) (ell ^ (j + 1)) (iota (ell ^ j) Y i) = i := by
  funext μ
  unfold idx
  rw [corner_iota ell j hell hdvd Y hY i hi, iota_val ell j hell hdvd Y hY i hi μ, Nat.add_sub_cancel_left,
    Nat.mul_div_cancel_left _ (pow_pos hell j)]

theorem iota_inj (Y Y' : PeriodicLatticeSite L) (hY : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val)
    (hY' : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y' μ).val) (i i' : Fin 3 → ℕ) (hi : i ∈ cube ell) (hi' : i' ∈ cube ell)
    (h : iota (ell ^ j) Y i = iota (ell ^ j) Y' i') : Y = Y' ∧ i = i' := by
  have h1 : Y = Y' := by
    rw [← corner_iota ell j hell hdvd Y hY i hi, h, corner_iota ell j hell hdvd Y' hY' i' hi']
  refine ⟨h1, ?_⟩
  rw [← idx_iota ell j hell hdvd Y hY i hi, h, idx_iota ell j hell hdvd Y' hY' i' hi']

/-- the big block of `Y` is the union of the cells `iota Y i`. -/
theorem sum_stepBlock_cube {M : Type*} [AddCommMonoid M] (Y : PeriodicLatticeSite L)
    (hY : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val) (g : PeriodicLatticeSite L → M) :
    ∑ x ∈ stepBlockOf Y (ell ^ j) ell, g x = ∑ i ∈ cube ell, g (iota (ell ^ j) Y i) := by
  classical
  have hn : 0 < ell ^ j := pow_pos hell j
  symm
  refine Finset.sum_nbij' (fun i => iota (ell ^ j) Y i)
    (fun x => fun μ => ((x μ).val - (Y μ).val) / ell ^ j) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have hi' : i ∈ cube ell := hi
    rw [mem_stepBlockOf]
    intro μ
    rw [iota_val ell j hell hdvd Y hY i hi' μ]
    refine ⟨Nat.le_add_right _ _, ?_, ⟨i μ, by omega⟩⟩
    have := iota_lt ell j hell hdvd Y hY i hi' μ
    rw [pow_succ] at this; exact this
  · intro x hx
    rw [mem_stepBlockOf] at hx
    show (fun μ => ((x μ).val - (Y μ).val) / ell ^ j) ∈ cube ell
    rw [mem_cube]
    intro μ
    obtain ⟨h1, h2, ⟨p, hp⟩⟩ := hx μ
    rw [hp, Nat.mul_div_cancel_left _ hn]
    have : ell ^ j * p < ell ^ j * ell := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  · intro i hi
    have hi' : i ∈ cube ell := hi
    funext μ
    show ((iota (ell ^ j) Y i μ).val - (Y μ).val) / ell ^ j = i μ
    rw [iota_val ell j hell hdvd Y hY i hi' μ, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hn]
  · intro x hx
    rw [mem_stepBlockOf] at hx
    funext μ
    obtain ⟨h1, h2, ⟨p, hp⟩⟩ := hx μ
    apply Fin.ext
    rw [iota_val_mod]
    show ((Y μ).val + ell ^ j * (((x μ).val - (Y μ).val) / ell ^ j)) % (L μ + 1) = (x μ).val
    rw [hp, Nat.mul_div_cancel_left _ hn, ← hp, Nat.add_sub_cancel' h1, Nat.mod_eq_of_lt (x μ).isLt]
  · intro i _; rfl

end

#print axioms shift_iota
#print axioms iota_val
#print axioms corner_iota
#print axioms idx_mem_cube
#print axioms iota_idx
#print axioms idx_iota
#print axioms iota_inj
#print axioms sum_stepBlock_cube

#print axioms iota_val_mod
#print axioms fit_big
#print axioms iota_lt
#print axioms iota_mem_block
#print axioms iota_onLat

end AdalyFormal.LemIFlat
