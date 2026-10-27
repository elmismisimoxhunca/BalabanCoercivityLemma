import M2B4
import M1B

/-!
# M2B5a -- offsets from a box corner and their behaviour under the periodic shift (m2_bridge_20261014, Layer B1)

`offc z x σ = ((x σ).val + (N_σ - z_σ)) % N_σ` (`N_σ = L σ + 1`) is the offset of `x_σ` from the box corner `z_σ`; `x ∈ siteBox z s ↔ ∀ σ, offc z x σ < s`.
`offc_shift` / `offc_shiftBack` : the offset vector of `periodicLatticeShift x μ` / `periodicLatticeShiftBack x μ` is `Function.update (offc z x) μ ((o+1) % N)` /
`... ((o + (N-1)) % N)`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Bridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

variable {L : PeriodicLatticeExtent}

/-- offset of `x_σ` from the corner `z_σ`. -/
def offc (z x : PeriodicLatticeSite L) (σ : Fin 3) : ℕ := ((x σ).val + (L σ + 1 - (z σ).val)) % (L σ + 1)

theorem offc_lt (z x : PeriodicLatticeSite L) (σ : Fin 3) : offc z x σ < L σ + 1 := Nat.mod_lt _ (Nat.succ_pos _)

theorem mem_siteBox_offc (z x : PeriodicLatticeSite L) (s : ℕ) : x ∈ siteBox z s ↔ ∀ σ, offc z x σ < s := by
  unfold siteBox offc
  simp only [Set.mem_setOf_eq]
  constructor <;> intro h σ <;> have := h σ <;> have hz := (z σ).isLt <;> have e : (x σ).val + (L σ + 1) - (z σ).val = (x σ).val + (L σ + 1 - (z σ).val) := by omega
  · rw [← e]; exact this
  · rw [e]; exact this

theorem fin_add_one_val {n : ℕ} (hn : 2 ≤ n + 1) (a : Fin (n + 1)) : ((a + 1 : Fin (n + 1)) : ℕ) = ((a : ℕ) + 1) % (n + 1) := by
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n + 1)]

theorem fin_sub_one_val {n : ℕ} (hn : 2 ≤ n + 1) (a : Fin (n + 1)) : ((a - 1 : Fin (n + 1)) : ℕ) = ((a : ℕ) + n) % (n + 1) := by
  rw [Fin.coe_sub, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n + 1)]
  rw [add_comm]
  congr 1

theorem offc_shift_same (hL : ∀ σ, 1 ≤ L σ) (z x : PeriodicLatticeSite L) (μ : Fin 3) :
    offc z (periodicLatticeShift x μ) μ = (offc z x μ + 1) % (L μ + 1) := by
  have h := fin_add_one_val (n := L μ) (by have := hL μ; omega) (x μ)
  unfold offc periodicLatticeShift
  simp only [Function.update_self]
  rw [h, Nat.mod_add_mod, Nat.mod_add_mod]
  congr 1
  omega

theorem offc_shift_ne (z x : PeriodicLatticeSite L) {μ σ : Fin 3} (h : σ ≠ μ) :
    offc z (periodicLatticeShift x μ) σ = offc z x σ := by
  unfold offc periodicLatticeShift
  rw [Function.update_of_ne h]

theorem offc_shiftBack_same (hL : ∀ σ, 1 ≤ L σ) (z x : PeriodicLatticeSite L) (μ : Fin 3) :
    offc z (periodicLatticeShiftBack x μ) μ = (offc z x μ + L μ) % (L μ + 1) := by
  have h := fin_sub_one_val (n := L μ) (by have := hL μ; omega) (x μ)
  unfold offc periodicLatticeShiftBack
  simp only [Function.update_self]
  rw [h, Nat.mod_add_mod, Nat.mod_add_mod]
  congr 1
  omega

theorem offc_shiftBack_ne (z x : PeriodicLatticeSite L) {μ σ : Fin 3} (h : σ ≠ μ) :
    offc z (periodicLatticeShiftBack x μ) σ = offc z x σ := by
  unfold offc periodicLatticeShiftBack
  rw [Function.update_of_ne h]

end AdalyFormal.M2Bridge

#print axioms AdalyFormal.M2Bridge.mem_siteBox_offc
#print axioms AdalyFormal.M2Bridge.offc_shift_same
#print axioms AdalyFormal.M2Bridge.offc_shiftBack_same
