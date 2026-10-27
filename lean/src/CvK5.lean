import CvC1
import CvK4

/-!
# CvK5 -- the local test vector in the chain (lane cover_jacobi_20261016)

`e1vec C L n`: the vector `locVec (L-1) (C + L - 1 - x)` on the row slices `x in [C, C+L)`, zero elsewhere.  For `n = C + L + r`, `C = K + 1`, `L = k + 3`:
`qF C c (e1vec ..) = locEnergy (k+2) c` for every `c` (the chain energy of the zero-extended vector equals the abstract energy of CvC1), hence at `c = cLoc (k+2)` it is NEGATIVE.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open Finset

/-- the zero-extended local vector. -/
noncomputable def e1vec (C L n : ℕ) : Fin n → ℝ :=
  fun x => if C ≤ x.val ∧ x.val < C + L then locVec (L - 1) (C + L - 1 - x.val) else 0

theorem ex_e1vec (C L n : ℕ) (hCL : C + L ≤ n) (z : ℕ) :
    ex (e1vec C L n) z = if C ≤ z ∧ z < C + L then locVec (L - 1) (C + L - 1 - z) else 0 := by
  unfold ex e1vec
  by_cases hz : z < n
  · rw [dif_pos hz]
  · rw [dif_neg hz]
    have : ¬ (C ≤ z ∧ z < C + L) := by omega
    rw [if_neg this]

theorem locVec_zero (m : ℕ) (hm : 0 < m) : locVec m 0 = 0 := by
  unfold locVec; rw [if_pos hm]; simp

/-- the chain energy of the zero-extended local vector is the abstract local energy. -/
theorem qF_e1vec (K k r : ℕ) (c : ℝ) :
    qF (K + 1) c (e1vec (K + 1) (k + 3) ((K + 1) + (k + 3) + r)) = locEnergy (k + 2) c := by
  set n := (K + 1) + (k + 3) + r with hn
  set e1 := e1vec (K + 1) (k + 3) n with he1
  have hCL : (K + 1) + (k + 3) ≤ n := by omega
  have hex0 := ex_e1vec (K + 1) (k + 3) n hCL
  have hex : ∀ z, ex e1 z = if K + 1 ≤ z ∧ z < K + 1 + (k + 3) then locVec (k + 2) (K + 1 + (k + 3) - 1 - z) else 0 := by
    intro z; rw [he1, hex0 z, show k + 3 - 1 = k + 2 by omega]
  have hf0 : locVec (k + 2) 0 = 0 := locVec_zero (k + 2) (by omega)
  have D1 : ∀ y, y < K → dlt e1 y = 0 := by
    intro y hy; unfold dlt; rw [hex, hex]; rw [if_neg (by omega), if_neg (by omega)]; ring
  have D2 : dlt e1 K = locVec (k + 2) (k + 2) := by
    unfold dlt; rw [hex, hex]
    rw [if_pos (by omega), if_neg (by omega)]
    rw [show K + 1 + (k + 3) - 1 - (K + 1) = k + 2 by omega]; ring
  have D3 : dlt e1 (K + 1) = locVec (k + 2) (k + 1) - locVec (k + 2) (k + 2) := by
    unfold dlt; rw [hex, hex]
    rw [if_pos (by omega), if_pos (by omega)]
    rw [show K + 1 + (k + 3) - 1 - (K + 1 + 1) = k + 1 by omega, show K + 1 + (k + 3) - 1 - (K + 1) = k + 2 by omega]
  have D4 : ∀ t, t < k + 1 → dlt e1 (K + (t + 2)) = locVec (k + 2) (k - t) - locVec (k + 2) (k + 1 - t) := by
    intro t ht
    unfold dlt; rw [hex, hex]
    rw [if_pos (by omega), if_pos (by omega)]
    rw [show K + 1 + (k + 3) - 1 - (K + (t + 2) + 1) = k - t by omega, show K + 1 + (k + 3) - 1 - (K + (t + 2)) = k + 1 - t by omega]
  have D5 : ∀ s, dlt e1 (K + (k + 3) + s) = 0 := by
    intro s
    unfold dlt; rw [hex, hex]
    by_cases hs : s = 0
    · subst hs
      rw [if_neg (by omega), if_pos (by omega)]
      rw [show K + 1 + (k + 3) - 1 - (K + (k + 3) + 0) = 0 by omega, hf0]; ring
    · rw [if_neg (by omega), if_neg (by omega)]; ring
  unfold qF aF bF
  have hsplit : n - 1 = K + ((k + 3) + r) := by omega
  rw [hsplit, Finset.sum_range_add, Finset.sum_range_add]
  have z1 : ∑ y ∈ Finset.range K, (dlt e1 y) ^ 2 = 0 :=
    Finset.sum_eq_zero (fun y hy => by rw [D1 y (Finset.mem_range.mp hy)]; ring)
  have z2 : ∑ s ∈ Finset.range r, (dlt e1 (K + ((k + 3) + s))) ^ 2 = 0 :=
    Finset.sum_eq_zero (fun s _ => by
      have := D5 s
      rw [show K + ((k + 3) + s) = K + (k + 3) + s by ring, this]; ring)
  rw [z1, z2, zero_add, add_zero]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hmid : ∑ t ∈ Finset.range (k + 1), (dlt e1 (K + (t + 1 + 1))) ^ 2 =
      ∑ j ∈ Finset.range (k + 1), (locVec (k + 2) (j + 1) - locVec (k + 2) j) ^ 2 := by
    rw [← Finset.sum_range_reflect (fun j => (locVec (k + 2) (j + 1) - locVec (k + 2) j) ^ 2) (k + 1)]
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := Finset.mem_range.mp ht
    have := D4 t ht'
    show (dlt e1 (K + (t + 1 + 1))) ^ 2 = (locVec (k + 2) (k + 1 - 1 - t + 1) - locVec (k + 2) (k + 1 - 1 - t)) ^ 2
    rw [show t + 1 + 1 = t + 2 by ring, this]
    rw [show k + 1 - 1 - t + 1 = k + 1 - t by omega, show k + 1 - 1 - t = k - t by omega]; ring
  rw [hmid]
  have hD0 : dlt e1 (K + 0) = locVec (k + 2) (k + 2) := by simpa using D2
  have hD1 : dlt e1 (K + (0 + 1)) = locVec (k + 2) (k + 1) - locVec (k + 2) (k + 2) := by simpa using D3
  have hD2 : dlt e1 (K + 1 - 1) = locVec (k + 2) (k + 2) := by
    rw [show K + 1 - 1 = K by omega]; exact D2
  rw [hD0, hD1, hD2]
  unfold locEnergy
  rw [show k + 2 - 1 = k + 1 by omega]
  ring


#print axioms e1vec
#print axioms ex_e1vec
#print axioms locVec_zero
#print axioms qF_e1vec

end AdalyFormal.CoverJacobi
