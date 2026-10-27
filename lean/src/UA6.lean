import Mathlib

/-!
# UA6 -- the 1D IMS partition `ψ_m(t)` on `ℤ/(KM)` (lane m2_unit_20261014)

Cells of length `M`, `K ≥ 2` cells.  For `t = aM + r` (`r < M`): `ψ_a(t) = sin(πr/2M)`, `ψ_{a−1}(t) = cos(πr/2M)`, all other `ψ_m(t) = 0`.
* `psi1_sumsq`  : `Σ_m ψ_m(t)² = 1`.
* `psi1_cross`  : `Σ_m ψ_m(t) ψ_m(t+1 mod KM) = cos(π/2M)`.
* `psi1_lip`    : `Σ_m (ψ_m(t+1 mod KM) − ψ_m(t))² ≤ (π/2M)²`.
Pure arithmetic; no lattice objects.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.M2Unit

/-- `(a + K − 1) % K`, the previous cell. -/
def prevC (K a : ℕ) : ℕ := (a + K - 1) % K

/-- the angle of `t` inside its cell. -/
noncomputable def ang (M t : ℕ) : ℝ := Real.pi * ((t % M : ℕ) : ℝ) / (2 * M)

/-- the 1D partition function. -/
noncomputable def psi1 (M K : ℕ) (m : Fin K) (t : ℕ) : ℝ :=
  if m.val = t / M then Real.sin (ang M t)
  else if m.val = prevC K (t / M) then Real.cos (ang M t) else 0

theorem prevC_lt {K a : ℕ} (hK : 0 < K) : prevC K a < K := Nat.mod_lt _ hK

theorem prevC_ne {K a : ℕ} (hK : 2 ≤ K) (ha : a < K) : prevC K a ≠ a := by
  unfold prevC
  intro h
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at h
    omega
  · have : a + K - 1 = (a - 1) + K := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
    omega

theorem prevC_succ {K a : ℕ} (hK : 0 < K) (ha : a < K) : prevC K ((a + 1) % K) = a := by
  unfold prevC
  rcases Nat.lt_or_ge (a + 1) K with h | h
  · rw [Nat.mod_eq_of_lt h]
    have : a + 1 + K - 1 = a + K := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  · have hK' : a + 1 = K := by omega
    rw [hK', Nat.mod_self, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem succ_mod_ne {K a : ℕ} (hK : 2 ≤ K) (ha : a < K) : (a + 1) % K ≠ a := by
  rcases Nat.lt_or_ge (a + 1) K with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · have hK' : a + 1 = K := by omega
    rw [hK', Nat.mod_self]; omega

/-- a two-point sum over `Fin K`. -/
theorem sum_two {K : ℕ} (a b : ℕ) (ha : a < K) (hb : b < K) (hab : a ≠ b) (x y : ℝ) :
    ∑ m : Fin K, (if m.val = a then x else if m.val = b then y else 0) = x + y := by
  have e : ∀ m : Fin K, (if m.val = a then x else if m.val = b then y else 0)
      = (if m = (⟨a, ha⟩ : Fin K) then x else 0) + (if m = (⟨b, hb⟩ : Fin K) then y else 0) := by
    intro m
    by_cases h1 : m.val = a
    · have h2 : m.val ≠ b := by omega
      have e1 : m = (⟨a, ha⟩ : Fin K) := Fin.ext h1
      have e2 : m ≠ (⟨b, hb⟩ : Fin K) := fun h => h2 (by rw [h])
      rw [if_pos h1, if_pos e1, if_neg e2, add_zero]
    · have e1 : m ≠ (⟨a, ha⟩ : Fin K) := fun h => h1 (by rw [h])
      rw [if_neg h1, if_neg e1, zero_add]
      by_cases h2 : m.val = b
      · rw [if_pos h2, if_pos (Fin.ext h2)]
      · have e2 : m ≠ (⟨b, hb⟩ : Fin K) := fun h => h2 (by rw [h])
        rw [if_neg h2, if_neg e2]
  rw [Finset.sum_congr rfl (fun m _ => e m), Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]

theorem cell_lt {M K t : ℕ} (hM : 0 < M) (ht : t < K * M) : t / M < K := by
  rw [Nat.div_lt_iff_lt_mul hM]; exact ht

theorem psi1_sumsq {M K t : ℕ} (hM : 0 < M) (hK : 2 ≤ K) (ht : t < K * M) :
    ∑ m : Fin K, psi1 M K m t ^ 2 = 1 := by
  have ha := cell_lt hM ht
  have hpa : prevC K (t / M) < K := prevC_lt (by omega)
  have hne : t / M ≠ prevC K (t / M) := fun h => prevC_ne hK ha h.symm
  have e : ∀ m : Fin K, psi1 M K m t ^ 2 = (if m.val = t / M then Real.sin (ang M t) ^ 2
      else if m.val = prevC K (t / M) then Real.cos (ang M t) ^ 2 else 0) := by
    intro m; unfold psi1; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun m _ => e m), sum_two _ _ ha hpa hne, Real.sin_sq_add_cos_sq]

theorem psi1_cross {M K t : ℕ} (hM : 0 < M) (hK : 2 ≤ K) (ht : t < K * M) :
    ∑ m : Fin K, psi1 M K m t * psi1 M K m ((t + 1) % (K * M)) = Real.cos (Real.pi / (2 * M)) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  set a := t / M with ha_def
  set r := t % M with hr_def
  have ht_eq : t = a * M + r := by rw [ha_def, hr_def, mul_comm]; exact (Nat.div_add_mod t M).symm
  have hr : r < M := Nat.mod_lt _ hM
  have ha := cell_lt hM ht
  have hpa : prevC K a < K := prevC_lt (by omega)
  have hne : a ≠ prevC K a := fun h => prevC_ne hK ha h.symm
  rcases Nat.lt_or_ge (r + 1) M with hcase | hcase
  · -- inside the cell
    have ht1 : t + 1 < K * M := by
      have : (a + 1) * M ≤ K * M := Nat.mul_le_mul_right M (by omega)
      nlinarith
    rw [Nat.mod_eq_of_lt ht1]
    have hd1 : (t + 1) / M = a := by
      rw [ht_eq, show a * M + r + 1 = (r + 1) + a * M by ring, Nat.add_mul_div_right _ _ hM,
        Nat.div_eq_of_lt hcase, zero_add]
    have hm1 : (t + 1) % M = r + 1 := by
      rw [ht_eq, show a * M + r + 1 = (r + 1) + a * M by ring, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcase]
    have hang1 : ang M (t + 1) = ang M t + Real.pi / (2 * M) := by
      unfold ang; rw [hm1, ← hr_def]; push_cast; ring
    have e : ∀ m : Fin K, psi1 M K m t * psi1 M K m (t + 1) = (if m.val = a then Real.sin (ang M t) *
        Real.sin (ang M t + Real.pi / (2 * M)) else if m.val = prevC K a then Real.cos (ang M t) *
        Real.cos (ang M t + Real.pi / (2 * M)) else 0) := by
      intro m; unfold psi1; rw [hd1, hang1, ← ha_def]; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun m _ => e m), sum_two _ _ ha hpa hne]
    have := Real.cos_sub (ang M t + Real.pi / (2 * M)) (ang M t)
    rw [show ang M t + Real.pi / (2 * M) - ang M t = Real.pi / (2 * M) by ring] at this
    rw [this]; ring
  · -- the last site of the cell
    have hr' : r = M - 1 := by omega
    have hsucc : t + 1 = (a + 1) * M := by rw [ht_eq, hr']; have : 1 ≤ M := hM; rw [add_mul]; omega
    have hmod : (t + 1) % (K * M) = ((a + 1) % K) * M := by
      rw [hsucc]
      rcases Nat.lt_or_ge (a + 1) K with h | h
      · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_right h hM)]
      · have hK' : a + 1 = K := by omega
        rw [hK', Nat.mod_self, Nat.mod_self, zero_mul]
    rw [hmod]
    have hb : (a + 1) % K < K := Nat.mod_lt _ (by omega)
    have hd1 : ((a + 1) % K) * M / M = (a + 1) % K := Nat.mul_div_cancel _ hM
    have hm1 : ((a + 1) % K) * M % M = 0 := Nat.mul_mod_left _ _
    have hang1 : ang M (((a + 1) % K) * M) = 0 := by unfold ang; rw [hm1]; simp
    have hpb : prevC K ((a + 1) % K) = a := prevC_succ (by omega) ha
    have hbne : (a + 1) % K ≠ a := succ_mod_ne hK ha
    have e : ∀ m : Fin K, psi1 M K m t * psi1 M K m (((a + 1) % K) * M)
        = (if m.val = a then Real.sin (ang M t) else if m.val = prevC K a then 0 else 0) := by
      intro m
      unfold psi1
      rw [hd1, hang1, hpb, Real.sin_zero, Real.cos_zero, ← ha_def]
      have hbne' : a ≠ (a + 1) % K := fun h => hbne h.symm
      by_cases h1 : m.val = a
      · simp [h1, hbne']
      · by_cases h3 : m.val = (a + 1) % K
        · simp [h1, h3, hbne]
        · simp [h1, h3]
    rw [Finset.sum_congr rfl (fun m _ => e m), sum_two _ _ ha hpa hne, add_zero]
    unfold ang
    rw [← hr_def, hr']
    have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by rw [Nat.cast_sub hM]; simp
    rw [hM1]
    have : Real.pi * ((M : ℝ) - 1) / (2 * M) = Real.pi / 2 - Real.pi / (2 * M) := by field_simp
    rw [this, Real.sin_pi_div_two_sub]

theorem psi1_lip {M K t : ℕ} (hM : 0 < M) (hK : 2 ≤ K) (ht : t < K * M) :
    ∑ m : Fin K, (psi1 M K m ((t + 1) % (K * M)) - psi1 M K m t) ^ 2 ≤ (Real.pi / (2 * M)) ^ 2 := by
  have hKM : 0 < K * M := Nat.mul_pos (by omega) hM
  have h1 := psi1_sumsq hM hK ht
  have h2 := psi1_sumsq hM hK (Nat.mod_lt (t + 1) hKM)
  have h3 := psi1_cross hM hK ht
  have e : ∑ m : Fin K, (psi1 M K m ((t + 1) % (K * M)) - psi1 M K m t) ^ 2
      = ∑ m : Fin K, psi1 M K m ((t + 1) % (K * M)) ^ 2 + ∑ m : Fin K, psi1 M K m t ^ 2
        - 2 * ∑ m : Fin K, psi1 M K m t * psi1 M K m ((t + 1) % (K * M)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => by ring)
  rw [e, h1, h2, h3]
  have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi / (2 * M))
  nlinarith

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.psi1_sumsq
#print axioms AdalyFormal.M2Unit.psi1_cross
#print axioms AdalyFormal.M2Unit.psi1_lip
